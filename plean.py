from dataclasses import dataclass
from typing import Union

class PleanException(Exception):
    pass

def imax(u,v):
    ''' impredicative maximum. Sort 0 (i.e. Prop) is impredicative '''
    if v == 0:
        return 0
    else:
        return max(u,v)

@dataclass(frozen=True)
class Token:
    val: str
    def __repr__(self):
        return f"`{self.val}"

@dataclass(frozen=True)
class Sort:
    universe: int
    def __repr__(self):
        if self.universe == 0:
            return "Prop"
        elif self.universe == 1:
            return "Type"
        else:
            return f"Sort({self.universe})"

@dataclass(frozen=True)
class Variable:
    type: 'Expression'
    name: Token
    def __repr__(self):
        return self.name.val

@dataclass(frozen=True)
class Constant:
    name: Token
    def __repr__(self):
        return self.name.val

@dataclass(frozen=True)
class Pi:
    arg_name: Token
    arg_type: 'Expression'
    result_type: 'Expression'
    def __repr__(self):
        return f"(Π {self.arg_name}:{self.arg_type}, {self.result_type})"

@dataclass(frozen=True)
class Apply:
    func_expression: 'Expression'
    arg_expression: 'Expression'
    def __repr__(self):
        return f"({self.func_expression} {self.arg_expression})"

@dataclass(frozen=True)
class Lambda:
    arg_name: Token
    arg_type: 'Expression'
    body: 'Expression'
    def __repr__(self):
        return f"(λ {self.arg_name.val}:{self.arg_type}, {self.body})"

@dataclass(frozen=True)
class ConstructorTemplate:
    name: Token
    arg_names: tuple[Token, ...]
    arg_types: tuple['Expression', ...]
    result_indexes: tuple['Expression', ...]
    def __post_init__(self):
        assert len(self.arg_names) == len(self.arg_types), f"Constructor template {self.name} has mismatch of specified arg names and arg types lengths"

@dataclass(frozen=True)
class ConstructedType:
    constructors: tuple[ConstructorTemplate, ...]
    args: tuple[tuple[Token, 'Expression'], ...]
    indexes: tuple[tuple[Token, 'Expression'], ...]
    type: Sort
    name: Token
    def __repr__(self):
        return repr(self.name)
    def __post_init__(self):
        # Check the universe of the constructed type. Must be either:
        # 1. 0 (i.e., Prop), or
        # 2. At least as large as the universe of any type argument or index
        max_universe = 0
        for _,t in (*self.args, *self.indexes):
            t_type = infer_type(t)
            assert isinstance(t_type, Sort), f"{self.type} must have all type arguments/indexes have their type being a Sort but had {t}:{t_type}"
            max_universe = max(max_universe, t_type.universe)
        if self.type.universe > 0:
            assert self.type.universe >= max_universe, f"{self.type} is specified to be universe {self.type.universe} but expected to have universe at least {max_universe}"
        for constructor in self.constructors:
            assert len(constructor.result_indexes) == len(self.indexes), f"Incorrect number of indexes in constructor {self}.{constructor.name.val}"


@dataclass(frozen=True)
class InstantiatedConstructedType:
    type: ConstructedType
    type_args: tuple['Expression', ...]
    type_indexes: tuple['Expression', ...]
    def __post_init__(self):
        # Check arg types match expectation
        assert len(self.type_args) == len(self.type.args), f"Expected {len(self.type.args)} args for {self.type} but received {len(self.type_args)} instead"
        for i, (arg, (arg_name, arg_type)) in enumerate(zip(self.type_args, self.type.args)):
            arg_names_head = tuple(name for name, type in self.type.args)[:i]
            arg_vals_head = self.type_args[:i]
            arg_instantiated = instantiate_list( arg_names_head, arg_vals_head, arg)
            arg_type_instantiated = instantiate_list(arg_names_head, arg_vals_head, arg_type)
            inferred_type = infer_type(arg_instantiated)
            assert is_def_eq(inferred_type, arg_type_instantiated), f"Expected arg for {self.type.name} of type {arg_type_instantiated} but got {arg}:{inferred_type} instead"
        # Check index types match expectation
        assert len(self.type_indexes) == len(self.type.indexes), f"Expected {len(self.type.indexes)} indexes for {self.type} but received {len(self.type_indexes)} instead"
        for index, (index_name, index_type) in zip(self.type_indexes, self.type.indexes):
            # TODO: do we also need to instantiate earlier indexes? Can one indexe depend upon a previous one?
            arg_names_head = tuple(name for name, type in self.type.args)
            arg_vals_head = self.type_args
            index_instantiated = instantiate_list(arg_names_head, arg_vals_head, index)
            index_type_instantiated = instantiate_list(arg_names_head, arg_vals_head, index_type)
            inferred_type = infer_type(index_instantiated)
            assert is_def_eq(inferred_type, index_type_instantiated), f"Expected index {index_name} for {self.type.name} of type {index_type_instantiated} but got {index}:{inferred_type} instead"
    def __repr__(self):
        args = ','.join(repr(x) for x in (*self.type_args, *self.type_indexes))
        return f"{self.type.name.val}({args})"

@dataclass(frozen=True)
class Constructor:
    type: ConstructedType
    constructor_index: int
    args: tuple['Expression',...]
    type_args: tuple['Expression',...]

    def __post_init__(self):
        assert len(self.type_args) == len(self.type.args), f"Expected {len(self.type.args)} type args for constructor of {self.type} but got {len(self.type_args)}"
        for i, (arg, (arg_name, arg_type)) in enumerate(zip(self.type_args, self.type.args)):
            arg_names_head = tuple(name for name, type in self.type.args)[:i]
            arg_vals_head = self.type_args[:i]
            arg_instantiated = instantiate_list( arg_names_head, arg_vals_head, arg)
            arg_type_instantiated = instantiate_list(arg_names_head, arg_vals_head, arg_type)
            assert is_def_eq(infer_type(arg_instantiated), arg_type_instantiated), f"Expected type {arg_type_instantiated} for constructor type arg {arg_name} of {self.type}.{self.template.name} but got {arg_instantiated}"

        assert len(self.args) == len(self.template.arg_types), f"Expected {len(self.template.arg_types)} args for type {self.type} constructor but got {len(self.args)}"
        for arg, (arg_type) in zip(self.args, self.template.arg_types):
            instantiated_arg = instantiate_list(
                tuple(name for name, type in self.type.args), self.type_args, arg
            )
            arg_type = instantiate_type_args(self.type.args, self.type_args, arg_type)
            assert is_def_eq(infer_type(instantiated_arg), arg_type), f"Expected arg of type {arg_type} in constructor for {self.type}.{self.template.name} but got {arg}"

    @property
    def template(self):
        return self.type.constructors[self.constructor_index]

@dataclass(frozen=True)
class Recursor:
    type: InstantiatedConstructedType
    result_type: 'Expression'
    match_cases: tuple['Expression', ...]
    def __post_init__(self):
        result_type = apply_list(
            self.result_type,
            list(self.type.type_indexes),
        )
        res_sort = infer_type(result_type)
        assert isinstance(res_sort, Sort), f"Recursor for {self.type} must yield a Sort type but yields {result_type}:{res_sort}"

        # Verify types match
        assert len(self.match_cases) == len(self.type.type.constructors), f"Recursor has {len(self.match_cases)} cases but {self.type} needs {len(self.type.type.constructors)}"
        for constructor, case in zip(self.type.type.constructors, self.match_cases):
            case_type = infer_type(case)
            for arg_type in constructor.arg_types:
                arg_type = instantiate_type_args(self.type.type.args, self.type.type_args, arg_type)
                assert isinstance(case_type, Pi), f"Recursor for {self.type} expected to have Pi type but had {case_type}"
                assert is_def_eq(case_type.arg_type, arg_type), f"Recursor for {self.type} expected to have match-case accepting {arg_type} but had type {case_type}"
                # Select the next step and compare it
                case_type = case_type.result_type #TODO: substitute free variables into this?
            assert is_def_eq(case_type, result_type), f"Recursor for {self.type} expected to yield {result_type} but yields {case_type} instead"

        if self.type.type.type.universe == 0:
            # Prop types have extra conditions on their recursors. Either:
            # 1. The recursor type must be a Prop, or
            # 2. There is only one constructor for the type and its arguments are
            #    other Props
            # Meeting these conditions is called "large elimination" (See Carneiro 2019)
            if res_sort.universe != 0:
                assert len(self.type.type.constructors) == 1, f"Recursor for {self.type} must yield a Prop type but yields {result_type}:{res_sort}"
                for constructor_template in self.type.type.constructors:
                    for t in constructor_template.arg_types:
                        assert is_prop_type(t), f"Recursor for {self.type} must yield a Prop type but yields {result_type}:{res_sort}"

Expression = Union[
    Variable,
    Constant,
    Sort,
    Pi,
    Apply,
    Lambda,
    Constructor,
    InstantiatedConstructedType,
    Recursor,
]

# Global environment
constants : dict[str, Expression] = {}

def pretty_print(expr: Expression) -> str:
    ''' pretty print an expression '''
    def pp(t: Expression) -> str:
        if isinstance(t, Variable):
            return f"{t.name.val}:{pp(t.type)}"
        elif isinstance(t, Constant):
            return f"{t.name}"
        elif isinstance(t, Sort):
            return f"Sort({t.universe})"
        elif isinstance(t, Pi):
            return f"(∀ {t.arg_name.val}:{pp(t.arg_type)} => {pp(t.result_type)})"
        elif isinstance(t, Apply):
            return f"{pp(t.func_expression)} {pp(t.arg_expression)}"
        elif isinstance(t, Lambda):
            return f"(λ {t.arg_name.val}:{pp(t.arg_type)}, {pp(t.body)})"
        elif isinstance(t, Constructor):
            pp_args = [pp(arg) for arg in t.args]
            return f"{t.type.name}{t.type_args} " + " ".join(pp_args)
        elif isinstance(t, ConstructedType):
            return t.name.val
        elif isinstance(t, Recursor):
            return f"({t.type}.rec" + " ".join(pp(m) for m in t.match_cases) + ")"
        else:
            raise NotImplementedError
    return pp(expr)

def is_prop_type(t: Expression):
    ''' Returns whether t's type is a Prop '''
    t_type = infer_type(t)
    return isinstance(t_type, Sort) and t_type.universe == 0

def free_vars(expr: Expression):
    ''' Return list of unbound variables in the expression '''
    free_var_list: set[Token] = set()
    def free_vars_(expr: Expression, bound_vars: set[Token]):
        if isinstance(expr, Variable):
            if expr.name not in bound_vars:
                free_var_list.add(expr.name)
        elif isinstance(expr, Lambda):
            free_vars_(expr.body, bound_vars.union([expr.arg_name]))
        elif isinstance(expr, Pi):
            free_vars_(expr.result_type, bound_vars.union([expr.arg_name]))
        elif isinstance(expr, Apply):
            free_vars_(expr.arg_expression, bound_vars)
            free_vars_(expr.func_expression, bound_vars)
        elif isinstance(expr, Constructor):
            type_args = [name for name, expr2 in expr.type.args]
            for arg in expr.args:
                free_vars_(arg, bound_vars.union(type_args))
        elif isinstance(expr, Recursor):
            for case in expr.match_cases:
                free_vars_(case, bound_vars)
        # ConstructedType have no free vars
        #TODO: InstantiatedConstructedType args in type_args? And so in Recursor/Constructor too?
        else:
            # TODO: can constants have free vars?
            pass
    free_vars_(expr, set())
    return free_var_list

def instantiate(expr: Expression, arg_name: Token, arg_expression: Expression) -> Expression:
    ''' Replace a free variable in an expression with an expression '''
    match expr:
        case Variable(type, name):
            if name == arg_name:
                arg_type = infer_type(arg_expression)
                assert is_def_eq(arg_type, type), f"Cannot instantiate variable {name}:{type} as {arg_expression}:{arg_type}"
                return arg_expression
            return Variable(
                instantiate(expr.type, arg_name, arg_expression),
                expr.name,
            )
        case Constant(name):
            return constants[name.val]
        case Sort(_):
            return expr
        case Pi(pi_arg_name, pi_arg_type, pi_body):
            if pi_arg_name == arg_name:
                # arg_name now is bound, so don't try to rebind it
                return expr
            else:
                return Pi(
                    pi_arg_name,
                    pi_arg_type,
                    instantiate(pi_body, arg_name, arg_expression),
                )
        case Apply(func_expression, app_arg_expression):
            return Apply(
                instantiate(func_expression, arg_name, arg_expression),
                instantiate(app_arg_expression, arg_name, arg_expression),
            )
        case Lambda(lambda_arg_name, lambda_arg_type, body):
            if lambda_arg_name == arg_name:
                # arg_name is now bound, don't instantiate it inside the lambda
                return expr
            free_vars_in_arg = free_vars(arg_expression)
            if expr.arg_name in free_vars_in_arg:
                # Must rename the parameter of this function
                # so that it does not colide with the free variables being substituted in
                # otherwise those variables would inadvertently become bound
                new_arg_name = Token(expr.arg_name.val + "`")
                new_bound_var = Variable(expr.arg_type, new_arg_name)
                expr = Lambda(
                    new_arg_name,
                    expr.arg_type,
                    instantiate(expr.body, expr.arg_name, new_bound_var)
                )
            return Lambda(
                expr.arg_name,
                instantiate(expr.arg_type, arg_name, arg_expression),
                instantiate(expr.body, arg_name, arg_expression),
            )
        case Constructor(_, _):
            if arg_name in expr.template.arg_names:
                raise NotImplementedError(f"Cannot yet substitute values ({arg_name}) into a constructor for {expr.type} with constructor argument of the same name")
                # NOTE: constructor indexes are evaluated in the environment containing the arguments
                #       so we have to skip over instantiating variables with the same name as the arguments
                #       But we still need to instantiate other free variables
            return Constructor(
                expr.type,
                expr.constructor_index,
                tuple(instantiate(constructor_arg, arg_name, arg_expression)
                    for constructor_arg in expr.args),
                tuple(instantiate(type_arg, arg_name, arg_expression)
                    for type_arg in expr.type_args),
            )
        case InstantiatedConstructedType(_):
            return InstantiatedConstructedType(
                expr.type,
                tuple(instantiate(type_arg, arg_name, arg_expression)
                    for type_arg in expr.type_args),
                tuple(instantiate(type_index, arg_name, arg_expression)
                    for type_index in expr.type_indexes),
            )
        case Recursor(_,_,_):
            return Recursor(
                type = expr.type,
                result_type = instantiate(expr.result_type, arg_name, arg_expression),
                match_cases = tuple(instantiate(case, arg_name, arg_expression) for case in expr.match_cases),
            )
        case _:
            raise NotImplementedError(f"Unknown how to instantiate {expr}")

def instantiate_list(arg_names: tuple[Token,...], arg_values: tuple['Expression',...], expr: 'Expression'):
    ''' Instiate a list of var names and values into an expr'''
    for (arg_name, arg_value) in zip(arg_names, arg_values):
        expr = instantiate(
            expr,
            arg_name,
            arg_value
        )
    return expr

def instantiate_type_args(arg_spec: tuple[tuple[Token, 'Expression'],...], arg_values: tuple['Expression',...], expr: 'Expression') -> 'Expression':
    # Instantiate the type arguments into an expression
    for (arg_name, arg_type), arg_value in zip(arg_spec, arg_values):
        expr = instantiate(
            expr,
            arg_name,
            arg_value,
        )
    return expr


def whnf(t: Expression) -> Expression:
    ''' weak head normal form (whnf) of an expression '''
    match t:
        # Non-trivial
        case Apply(func_expression, arg_expression):
            whnf_func = whnf(func_expression)
            if isinstance(whnf_func, Lambda):
                new_expr = whnf(instantiate(
                    whnf_func.body,
                    whnf_func.arg_name,
                    arg_expression
                ))
                return new_expr
                #TODO: Constructors as well as Lambdas
            elif whnf_func == t.func_expression:
                #TODO: iota-reduction? see L338 in type_checker.cpp
                return t
            else:
                raise NotImplementedError
        case _:
            # All others are trivial
            return t

def apply_list(expr: Expression, args: list[Expression]) -> Expression:
    ''' Given an expression and a list of argument expression, builds
    a chain of Apply's to apply all of them in order, i.e.,
    apply_list(expr, [a,b]) = Apply(Apply(expr, a), b)'''
    if len(args) == 0:
        return expr
    else:
        return apply_list(Apply(expr, args[0]), args[1:])

def lambda_chain(arg_names: list[Token], arg_types: list[Expression], body: Expression):
    ''' Create a multi-argument function by chaining lambdas together'''
    assert len(arg_names) == len(arg_types)

    if len(arg_names) == 0:
        return body
    return Lambda(
        arg_names[0],
        arg_types[0],
        lambda_chain(arg_names[1:], arg_types[1:], body)
    )


def is_def_eq(t: Expression, s: Expression) -> bool:
    ''' Test is expression t and s are definitionally equal to each other '''
    # Populate constants
    if isinstance(t, Constant):
        t = constants[t.name.val]
    if isinstance(s, Constant):
        s = constants[s.name.val]

    if isinstance(t, Sort) and isinstance(s, Sort):
        return t.universe == s.universe
    elif isinstance(t, Variable) and isinstance(s, Variable):
            return t.name == s.name
    elif isinstance(t, Lambda) and isinstance(s, Lambda):
        if isinstance(t.body, Apply) and isinstance(t.body.arg_expression, Variable):
            # First check if eta-conversion is possible
            #TODO: eta-conversion may need to be done elsewhere
            #      or to otherwise handle the case where (lambda x: f y) has
            #      y def-eq to x but not exactly equal to x
            if (t.body.arg_expression.name == t.arg_name and
                    is_def_eq(t.body.func_expression, s)):
                    return True
        if isinstance(s.body, Apply) and isinstance(s.body.arg_expression, Variable):
            # First check if eta-conversion is possible
            if (s.body.arg_expression.name == s.arg_name and
                    is_def_eq(s.body.func_expression, t)):
                    return True
        # If not, then just compare both body and arg type
        return (
            is_def_eq(
                t.arg_type,
                s.arg_type
            )
            and
            is_def_eq(
                t.body,
                instantiate(
                    s.body,
                    s.arg_name,
                    Variable(t.arg_type, t.arg_name),
                )
            )
        )
    elif isinstance(t, Constructor) and isinstance(s, Constructor):
        if t.type.type.universe == 0:
            if s.type.type.universe == 0:
                # Proof irrelevance: all instances of the same Prop type are equal
                return t.type == s.type

        return (
            (t.type == s.type) and
            t.constructor_index == s.constructor_index and
            len(t.args) == len(s.args) and
            all(is_def_eq(t_arg, s_arg) for t_arg, s_arg in zip(t.args, s.args)) and
            len(t.type_args) == len(s.type_args) and
            all(is_def_eq(t_arg, s_arg) for t_arg, s_arg in zip(t.type_args, s.type_args))
        )
    elif isinstance(t, InstantiatedConstructedType) and isinstance(s, InstantiatedConstructedType):
        return (
            t.type == s.type and
            all(is_def_eq(t_arg, s_arg) for t_arg, s_arg in zip(t.type_args, s.type_args))
        )
    elif isinstance(t, Pi) and isinstance(s, Pi):
        # NOTE: no eta-conversion done for Pi-types
        # this surpirses me but agrees with references (Carneiro, 2019)
        # and I believe also with Lean behavior
        return (
            is_def_eq(
                t.arg_type,
                s.arg_type,
            )
            and
            is_def_eq(
                t.result_type,
                instantiate(
                    s.result_type,
                    s.arg_name,
                    Variable(t.arg_type, t.arg_name),
                )
            )
        )
    elif isinstance(t, Apply) and isinstance(s, Apply):
        if is_def_eq(t.func_expression, s.func_expression) and is_def_eq(t.arg_expression, s.arg_expression):
            return True

    # Expression types don't match:
    if isinstance(t, Apply):
        whnf_func = whnf(t.func_expression)
        if isinstance(whnf_func, Recursor):
            # Perform iota reduction - evaluate recursor on a constructor
            recursor = whnf_func
            whnf_arg = whnf(t.arg_expression) #WHNF of recursor arg should be a constructor
            if isinstance(whnf_arg, Constructor):
                if (whnf_arg.type.name != recursor.type.type.name):
                    raise PleanException(f"Inferred type of {t.arg_expression} must be {recursor.type}.\nInstead was {whnf_arg.type}")
                match_case = recursor.match_cases[whnf_arg.constructor_index]
                return is_def_eq(
                    apply_list(match_case, list(whnf_arg.args)),
                    s
                )
            # TODO: do we need to handle anything other than Constructors?
        elif isinstance(whnf_func, Lambda):
            # Beta reduction: evaluate the argument into the function
            return is_def_eq(
                instantiate(
                    whnf_func.body,
                    whnf_func.arg_name,
                    t.arg_expression,
                ),
                s
            )
    elif isinstance(s, Apply):
        # Swap t and s
        return is_def_eq(s, t)

    t_type = infer_type(t)
    if is_prop_type(t_type):
        s_type = infer_type(s)
        if is_prop_type(s_type):
            # both t's type and s's type are Props
            if is_def_eq(t_type, s_type):
                # Proof irrelevance says that t and s are the same
                # since their types are the same which are Props
                return True

    #TODO: does eta expansion need to be moved to the last thing?
    # and why does the Lean code appear to do eta expansion only if
    # t is Lambda and s not-lambda (or vice-versa) - seems like both need to be lambda (or built-in or constructor)

    return False

def infer_type(expr: Expression) -> Expression:
    ''' Given an expression, infer its type '''
    if isinstance(expr, Variable):
        return expr.type
    elif isinstance(expr, Constant):
        return infer_type(constants[expr.name.val])
    elif isinstance(expr, Sort):
        return Sort(expr.universe + 1)
    elif isinstance(expr, Pi):
        arg_type = infer_type(expr.arg_type)
        result_type = infer_type(expr.result_type)
        if isinstance(arg_type, Sort) and isinstance(result_type, Sort):
            return Sort(
                imax(
                    arg_type.universe,
                    result_type.universe,
                )
            )
        else:
            raise NotImplementedError
    elif isinstance(expr, Apply):
        func_type = infer_type(expr.func_expression)
        if isinstance(func_type, Pi):
            return instantiate(
                func_type.result_type,
                func_type.arg_name,
                expr.arg_expression,
            )
        else:
            raise NotImplementedError
    elif isinstance(expr, Lambda):
        return Pi(
            expr.arg_name,
            expr.arg_type,
            infer_type(instantiate(
                expr.body,
                expr.arg_name,
                Variable(expr.arg_type, expr.arg_name),
            ))
        )
    elif isinstance(expr, Constructor):
        return InstantiatedConstructedType(
            expr.type,
            expr.type_args,
            tuple(instantiate_list(expr.template.arg_names, expr.type_args, x) for x in expr.template.result_indexes),
        )
    elif isinstance(expr, InstantiatedConstructedType):
        return expr.type.type
    elif isinstance(expr, Recursor):
        result_type =  apply_list(
            expr.result_type,
            list(expr.type.type_indexes),
        )
        return Pi(
            Token('?'), # TODO: Allow recursors to have dependent return types
            expr.type,
            result_type,
        )
    else:
        raise NotImplementedError