import io
from dataclasses import dataclass, field
from typing import Union
from typing import overload
import functools

class PleanException(Exception):
    pass

def imax(u,v):
    #impredicative maximum. Sort 0 (i.e. Prop) is impredicative
    if v == 0:
        return 0
    else:
        return max(u,v)

@dataclass(frozen=True)
class Token:
    val: str

@dataclass(frozen=True)
class Sort:
    universe: int

@dataclass(frozen=True)
class Variable:
    type: 'Expression'
    name: Token

@dataclass(frozen=True)
class Constant:
    name: Token

@dataclass(frozen=True)
class Pi:
    arg_name: Token
    arg_type: 'Expression'
    result_type: 'Expression'

    #def __post_init__(self):
    #    res_type = substitute(self.arg_name, self.arg_type, self.result_type_expr)
    #    if res_type != self.result_type:
    #        raise ExpressionError(f"Result type expression passed to Pi has type\n{res_type}\nbut expected to have\n{self.result_type}")

@dataclass(frozen=True)
class Apply:
    func_expression: 'Expression'
    arg_expression: 'Expression'

@dataclass(frozen=True)
class Lambda:
    arg_name: Token
    arg_type: 'Expression'
    body: 'Expression'

@dataclass(frozen=True)
class ConstructorTemplate:
    name: Token
    arg_names: tuple[Token, ...]
    arg_types: tuple['Expression', ...]
    constructed_type: Constant

@dataclass(frozen=True)
class ConstructedType:
    constructors: tuple[ConstructorTemplate, ...]
    type: Sort
    name: Token

@dataclass(frozen=True)
class Constructor:
    template: ConstructorTemplate
    args: tuple['Expression',...]

@dataclass(frozen=True)
class Destructor:
    type: ConstructedType 
    # match_exprs are ( ((a,b,c), expr), ((x,y), expr), ...)
    # to match constructors like ( (cons1 a b c), (cons2 x y), ...)
    match_exprs: tuple[
        tuple[tuple[Token,...], 'Expression'],...
    ]
    result_type: 'Expression'


Expression = Union[
    Variable,
    Constant,
    Sort,
    Pi,
    Apply,
    Lambda,
    Constructor,
    ConstructedType,
    Destructor,
]

# Global environment
constants : dict[str, Expression] = {}

def pretty_print(expr: Expression) -> str:
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
            return f"{t.template.name.val} " + " ".join(pp_args)
        elif isinstance(t, ConstructedType):
            return t.name.val
        elif isinstance(t, Destructor):
            matches = [cons.name.val + " " + ' '.join(x.val for x in m[0])
                            for cons, m in zip(t.type.constructors, t.match_exprs)]
            return "(" + " | ".join(matches) + ")"
        else:
            raise NotImplementedError
    return pp(expr)

@functools.cache
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
            for arg in expr.args:
                free_vars_(arg, bound_vars)
        elif isinstance(expr, Destructor):
            free_vars_(expr.result_type, bound_vars)
            for (args, result) in expr.match_exprs:
                free_vars_(result, bound_vars.union(args))
        # ConstructedType has no free vars
        else:
            # TODO: can constants have free vars?
            pass
    free_vars_(expr, set())
    return free_var_list

@overload
def instantiate(expr: Variable, arg_name: Token, arg_expression: Expression) -> Variable: ...
@overload
def instantiate(expr: Sort, arg_name: Token, arg_expression: Expression) -> Sort: ...
@overload
def instantiate(expr: Pi, arg_name: Token, arg_expression: Expression) -> Pi: ...
@overload
def instantiate(expr: Lambda, arg_name: Token, arg_expression: Expression) -> Lambda: ...
@overload
def instantiate(expr: Apply, arg_name: Token, arg_expression: Expression) -> Apply: ...
@overload
def instantiate(expr: Constructor, arg_name: Token, arg_expression: Expression) -> Constructor: ...
@overload
def instantiate(expr: ConstructedType, arg_name: Token, arg_expression: Expression) -> ConstructedType: ...
@functools.cache
def instantiate(expr: Expression, arg_name: Token, arg_expression: Expression) -> Expression:
    ''' Replace a free variable in an expression with an expression '''
    match expr:
        case Variable(type, name):
            if name == arg_name:
                # TODO: assert type match?
                return arg_expression
            return expr
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
            return Constructor(
                expr.template,
                tuple(instantiate(constructor_arg, arg_name, arg_expression)
                    for constructor_arg in expr.args)
            )
        case ConstructedType(_):
            return expr
        case Destructor(_,_,_):
            match_exprs = []
            for (args, result), template in zip(expr.match_exprs, expr.type.constructors):
                if arg_name in args:
                    # Variable is now bound, do not instantiate it
                    # inside of the result expression
                    match_exprs.append((args, result))
                    continue
                free_vars_in_arg = free_vars(arg_expression)
                new_args = []
                for arg, arg_type in zip(args, template.arg_types):
                    # Check for clashes where bound args occur in the
                    # expression being substituted in and avoid those
                    if arg in free_vars_in_arg:
                        # Rename destructor arg to avoid clash with free var
                        new_arg_name = Token(arg_name.val + "`")
                        new_bound_var = Variable(arg_type, new_arg_name)
                        result = instantiate(
                            result,
                            arg_name,
                            new_bound_var,
                        )
                        new_args.append(new_arg_name)
                    else:
                        new_args.append(arg)
                # Perform the actual instantiation
                result = instantiate(result, arg_name, arg_expression)
                match_exprs.append((tuple(new_args,), result))
            return Destructor(
                expr.type,
                tuple(match_exprs),
                instantiate(
                    expr.result_type,
                    arg_name,
                    arg_expression
                )
            )
        case _:
            raise NotImplementedError(f"Unknown how to instantiate {expr}")

@functools.cache
def whnf(t: Expression) -> Expression:
    match t:
        # Trivial cases:
        case Variable(type, name):
            return t
        case Constant(name):
            return whnf(constants[name.val])
        case Sort(universe):
            return t
        case Pi(arg_name, arg_type, result_type):
            return t
        case Lambda(arg_name, arg_type, body):
            return t
        case Constructor(_, _):
            return t
        case ConstructedType(_):
            return t
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
            raise NotImplementedError
            
def is_def_eq(t: Expression, s: Expression) -> bool:
    # Populate constnats
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
        return ((t.template == s.template) and
            len(t.args) == len(s.args) and
            all(is_def_eq(t_arg, s_arg) for t_arg, s_arg in zip(t.args, s.args)))
    elif isinstance(t, ConstructedType) and isinstance(s, ConstructedType):
        return t == s
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

    # Types don't match:
    if isinstance(t, Apply):
        if isinstance(t.func_expression, Destructor):
            # Perform iota reduction - evaluate destructor on a constructor
            destructor = t.func_expression
            whnf_arg = whnf(t.arg_expression) #WHNF of destructor arg should be a constructor
            if isinstance(whnf_arg, Constructor):
                if (whnf_arg.template.constructed_type.name != destructor.type.name):
                    raise PleanException(f"Inferred type of {pretty_print(t.arg_expression)} must be {pretty_print(destructor.type)}.\nInstead was {whnf_arg.template.constructed_type}")
                template_idx = destructor.type.constructors.index(whnf_arg.template)
                match_arg_tokens, match_body = destructor.match_exprs[template_idx]
                # TODO: for now we only support one-argument destructors/constructors
                if len(match_arg_tokens) == 0:
                    new_t = match_body
                elif len(match_arg_tokens) == 1:
                    new_t = instantiate(
                        match_body,
                        match_arg_tokens[0],
                        t.arg_expression,
                    )
                else:
                    raise NotImplementedError(f"Only support constructors with one argument: {destructor.type} constructor number {template_idx}")
                return is_def_eq(new_t, s)
            else:
                raise NotImplementedError(f"Expected Constructor, received {pretty_print(whnf_arg)}")
        elif isinstance(t.func_expression, Lambda):
            # Beta reduction: evaluate the argument into the function
            return is_def_eq(
                instantiate(
                    t.func_expression.body,
                    t.func_expression.arg_name,
                    t.arg_expression,
                ),
                s
            )
    elif isinstance(s, Apply):
        # Swap t and s
        return is_def_eq(s, t)

    #TODO: does eta expansion need to be moved to the last thing?
    # and why does the Lean code appear to do eta expansion only if
    # t is Lambda and s not-lambda (or vice-versa) - seems like both need to be lambda (or built-in or constructor)

    #TODO: make Prop have proof irrelevance
    return False

def infer_type(expr: Expression) -> Expression:
    if isinstance(expr, Variable):
        return expr.type
    elif isinstance(expr, Constant):
        return infer_type(constants[expr.name.val])
    elif isinstance(expr, Sort):
        return Sort(expr.universe + 1)
    elif isinstance(expr, Pi):
        arg_type = infer_type(expr.arg_type)
        result_type = infer_type(
            instantiate(
                expr.result_type,
                expr.arg_name,
                arg_type,
            )
        )
        if isinstance(arg_type, Sort) and isinstance(result_type, Sort):
            return Sort(
                max(
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
        return expr.template.constructed_type
    elif isinstance(expr, ConstructedType):
        return expr.type
    elif isinstance(expr, Destructor):
        return Pi(
            Token(''), # TODO: unsure, no var here -- can destructors have parametric return types?
            expr.type,
            expr.result_type,
        )
    else:
        raise NotImplementedError