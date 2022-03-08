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
    result_type: 'Expression'
    body: 'Expression'

@dataclass(frozen=True)
class ConstructorTemplate:
    name: Token
    arg_names: tuple[Token, ...]
    arg_types: tuple['Expression', ...]
    constructed_type: 'ConstructedType'

@dataclass(frozen=True)
class ConstructedType:
    constructor_info: tuple[
        tuple[Token, tuple[Token, ...], tuple[Union['Expression', None], ...]],
        ...
    ]
    type: Sort
    name: Token
    def _get_constructors(self) -> tuple[ConstructorTemplate]:
        templates = tuple(ConstructorTemplate(
            name,
            arg_names,
            # None indicates that this is a self-reference and we
            # replace that with this type
            tuple(expr if isinstance(expr, Expression) else self
                for expr in arg_types),
            self
        ) for name, arg_names, arg_types in self.constructor_info)
        return templates
    constructors = property(
        _get_constructors
    )


@dataclass(frozen=True)
class Constructor:
    template: ConstructorTemplate
    args: tuple['Expression',...]


Expression = Union[
    Variable,
    Sort,
    Pi,
    Apply,
    Lambda,
    Constructor,
    ConstructedType,
]

def pretty_print(expr: Expression) -> str:
    def pp(t: Expression) -> str:
        if isinstance(t, Variable):
            return f"{t.name.val}:{pp(t.type)}"
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
        # ConstructedType has no free vars
        else:
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
        case Lambda(lambda_arg_name, lambda_arg_type, result_type, body):
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
                    instantiate(expr.result_type, expr.arg_name, new_bound_var),
                    instantiate(expr.body, expr.arg_name, new_bound_var)
                )
            return Lambda(
                expr.arg_name,
                instantiate(expr.arg_type, arg_name, arg_expression),
                instantiate(expr.result_type, arg_name, arg_expression),
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
        case _:
            raise NotImplementedError

@functools.cache
def whnf(t: Expression) -> Expression:
    match t:
        # Trivial cases:
        case Variable(type, name):
            return t
        case Sort(universe):
            return t
        case Pi(arg_name, arg_type, result_type):
            return t
        case Lambda(arg_name, arg_type, result_type, body):
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
    if isinstance(t, Sort) and isinstance(s, Sort):
        return t.universe == s.universe
    elif isinstance(t, Variable) and isinstance(s, Variable):
            return t.name == s.name
    elif isinstance(t, Lambda) and isinstance(s, Lambda):
        if isinstance(t.body, Apply) and isinstance(t.body.arg_expression, Variable):
            # First check if eta-conversion is possible
            #TODO: eta-conversion may need to be done elsewhere
            #      or to otherwise handle the case where (lambda x: f y) has
            #      y def-eq to x but exactly equal to x
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
        return is_def_eq(t.func_expression, s.func_expression) and is_def_eq(t.arg_expression, s.arg_expression)

    #TODO: does eta expansion need to be moved to the last thing?
    # and why does the Lean code appear to do eta expansion only if
    # t is Lambda and s not-lambda (or vice-versa) - seems like both need to be lambda (or built-in or constructor)

    #TODO: make Prop have proof irrelevance
    return False

def infer_type(expr: Expression) -> Expression:
    if isinstance(expr, Variable):
        return expr.type
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
        reduced_func = whnf(expr.func_expression)
        if isinstance(reduced_func, Lambda):
            return infer_type(
                #???
                    instantiate(
                        reduced_func.body,
                        reduced_func.arg_name,
                        expr.arg_expression
                    )
                )
        #elif isinstance(expr.func_expression, Apply):
        #    return infer_type(
        #        #TODO
        #    )
        else:
            print(pretty_print(expr))
            print(pretty_print(reduced_func))
            raise NotImplementedError
    elif isinstance(expr, Lambda):
        return Pi(
            expr.arg_name,
            expr.arg_type,
            expr.result_type,
        )
    elif isinstance(expr, Constructor):
        return expr.template.constructed_type
    elif isinstance(expr, ConstructedType):
        return expr.type
    else:
        raise NotImplementedError