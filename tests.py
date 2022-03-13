import pytest
from plean import *
from library import *

x = Variable(Prop, Token("x"))
p = Variable(Prop, Token("p"))
r = Variable(Prop, Token("r"))
q = Variable(Prop, Token("q"))

# p -> x
f = Lambda(
    Token("p"),
    Prop,
    x,
)

# p -> r
fr = Lambda(
    Token("p"),
    Prop,
    r,
)
app_f = Apply(f, q)
app_fr = Apply(fr, q)


# p -> p
f_id = Lambda(
    Token("p"),
    Prop,
    Variable(Prop, Token("p"))
)

# p -> q -> p
f_pqp = Lambda(
    Token("p"),
    Prop,
    Lambda(Token("q"), Prop, Variable(Prop, Token("p"))),
)

# p -> q -> q
f_pqq = Lambda(
    Token("p"),
    Prop,
    Lambda(Token("q"), Prop, Variable(Prop, Token("q"))),
)

# Prop -> Prop -> Prop
pi = Pi(
    Token("x"),
    Prop,
    Pi(
        Token("y"),
        Prop,
        Prop,
    )
)


def test_free_vars():
    assert free_vars(p) == set([Token("p")])
    assert free_vars(f_id) == set()
    assert free_vars(Apply(fr, Variable(Prop, Token('p')))) == set([Token('r'), Token('p')])
    assert free_vars(fr) == set([Token("r")])
    assert free_vars(nat_one) == set()

def test_instantiate():
    assert instantiate(f, Token("x"), r) == fr
    inst_app = instantiate(app_f, Token("x"), r) 
    assert isinstance(inst_app, Apply)
    assert inst_app.arg_expression == app_fr.arg_expression
    assert inst_app == app_fr


    # Substituting y shouldn't change anything
    # since y is bound locally
    assert instantiate(pi, Token('y'), q) == pi


    # Substituting in an expression with a free variable
    # that collides with a bound var will have to rename
    # the bound var
    assert instantiate(fr, Token('r'), p) == Lambda(Token("p`"), Prop, p)

def test_whnf():
    assert whnf(fr) == fr
    assert whnf(q) == q
    assert whnf(pi) == pi
    assert whnf(Prop) == Prop
    assert whnf(nat_one) == nat_one
    assert whnf(nat_zero) == nat_zero

    # (p -> x) q  == x
    assert whnf(app_f) == x
    # (p -> q -> p) x p == x
    assert whnf(Apply(
        Apply(
            f_pqp,
            x,
        ),
        p
    )) == x

    # (p -> q -> q) x p == p
    assert whnf(Apply(
        Apply(
            f_pqq,
            x,
        ),
        p
    )) == p

def test_is_def_eq():
    assert is_def_eq(q, q)
    assert is_def_eq(f, f)
    assert is_def_eq(
        Pi(Token('x'), Prop, Prop),
        Pi(Token('y'), Prop, Prop),
    )
    assert is_def_eq(
        f_id,
        Lambda(Token('q'), Prop, q),
    )
    assert is_def_eq(f, Lambda(Token('q'), Prop, x))
    assert not is_def_eq(f, fr)
    assert not is_def_eq(f_pqp, f_pqq)
    assert is_def_eq(pi, pi)
    assert is_def_eq(pi, Pi(Token('y'), Prop, Pi(Token('z'), Prop, Prop)))

    assert is_def_eq(app_f, app_f)

    assert is_def_eq(nat_zero, nat_zero)
    assert is_def_eq(nat_one, nat_one)

    # Eta conversion
    assert is_def_eq(f, Lambda(Token("r"), Prop, Apply(f, r)))
    assert is_def_eq(Lambda(Token("r"), Prop, Apply(f, r)), f)
    assert not is_def_eq(f, Lambda(Token('r'), Prop, Apply(f, x)))

def test_infer_type():
    assert infer_type(p) == Prop
    assert infer_type(Prop) == Sort(1)
    assert infer_type(f_id) == Pi(Token('p'), Prop, Prop)
    assert infer_type(f_pqp) == Pi(
        Token('p'),
        Prop,
        Pi(
            Token('q'),
            Prop,
            Prop
        )
    )

    assert infer_type(Apply(f_id, p)) == Prop
    assert infer_type(Pi(Token('p'), Prop, Prop)) == Sort(1)
    assert infer_type(Pi(Token('p'), Sort(universe=1), Prop)) == Sort(2)
    assert infer_type(Pi(Token('p'), Prop, Sort(universe=1))) == Sort(universe=2)

    assert infer_type(nat_one) == Nat
    assert infer_type(nat_zero) == Nat
    assert infer_type(infer_type(nat_greater)) == Sort(1)

def test_nat():
    thm_one_gt_zero = Apply(
        nat_succ_greater_zero,
        nat_zero
    )
    assert infer_type(thm_one_gt_zero) == Apply(
        Apply(
            nat_greater,
            nat_one,
        ),
        nat_zero,
    )

    assert infer_type(nat_twist) == Pi(
        Token(''),
        nat_twist.type,
        nat_twist.result_type,
    )
    assert infer_type(Apply(nat_twist, nat_one)) == Nat

    #assert is_def_eq(Apply(Apply(nat_add, nat_one), nat_zero), nat_one)
    assert infer_type(Apply(Apply(nat_add, nat_one), nat_zero)) == Nat