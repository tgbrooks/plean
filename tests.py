import pytest
from plean import *
from library import *

x = Variable(Prop, Token("x"))
p = Variable(Prop, Token("p"))
r = Variable(Prop, Token("r"))
q = Variable(Prop, Token("q"))

# p |-> x
f = Lambda(
    Token("p"),
    Prop,
    x,
)

# p |-> r
fr = Lambda(
    Token("p"),
    Prop,
    r,
)
app_f = Apply(f, q)
app_fr = Apply(fr, q)


# p |-> p
f_id = Lambda(
    Token("p"),
    Prop,
    Variable(Prop, Token("p"))
)

# p |-> q |-> p
f_pqp = Lambda(
    Token("p"),
    Prop,
    Lambda(Token("q"), Prop, Variable(Prop, Token("p"))),
)

# p |-> q |-> q
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
        Variable(Prop, Token('y')),
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

    # (p |-> x) q  == x
    assert whnf(app_f) == x
    # (p |-> q |-> p) x p == x
    assert whnf(Apply(
        Apply(
            f_pqp,
            x,
        ),
        p
    )) == x

    # (p |-> q |-> q) x p == p
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
    assert is_def_eq(pi, Pi(Token('y'), Prop, Pi(Token('z'), Prop, Variable(Prop, Token('z')))))

    assert is_def_eq(app_f, app_f)

    assert is_def_eq(nat_zero, nat_zero)
    assert is_def_eq(nat_one, nat_one)

    # Applications
    assert is_def_eq(Apply(f_id, p), p)
    assert is_def_eq(Apply(f, p), x)
    assert is_def_eq(
        Apply(f_pqp, r),
        Lambda(Token('q'), Prop, r)
    )
    assert is_def_eq(
        Apply(Apply(f_pqp, r), p),
        r
    )

    # Eta conversion
    assert is_def_eq(f, Lambda(Token("r"), Prop, Apply(f, r)))
    assert is_def_eq(Lambda(Token("r"), Prop, Apply(f, r)), f)

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
    assert infer_type(Pi(Token('p'), Prop, p)) == Prop
    assert infer_type(Pi(Token('p'), Prop, q)) == Prop
    assert infer_type(Pi(Token('hp'), p, Variable(Sort(5), Token('x')))) == Sort(5)
    assert infer_type(Pi(Token('x'),  Variable(Sort(5), Token('X')), p)) == Prop # Due to imax

    assert infer_type(Apply(f_id, p)) == Prop
    assert infer_type(Pi(Token('p'), Prop, Prop)) == Sort(1)
    assert infer_type(Pi(Token('p'), Sort(universe=1), Prop)) == Sort(2)
    assert infer_type(Pi(Token('p'), Prop, Sort(universe=1))) == Sort(universe=2)

    assert infer_type(nat_one) == Nat
    assert infer_type(nat_zero) == Nat
    assert infer_type(infer_type(nat_greater)) == Sort(1)

    assert infer_type(Lambda(
        Token('x'),
        Type,
        Pi(
            Token('x'),
            Type,
            p
        )
    )) == Pi(Token('x'), Type, Prop)

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
        Token('?'),
        nat_twist.type,
        nat_twist.result_type,
    )
    assert infer_type(Apply(nat_twist, nat_one)) == Nat

    assert is_def_eq(Apply(nat_twist, nat_zero), nat_one)
    assert is_def_eq(Apply(nat_twist, nat_one), nat_zero)
    assert is_def_eq(nat_one, Apply(nat_twist, nat_zero))
    assert is_def_eq(nat_zero, Apply(nat_twist, nat_one))

    # TODO??
    #assert is_def_eq(Apply(Apply(nat_add, nat_one), nat_zero), nat_one)
    #assert infer_type(Apply(Apply(nat_add, nat_one), nat_zero)) == Nat

def test_logic():
    hp, hq = Variable(p, Token("hp")), Variable(q, Token("hq"))
    hr = Variable(r, Token("hr"))
    And_p_q = InstantiatedConstructedType(And, (p, q), ())
    h_And_p_q = Constructor(
        type = And,
        constructor_index=0,
        args = (hp, hq),
        type_args = (p, q),
    )
    h_And_p_p = Constructor(
        type = And,
        constructor_index=0,
        args = (hp, hp),
        type_args = (p,p),
    )
    assert is_def_eq(infer_type(h_And_p_q), And_p_q)
    assert not is_def_eq(infer_type(h_And_p_p), And_p_q)

    assert is_def_eq(h_And_p_q, and_intro(hp, hq))
    assert is_def_eq(infer_type(and_outro_left(h_And_p_q, p, q)), p)
    assert is_def_eq(infer_type(and_outro_right(h_And_p_q, p, q)), q)

    Or_p_q = InstantiatedConstructedType(Or, (p,q), ())
    h_Or_p_q1 = Constructor(
        type = Or,
        constructor_index = 0,
        args = (hp,),
        type_args = (p,q),
    )
    h_Or_p_q2 = Constructor(
        type = Or,
        constructor_index = 1,
        args = (hq,),
        type_args = (p,q),
    )

    assert is_def_eq(infer_type(h_Or_p_q1), Or_p_q)
    assert is_def_eq(infer_type(h_Or_p_q2), Or_p_q)
    assert is_def_eq(infer_type(h_Or_p_q2), infer_type(h_Or_p_q2))

    # Check true's trivial recursor
    assert is_def_eq(
        Apply( Recursor(
            type = InstantiatedConstructedType(true,(), ()),
            result_type = Type,
            match_cases = (
                Variable(Type, Token('X')),
            )
        ), true_intro),
        Variable(Type, Token('X'))
    )

    # Check proof irrelevance
    assert is_def_eq(h_Or_p_q1, h_Or_p_q2)
    assert not is_def_eq(h_Or_p_q1, h_And_p_p)

    h_or_p_q1 = or_intro_left(p, q, hp)
    h_or_p_q2 = or_intro_right(p, q, hq)
    assert is_def_eq(or_outro(
            h_or_p_q1,
            p,
            q,
            r,
            Lambda(Token('hp'), p, hr),
            Lambda(Token('hq'), q, hr),
        ),
        hr
    )

    and_p_q_implies_or_p_q = Lambda(
        Token('p'),
        Prop,
        Lambda(
            Token('q'),
            Prop,
            Lambda(
                Token("h_and_p_q"),
                And_p_q,
                or_intro_left(
                    Variable(Prop, Token('p')),
                    Variable(Prop, Token('q')),
                    and_outro_left(
                        Variable(
                            And_p_q,
                            Token('h_and_p_q')
                        ),
                        Variable(Prop, Token('p')),
                        Variable(Prop, Token('q')),
                    )
                )
            )
        )
    )

    proven_or_p_q = apply_list(and_p_q_implies_or_p_q, [p, q, and_intro(hp, hq)])
    assert is_def_eq(
        infer_type(proven_or_p_q),
        InstantiatedConstructedType(Or, (p,q), ()),
    )
    # Equal by proof irrelevance
    assert is_def_eq(
        proven_or_p_q,
        or_intro_left(p, q, Variable(p, Token('hp'))),
    )


    # p and (q or r) implies (p and q) or (p and r)
    p_and_q_or_p_and_r = InstantiatedConstructedType(
        Or,
        (
            InstantiatedConstructedType(And, (p,q), ()),
            InstantiatedConstructedType(And, (p,r), ())
        ),
        ()
    )
    p_and_q_or_r = InstantiatedConstructedType(
        And,
        (
            p,
            InstantiatedConstructedType(Or, (q,r), ()),
        ),
        ()
    )
    thm1 = lambda_chain(
        arg_names = [Token('p'), Token('q'), Token('r'), Token('hp_and_q_or_r')],
        arg_types = [Prop, Prop, Prop, p_and_q_or_r],
        body = or_outro(
            and_outro_right( # (q or r)
                Variable(p_and_q_or_r, Token('hp_and_q_or_r')),
                p,
                InstantiatedConstructedType(Or, (q,r), ()),
            ),
            q,
            r,
            p_and_q_or_p_and_r,
            Lambda(
                Token('hq'),
                q,
                or_intro_left(
                    InstantiatedConstructedType(And, (p,q), ()),
                    InstantiatedConstructedType(And, (p,r), ()),
                    and_intro(
                        and_outro_left(
                            Variable(p_and_q_or_r, Token('hp_and_q_or_r')),
                            p,
                            InstantiatedConstructedType(Or, (q,r), ())
                        ),
                        Variable(q, Token('hq')),
                    )
                )
            ),
            Lambda(
                Token('hr'),
                r,
                or_intro_right(
                    InstantiatedConstructedType(And, (p,q), ()),
                    InstantiatedConstructedType(And, (p,r), ()),
                    and_intro(
                        and_outro_left(
                            Variable(p_and_q_or_r, Token('hp_and_q_or_r')),
                            p,
                            InstantiatedConstructedType(Or, (q,r), ())
                        ),
                        Variable(r, Token('hr')),
                    )
                )
            ),
        )
    )
    assert is_def_eq(
        infer_type(
            apply_list(
                thm1,
                [p, q, r, Variable(p_and_q_or_r, Token("hp_and_q_or_r"))],
            ),
        ),
        p_and_q_or_p_and_r
    )

def test_eq():
    T = Variable(Type, Token('T'))
    x = Variable(T, Token('x'))
    y = Variable(T, Token('y'))
    z = Variable(T, Token('z'))
    eq_xy = InstantiatedConstructedType(
        type = Eq,
        type_args = (T, x,),
        type_indexes = (y,)
    )
    eq_yz = InstantiatedConstructedType(
        type = Eq,
        type_args = (T, y,),
        type_indexes = (z,)
    )
    eq_xz = InstantiatedConstructedType(
        type = Eq,
        type_args = (T, x,),
        type_indexes = (z,)
    )
    heq_xx = rfl(x)
    heq_xy = Variable(
        InstantiatedConstructedType(
            type = Eq,
            type_args = (T,x,),
            type_indexes = (y,),
        ),
        Token('heq_pq')
    )
    heq_xz = Variable(InstantiatedConstructedType(Eq, (T,x), (z,)), Token('heq_xz'))
    heq_yz = Variable(InstantiatedConstructedType(Eq, (T,y), (z,)), Token('heq_yz'))
    assert is_def_eq(infer_type(heq_xy), eq_xy)
    assert not is_def_eq(infer_type(heq_xx), heq_xy)

    Apply(Recursor(
        type = eq_xy,
        result_type = Lambda(Token('t'), T, eq_xy),
        match_cases = (
            heq_xy,
        ),
    ), heq_xy)

    thm_eq_transitive = lambda_chain(
        arg_names = [Token('T'), Token('x'), Token('y'), Token('heq_xy'), Token('heq_yz')],
        arg_types = [Type, T, T, eq_xy, eq_yz],
        body = Apply(
            Recursor(
                type = eq_xy,
                result_type = Lambda(
                    Token('t'),
                    T,
                    InstantiatedConstructedType(
                        type = Eq,
                        type_args = (T, Variable(T, Token('x'))),
                        type_indexes = (Variable(T, Token('t')),),
                    ),
                ),
                match_cases = (
                    Variable(eq_xy, Token('heq_xy')),
                ),
            ),
            Variable(eq_xy, Token('heq_xy')),
        )
    )
    proven_heq_xz = apply_list(
            thm_eq_transitive,
            [T, x, y, heq_xy, heq_yz]
        )
    assert is_def_eq(infer_type(proven_heq_xz), eq_xz)
    assert is_def_eq(proven_heq_xz, heq_xz)

def test_fails():
    with pytest.raises(AssertionError):
        # Try to prove a bogus theorem
        or_p_q_implies_and_p_q = Lambda(
            Token('p'),
            Prop,
            Lambda(
                Token('q'),
                Prop,
                Lambda(
                    Token("h_or_p_q"),
                    InstantiatedConstructedType(Or, (Variable(Prop, Token('p')), Variable(Prop, Token('q'))), ()),
                    and_intro(
                        or_outro(
                            Variable(
                                InstantiatedConstructedType(Or, (Variable(Prop, Token('p')), Variable(Prop, Token('q'))), ()),
                                Token('h_and_p_q')
                            ),
                            Variable(Prop, Token('p')),
                            Variable(Prop, Token('q')),
                            InstantiatedConstructedType(And, (Variable(Prop, Token('p')), Variable(Prop, Token('q'))), ()),
                            Lambda(
                                Token('hp'),
                                Variable(Prop, Token('p')),
                                Variable(Variable(Prop, Token('p')), Token('hp'))
                            ),
                            Lambda(
                                Token('hq'),
                                Variable(Prop, Token('q')),
                                Variable(Variable(Prop, Token('q')), Token('hq'))
                            ),
                        ),
                        or_outro(
                            Variable(
                                InstantiatedConstructedType(Or, (Variable(Prop, Token('p')), Variable(Prop, Token('q'))), ()),
                                Token('h_and_p_q')
                            ),
                            Variable(Prop, Token('p')),
                            Variable(Prop, Token('q')),
                            InstantiatedConstructedType(And, (Variable(Prop, Token('p')), Variable(Prop, Token('q'))), ()),
                            Lambda(
                                Token('hp'),
                                Variable(Prop, Token('p')),
                                Variable(Variable(Prop, Token('p')), Token('hp'))
                            ),
                            Lambda(
                                Token('hq'),
                                Variable(Prop, Token('q')),
                                Variable(Variable(Prop, Token('q')), Token('hq'))
                            ),
                        ),
                    )
                )
            )
        )

    with pytest.raises(AssertionError):
        a_type = Variable(Type, Token('T'))
        a_value = Variable(a_type, Token('v'))
        Recursor(
            type = InstantiatedConstructedType(Or, (p,q), ()),
            result_type = a_type,
            match_cases = (
                Lambda(
                    Token('hp'),
                    p,
                    a_value
                ),
                Lambda(
                    Token('hq'),
                    q,
                    a_value,
                )
            )
        )

    with pytest.raises(AssertionError):
        # Test constructors with wrong universe
        big_type = Variable(Sort(5), Token('T'))
        ConstructedType(
            constructors = (
                ConstructorTemplate(
                    name = Token('foo'),
                    arg_names = (Token('a'),),
                    arg_types = (Type,),
                    result_indexes = (),
                ),
            ),
            args = ((Token('a'), big_type),),
            indexes = (),
            type = Sort(1),
            name = Token("fail"),
        )