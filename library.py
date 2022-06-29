from plean import *

# Definitions
# Basic types and properties

Prop = Sort(0)
Type = Sort(1)


false = ConstructedType(
    constructors = (),
    args =  (),
    type = Prop,
    name = Token("false")
)

true = ConstructedType(
    constructors = (
        ConstructorTemplate(
            Token("intro"),
            tuple(),
            tuple(),
        ),
    ),
    args = (),
    type = Prop,
    name = Token("true")
)
true_intro = Constructor(
    true,
    0,
    tuple(),
    type_args = (),
)

And = ConstructedType(
    constructors = (
        ConstructorTemplate(
            Token("intro"),
            (Token('a'), Token('b')),
            (Variable(Prop, Token('alpha')), Variable(Prop, Token('beta')),),
        ),
    ),
    name = Token("and"),
    args = ((Token('alpha'), Prop), (Token('beta'), Prop)),
    type = Prop,
)
def and_intro(hp, hq):
    p = infer_type(hp)
    q = infer_type(hq)
    return Constructor(
        type = And,
        constructor_index=0,
        args = (hp, hq),
        type_args = (p, q),
    )
def and_outro(and_p_q, side):
    p,q = and_p_q.type_args
    type_ = infer_type(and_p_q)
    assert isinstance(type_, InstantiatedConstructedType)
    return Apply(
        Recursor(
            type = type_,
            result_type = p if side == "left" else q,
            match_cases = (
                Lambda(
                    arg_name = Token('hp'),
                    arg_type = p,
                    body = Lambda(
                        arg_name = Token('hq'),
                        arg_type = q,
                        body = Variable(p, Token("hp")) if side == "left" else Variable(q, Token("hq")),
                    )
                ),
            ),
        ), 
        and_p_q,
    )
def and_outro_left(and_p_q):
    return and_outro(and_p_q, "left")
def and_outro_right(and_p_q):
    return and_outro(and_p_q, "right")

Or = ConstructedType(
    constructors = (
        ConstructorTemplate(
            Token('intro_l'),
            (Token('a'),),
            (Variable(Prop, Token('alpha')),),
        ),
        ConstructorTemplate(
            Token('intro_r'),
            (Token('b'),),
            (Variable(Prop, Token('beta')),),
        ),
    ),
    name = Token("or"),
    args = ((Token('alpha'), Prop), (Token('beta'), Prop)),
    type = Prop,
)

Nat_type = ConstructedType(
    (
        ConstructorTemplate(
            Token("Zero"),
            tuple(),
            tuple(),
        ),
        ConstructorTemplate(
            Token("Succ"),
            (Token("n"),),
            (Constant(Token('Nat')),),
        ),
    ),
    args = (),
    type = Type,
    name = Token('Nat'),
)
Nat = InstantiatedConstructedType(Nat_type, ())
constants['Nat'] = Nat
nat_zero = Constructor(
    Nat.type,
    0,
    args  = (),
    type_args = (),
)
nat_succ = Nat.type.constructors[1]
nat_one = Constructor(Nat.type, 1, args=(nat_zero,), type_args=())


# Basic destructor for testing purposes
# Sends 0 -> 1 and all others to zero
nat_twist = Recursor(
    Nat,
    Nat,
    (
        nat_one,
        Lambda(Token('n'), Nat, nat_zero),
    ),
)

# Addition a + b = a if b is 0 else (a+1) + (b-1)
#nat_add = Lambda(
#    Token('a'),
#    Nat,
#    Lambda(
#        Token('b'),
#        Nat,
#        Apply(
#            Destructor(
#                Nat,
#                (
#                    (tuple(), Variable(Nat, Token('a'))),
#                    ((Token('b'),),
#                        Apply(
#                            Apply(
#                                Constant(Token('nat_add')),
#                                Constructor(nat_succ, (Variable(Nat, Token('a')),)),
#                            ),
#                            Variable(Nat, Token('b'))
#                    )),
#                ),
#                Nat
#            ),
#            Variable(Nat, Token('b')),
#        )
#    )
#)
#constants['nat_add'] = nat_add

nat_greater = Variable(
    Pi(
        Token('n'),
        Nat,
        Pi(
            Token('m'),
            Nat,
            Prop
        )
    ),
    Token('>')
)

nat_succ_greater_zero = Variable(
    Pi(
        Token('n'),
        Nat,
        Apply(
            Apply(
                nat_greater,
                Constructor(
                    Nat.type,
                    1,
                    args = (Variable(Nat, Token('n')),),
                    type_args = (),
                ),
            ),
            nat_zero,
        )
    ),
    Token('succ_greater_zero')
)