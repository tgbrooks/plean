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
constants['false'] = InstantiatedConstructedType(false, ())

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
constants['true'] = InstantiatedConstructedType(true, ())
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
constants['and'] = And

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
nat_zero = Constructor(
    Nat.type,
    0,
    args  = (),
    type_args = (),
)
nat_succ = Nat.type.constructors[1]
nat_one = Constructor(Nat.type, 1, args=(nat_zero,), type_args=())
constants['Nat'] = Nat


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