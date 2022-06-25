from plean import *

# Definitions
# Basic types and properties

Prop = Sort(0)
Type = Sort(1)

Nat = ConstructedType(
    (
        ConstructorTemplate(
            Token("Zero"),
            tuple(),
            tuple(),
            Constant(Token("Nat")),
        ),
        ConstructorTemplate(
            Token("Succ"),
            (Token("n"),),
            (Constant(Token('Nat')),),
            Constant(Token("Nat")),
        ),
    ),
    type = Type,
    name = Token('Nat'),
)
nat_zero = Constructor(
    template=Nat.constructors[0],
    args  = tuple(),
)
nat_succ = Nat.constructors[1]
nat_one = Constructor(nat_succ, args=(nat_zero,))
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
                    nat_succ,
                    (Variable(Nat, Token('n')),)
                ),
            ),
            nat_zero,
        )
    ),
    Token('succ_greater_zero')
)