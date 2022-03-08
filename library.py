from plean import *

# Definitions
# Basic types and properties

Prop = Sort(0)
Type = Sort(1)

Nat = ConstructedType(
    (
        (
            Token("Zero"),
            tuple(),
            tuple(),
        ),
        (
            Token("Succ"),
            (Token("n"),),
            (None,),
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