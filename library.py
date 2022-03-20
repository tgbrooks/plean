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


# Basic destructor for testing purposes
# Sends 0 -> 1 and all others to zero
nat_twist = Destructor(
    Nat,
    (
        (tuple(), nat_one),
        ((Token('n'),), nat_zero),
    ),
    Nat
)

# Hack to define a + b recursively
# Our frozen datastructures cannot have self-reference
# So we instead make a lambda function and apply it to itself, so
# add_precursor(add_precursor) = add
nat_add_precursor = Lambda(
    Token('f'),
    Pi(Token('x'), Nat, Nat),
    Lambda(
        Token('a'),
        Nat,
        Destructor(
            Nat,
            ((tuple(), Variable(Nat, Token('a'))),
            ((Token('b'),),
                Apply(
                    Apply(
                        Variable(Pi(Token('x'), Nat, Nat), Token('f')),
                        Constructor(nat_succ, (Variable(Nat, Token('a')),)),
                    ),
                    Variable(Nat, Token('b'))
                )
            )
            ),
            Nat,
        )
    )
)
nat_add = Apply(nat_add_precursor, nat_add_precursor)

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