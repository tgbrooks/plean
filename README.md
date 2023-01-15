# Plean

Plean is a Python implementation of the type system behind the [Lean](https://leanprover.github.io/about/) programming language / theorem prover.
Plean is not intended to be production ready or useful for any tasks other than learning more about how Lean works.
It does not implement any proof assistant features and is extremely verbose to use.
However, it is complete enough to write and check proofs of basic facts.
For example, the following is a proof that "p and q" implies "p or q" for any propositions p, q.

``` python
from plean import *
from library import *

p = Variable(Prop, Token("p"))
q = Variable(Prop, Token("q"))
And_p_q = InstantiatedConstructedType(And, (p, q), ())

# proof that p and q implies p or q
# In lean, this would be:
# example : (∀ p: Prop, ∀ q: Prop, p ∧ q → p ∨ q) :=
#   (λ p, λ q, λ h, or.intro_left q (and.elim_left h))
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
                p,
                q,
                and_outro_left(
                    Variable(
                        And_p_q,
                        Token('h_and_p_q')
                    ),
                    p,
                    q,
                )
            )
        )
    )
)
```