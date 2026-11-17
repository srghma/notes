# Does the extra cubical machinery in redtt/cooltt allow bigOmega?

No — this was an actual open problem, and it's now closed: normalization for univalent, Cartesian cubical type theory was proven, closing the last major open problem in the syntactic metatheory of cubical type theory, giving a reduction-free bijection between terms and normal forms, decidability of judgmental equality, and injectivity of type constructors. redtt and cooltt are both direct implementations of that theory. So even with the interval object, Kan composition, univalence-as-computation, and higher inductive types, the "every closed term reaches a normal form, nothing loops" guarantee still holds. More geometric structure doesn't buy you an escape hatch.

**Where a real, honest Big Omega *does* exist — by leaving the logic behind.**

- **Type-in-type used deliberately as a programming language, not a logic** — e.g. Lennart Augustsson's Cayenne, which has `Type : Type` on purpose. It's a known, accepted inconsistency: "a term of type A exists" stops meaning "A is true." That's the price, and Cayenne's designers pay it knowingly.
- **General recursion in `Type`/`Set`-land, not `Prop`** — every one of these systems (Lean, Arend, Agda, Idris) lets you write actually-looping *programs*, just not actually-looping *proofs*. Turn off the termination checker, or mark it `partial`/`unsafe`, and you get a function that spins forever at runtime — but it lives in a data universe with no claim to truth, so nothing breaks logically.
- **Untyped (or dynamically typed) lambda calculus** — `(λx. x x) (λx. x x)` loops immediately, precisely because there's no static discipline there to stand in the way. That's the one setting where Big Omega isn't just possible, it's the canonical example.

So: the type mismatch you found isn't a Lean-specific speed bump — it's one instance of a firewall every serious proof-relevant type theory needs, and different systems build that firewall at different points (predicativity, restricted elimination, or both), but none of the real ones leave a gap.
