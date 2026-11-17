## If `Quot` isn't an inductive, what is it?

It's an **axiomatic primitive type former** — a small, hand-picked extension of the kernel's type theory. Concretely, in Lean's trusted base `Quot` is:

- 4 *primitive constants* whose **types** are checked but whose **implementations are trusted** (no definitional body): `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`;
- 1 *axiom*: `Quot.sound`;
- 1 *definitional computation rule* wired into `whnf`: `Quot.lift f h (Quot.mk r a) ≡ f a` (and the analogous one for `Quot.ind`);
- a guard that `Eq` exists with the right shape (`check_eq_type`).

In the language of homotopy type theory, `Quot` is exactly a **set quotient**, which is a *higher inductive type* (HIT). But Lean does **not** implement general HITs — it bakes in this one specific HIT as an axiom + a reduction rule.

## Why it can't be an ordinary inductive

Ordinary inductive types are **freely generated** by their point constructors. The kernel's inductive machinery can only add *elements* (`Nat.zero`, `Nat.succ`, `Eq.refl`, …); it can never add an **equality between two distinct elements** of the type it's defining.

`Quot` needs precisely that:

```lean
Quot.sound : r a b → Quot.mk r a = Quot.mk r b
```

`Quot.mk r a` and `Quot.mk r b` are built from different inputs, yet must become *propositionally equal*. That is an **equality/path constructor**, and "a type former with point constructors *and* path constructors" is the definition of a HIT. CIC (Lean's and Coq's base calculus) has no path constructors, so quotients are simply not expressible as inductives — they must be *added*.

## Can you define `Quot` in Lean itself?

**Propositionally: yes. Definitionally: no** — and the "no" is the entire reason it lives in the kernel.

You can encode a quotient as "the type of its equivalence classes":

```lean
def Quot' (r : α → α → Prop) := { P : α → Prop // ∃ a, P = fun b => r a b }
```

With `funext`, `propext`, and `Classical.choice`, you can even *prove* an analogue of `sound` and a *propositional* `lift`-beta law. Lean/Coq stdlib and mathlib have done exactly this kind of thing.

But the encoded version only gives you

```lean
Quot'.lift f h (Quot'.mk r a) = f a   -- provable, but NOT by rfl
```

whereas the kernel primitive gives you that equation **judgmentally** (`by rfl`, holds in `whnf`, usable by `decide`, `simp only`, unification, `Decidable` instances, etc.). You cannot manufacture a *new definitional reduction rule* from inside CIC (Calculus of Inductive Constructions) — reduction rules come only from (a) β/η/ι of the built-in formers, or (b) primitives the kernel special-cases. So there is **no generic Lean syntax** that produces a type with its own judgmental computation rule; the only two sources are inductive recursors and the built-in `Quot`.

That's also why `Quot` *is* "the generic syntax": there is exactly one primitive quotient, and `Quotient`, `Int`, `Rat`, `Multiset`, `Finset`, … are all *library* constructions on top of it.

**Practical consequence for your "extract Quot from the kernel" goal:** you can't drop it to a pure-Lean encoding without losing the definitional `lift`-beta rule, and a huge amount of code (anything using `Quotient`/`Int`/`Rat`/mathlib quotients, plus `decide`-style reductions through quotients) depends on that rule holding by `rfl`. The kernel footprint is already about as minimal as CIC allows: 4 constants + 1 axiom + 1 whnf rule + the `Eq`-shape guard. Making it non-primitive requires *changing the underlying type theory*, not refactoring the port.

## HoTT / cubical: yes, this is exactly where quotients become definable *in-language*

The "more low-level" thing you're reaching for is **Higher Inductive Types**, and the system that makes them *compute* is **cubical type theory**.

- In **plain MLTT/CIC** (Lean, Coq), equality is itself an inductive (`Eq`/`Id`) with no computational path structure, so quotients must be axiomatic.
- In **cubical TT**, equality is the **primitive** object: there's an interval `I`, and paths, `transp`, and `hcomp` (Kan composition) have their own reduction rules. Because paths are primitive and *compute*, you can declare quotients as a genuine HIT:

  ```
  data Quotient (A : Type) (R : A → A → Prop) where
    mk    : A → Quotient A R
    sound : (a b : A) → R a b → mk a ≡ mk b   -- a real path constructor
    -- + set-truncation
  ```

  and the eliminator **computes on both `mk` and `sound`**. So there the quotient is defined *inside the language*, no axiom. The cost: the kernel is dramatically more complex (interval, face lattice, composition/Kan operations, coercion), which is precisely why Lean and Coq chose the axiomatic shortcut instead.

The deep reason Lean can get away with the shortcut: `Quot.sound` lands in `Prop`, and proofs in `Prop` are proof-irrelevant and never "run," so a *non-computing* `sound` costs nothing operationally. Only `lift` needs to compute, and one whnf rule handles that.

## Survey of other systems

| System                      | Foundation                                              | Quotients                                                                                                                                                                                                                                                                                                   |
| --------------------------- | ------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Lean 4**                  | CIC + primitives                                        | Axiomatic `Quot` (this discussion) — definitional `lift`-beta, `sound` as axiom                                                                                                                                                                                                                             |
| **Rocq / Coq**              | CIC                                                     | **No primitive quotient.** In practice: **setoids** (`Setoid`/`Equivalence` + `Proper`/generalized rewriting) — the famous "setoid hell." Can encode quotients via added axioms (funext/propext/choice) but only with *propositional* beta. `SProp` gives definitional proof irrelevance but not quotients. |
| **Cubical Agda**            | Cubical TT                                              | Native HITs; `SetQuotient` (`_/_`) in the cubical library, fully computational `sound`                                                                                                                                                                                                                      |
| **Agda (vanilla)**          | MLTT                                                    | No primitive; setoids, or postulated quotients (or switch on `--cubical`)                                                                                                                                                                                                                                   |
| **Arend**                   | HoTT-flavored w/ interval + native HITs                 | Built-in HITs incl. set-level quotients (`\truncated \data`); `sound`-like constructors with computation rules — genuinely in-language                                                                                                                                                                      |
| **cooltt / redtt / redPRL** | Cartesian cubical (cooltt/redtt) / cubical PRL (redPRL) | HITs supported ⇒ quotients definable as computing HITs; redPRL descends from Nuprl's PRL tradition                                                                                                                                                                                                          |
| **Nuprl**                   | Extensional computational TT                            | **Quotient type is primitive** (`{x,y : A // E}`), leaning on the system's extensional equality — a different flavor entirely                                                                                                                                                                               |
| **Isabelle/HOL**            | Classical simple type theory + choice                   | `quotient_type` command + Lifting/Transfer package; "has quotients," but HOL has no definitional reduction at all, so it's not comparable to CIC's judgmental rule                                                                                                                                          |

So to directly answer "does X have Quot": the **cubical / HIT systems (cooltt, redtt, Arend, Cubical Agda)** let you *define* it in-language *with a computing path*; **Rocq/Coq** does **not** — it uses setoids or added axioms; **Nuprl** has it as an extensional primitive; **Isabelle/HOL** has it as a package on a different foundation.

If you genuinely wanted `Quot` "not baked into the kernel," the only principled route is a **cubical kernel with HITs** — which is a different and substantially larger kernel than the CIC one you're porting. Within CIC, the current axiom-plus-one-reduction-rule form is the canonical minimal answer, and matches what Coq would need too (Coq just declined to add it).
