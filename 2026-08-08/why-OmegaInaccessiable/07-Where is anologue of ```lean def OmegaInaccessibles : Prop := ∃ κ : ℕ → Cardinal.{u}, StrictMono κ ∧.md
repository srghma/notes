**There is NO analogue of `OmegaInaccessibles` in `coq-in-coq`.**

In `coq-in-coq`, the consistency theorem is the exact theorem you just pasted at the bottom of `Consistency.v`:

```coq
Theorem coc_consistency : forall t, ~ typ nil t absurd_prop.
```

Notice that `coc_consistency` **has no hypothesis at all**—it is an unconditional theorem (`forall t, ~ ...`).

---

### Why doesn't `coq-in-coq` need `OmegaInaccessibles`?

The difference comes down to **what calculus is being modeled**:

1. **`Lean4LeanModel` models full Lean 4 (`CIC` with infinite universes $Sort\ u$):**
   * Lean has arbitrary universe levels $0, 1, 2, \dots, u$.
   * As we saw earlier, proving consistency for an infinite hierarchy of universes requires $\omega$ inaccessible cardinals.
   * Because Lean cannot prove the existence of $\omega$ inaccessibles inside a fixed ambient universe, `Lean4LeanModel` must take `OmegaInaccessibles` as an **explicit hypothesis**.

2. **`coq-in-coq` models basic $CC$ (Calculus of Constructions with only 2 fixed sorts: `prop` and `set`):**
   * `coq-in-coq` does **not** have an infinite sequence of universe parameters ($Type_0, Type_1, Type_2, \dots$). It only has `prop` and `set`.
   * Because the target language ($CC$) only has 2 fixed sorts, the host language (Coq) already has higher universe levels (`Type`) that are more than strong enough to interpret $CC$'s `prop` and `set`.
   * Therefore, Coq can prove the consistency of $CC$ **unconditionally**, without assuming any extra axioms or large cardinal hypotheses!

---

### How `coq-in-coq` proves consistency in these files

Instead of a set-theoretic model using inaccessible cardinals, `coq-in-coq` uses a **syntactic / logical relations model**:

1. **`Int_typ.v` / `Int_term.v` / `Int_stab.v`:** 
   Defines an interpretation (model) of $CC$ terms into Coq's native types (`Prop`, `Set`, `Type`).
2. **`Strong_Norm.v`:** 
   Proves **Strong Normalization** (`str_norm`) for $CC$ using Girard's *Candidates of Reducibility* (Logical Relations) technique inside Coq.
3. **`Consistency.v`:** 
   Uses Strong Normalization (`str_norm`) and subject reduction to show that any proof of `absurd_prop` (`∀ P : Prop, P`) would reduce to a normal form. Since no normal form proof of `absurd_prop` exists (`coc_consistency_nf`), no term can prove `absurd_prop`.
