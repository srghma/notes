In Mathlib, **`Lean.Order.Heyting`** actually corresponds to **`Order.Frame`** (a *complete* Heyting algebra), whereas Mathlib’s **`HeytingAlgebra`** is a *weaker* notion.

| Feature | `Lean.Order.Heyting` (`Std`) | Mathlib `Order.Frame` (`MinimalAxioms`) | Mathlib `HeytingAlgebra` |
| :--- | :--- | :--- | :--- |
| **Mathematical meaning** | Complete Heyting algebra (Frame) | Complete Heyting algebra (Frame) | Bounded lattice with `⇨` (not necessarily complete!) |
| **Sort** | `Prop` (`abbrev`) | `Type u` (`class`) (though `MinimalAxioms` is `Prop`) | `Type u` (`class`) |
| **Base requirement** | `[CompleteLattice α]` | `extends CompleteLattice α, HeytingAlgebra α` | Bounded lattice (`Lattice` + `⊤` + `⊥`) |
| **Core axiom** | `∀ a, PreservesSup (meet a)` (`a ⊓ sup s = ...`) | `a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b` | `a ≤ b ⇨ c ↔ a ⊓ b ≤ c` (`le_himp_iff`) |
| **Where does `⇨` come from?** | Built noncomputably via `Classical.choose` (`sup`) | Field of `HeytingAlgebra` (or built via `ofMinimalAxioms`) | Explicit data field `himp` on the typeclass |
| **On `Prop`, `a ⇨ b` is...** | Equal via `propext` (`himp_prop_eq_imp`) | **Definitionally** `a → b` | **Definitionally** `a → b` |

----

> so You say
> `∀ a, PreservesSup (meet a) (a ⊓ sup s = ...)`
> is same as
> `a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b?`

**Yes — in any `CompleteLattice`, they are completely equivalent!**
???

**`sSup`** stands for **set supremum** — the least upper bound (join / "ceiling") of an entire `Set α` (which in Lean is `α → Prop`).

It is Mathlib’s direct equivalent of **`CompleteLattice.sup`** from `Lean.Order`!

---

### 1. What it is (and how it compares to `⊔` and `⨆`)

Mathlib has three different "sup" names depending on how many inputs you give it:

| Name | Symbol | Type | Meaning |
| :--- | :--- | :--- | :--- |
| **`CompleteLattice.sup`** (from `Max` / `SemilatticeSup`) | `a ⊔ b` | `α → α → α` | Binary supremum of **2 elements** |
| **`sSup`** (from `SupSet`) | *(no infix symbol)* | `Set α → α` | **Set** supremum of an arbitrary **set** `s : Set α` |
| **`iSup`** | `⨆ i, f i` | `(ι → α) → α` | **Indexed** supremum, defined as `sSup (Set.range f)` |

```lean
noncomputable def CompleteLattice.sup (c : α → Prop) : α :=
  Classical.choose (CompleteLattice.has_sup c)

class SupSet (α : Type*) where
  sSup : Set α → α
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/CompleteSublattice.html#CompleteSublattice.instSupSet

https://github.com/leanprover-community/mathlib4/blob/b476d8fd31a353258f27f2e35e8e25b689d6a052/Mathlib/Order/Notation.lean#L58-L62
syntax:68 term:68 " ⊔ " term:69 : term
| `($a ⊔ $b) => `(Max.max $a $b)

https://github.com/leanprover-community/mathlib4/blob/b476d8fd31a353258f27f2e35e8e25b689d6a052/Mathlib/Order/Defs/Lattice.lean#L52-L63
/-- A `SemilatticeSup` is a join-semilattice, that is, a partial order
  with a join (a.k.a. lub / least upper bound, sup / supremum) operation
  `⊔` which is the least element larger than both factors. -/
class SemilatticeSup (α : Type u) extends PartialOrder α where
  /-- The binary supremum, used to derive `Max α` -/
  sup : α → α → α
  /-- The supremum is an upper bound on the first argument -/
  protected le_sup_left : ∀ a b : α, a ≤ sup a b
  /-- The supremum is an upper bound on the second argument -/
  protected le_sup_right : ∀ a b : α, b ≤ sup a b
  /-- The supremum is the *least* upper bound -/
  protected sup_le : ∀ a b c : α, a ≤ c → b ≤ c → sup a b ≤ c

instance SemilatticeSup.toMax [SemilatticeSup α] : Max α where max a b := SemilatticeSup.sup a b

-- https://github.com/leanprover-community/mathlib4/blob/b476d8fd31a353258f27f2e35e8e25b689d6a052/Mathlib/Order/SetNotation.lean#L49-L50
/-- Indexed supremum. -/
notation3 "⨆ " (...)", " r:60:(scoped f => iSup f) => r
```

-----

> `noncomputable def CompleteLattice.sup (c : α → Prop) : α := Classical.choose (CompleteLattice.has_sup c)`
>
> where `has_sup` is
>
> `has_sup (c : α → Prop) : Exists (is_sup c)`
>
> where `is_sup`
>
> `@[expose] def is_sup {α : Sort u} [PartialOrder α] (c : α → Prop) (s : α) : Prop := ∀ x, s ⊑ x ↔ (∀ y, c y → y ⊑ x)`
>
> why all this indirection? why not right away define just `sup` on `CompleteLattice`?
>
> and then if user really needs to taint himself with choose axiom - its his choice

How to find out ALL instances of CompleteLattice?

```lean
import Std.Internal.Order.Heyting
import Lean

open Lean Lean.Meta Lean.Order Std.Internal.Order

#eval show MetaM Unit from do
  let u ← mkFreshLevelMVar
  let α ← mkFreshExprMVar none
  let ty := mkApp (mkConst ``Lean.Order.CompleteLattice [u]) α
  let entries ← (← getGlobalInstancesIndex).getUnify ty
  let erased ← getErasedInstances
  for e in entries do
    if let some name := e.globalName? then
      if !erased.contains name then
        IO.println name

-- Std.WP.Assertion.toCompleteLattice
-- Std.Internal.Order.instCompleteLatticeProp
-- Lean.Order.ImplicationOrder.instCompleteLattice
-- Lean.Order.ReverseImplicationOrder.instCompleteLattice
-- Lean.Order.instCompleteLatticePProd
-- Lean.Order.instCompleteLatticeUnit
-- Lean.Order.instCompleteLatticeProd
-- Lean.Order.instCompleteLatticePi
```

-------------

eli5

### ELI5: The Lego / Toolbox Analogy

Imagine you are building a system of **"logical truth values"** (like `True`/`False`, or shades of truth between them) where you can combine statements with **AND (`⊓`)**, **OR (`⊔`)**, and **IF–THEN (`⇨`)**.

1. **Mathlib `HeytingAlgebra` = A normal logic kit**
   - You can combine **two** things at a time (`a ⊓ b`, `a ⊔ b`), you have a bottom (`⊥` = False) and a top (`⊤` = True), and you have an "if–then" arrow (`a ⇨ b`).
   - **What's missing?** You *cannot* necessarily take the "OR" of **infinitely many** things at once.
   - *Example:* Our `WithTop (WithBot ℚ)` (the rational numbers plus `⊥` and `⊤`). You can compare any two fractions and do `⊓`, `⊔`, `⇨`, so it's a `HeytingAlgebra`. But if you ask for the least upper bound of $\{q \in \mathbb{Q} \mid q^2 < 2\}$, $\sqrt{2}$ isn't a rational number—so infinite `OR` fails!

2. **Mathlib `Order.Frame` (and `MinimalAxioms`) = The "Infinite Superpower" logic kit**
   - It is a `HeytingAlgebra` **plus** you are guaranteed that **every** collection of elements—even an infinite one—has a least upper bound (`sSup`, infinite OR) and greatest lower bound (`sInf`, infinite AND), and `AND` distributes over infinite `OR`.
   - **`MinimalAxioms`** is just a **shortcut to build one**: if you already proved your type is a `CompleteLattice` (has infinite `OR` and `AND`), you don't have to manually define `⇨` and `ᶜ` (`¬`). You just prove one tiny rule (`a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b`), and `Order.Frame.ofMinimalAxioms` automatically builds `⇨`, `ᶜ`, and the whole `Order.Frame` for you!
   - *Example:* Open sets of a topological space (like open subsets of $\mathbb{R}$). The union of *any* number (even uncountably many!) of open sets is still open, and finite intersections distribute over arbitrary unions.

3. **`Lean.Order.Heyting` (`Std`) = Lean's built-in minimalist version of `Order.Frame`**
   - Mathematically, it is the **exact same thing** as `Order.Frame` (a complete Heyting algebra, as we proved!).
   - Why does it exist separately? Because `Std` does **not** import Mathlib! Lean's core team wrote a lightweight `CompleteLattice` + `Heyting` inside `Std.Internal.Order` (originally to power Lean's internal partial/coinductive fixpoint machinery, `partial_fixpoint` / `coinductive_fixpoint`).
   - Instead of asking you to provide an explicit `⇨` operation, it takes a `Lean.Order.CompleteLattice` and *defines* `⇨` noncomputably by taking the `sup` of all `x` such that `a ⊓ x ≤ b`.
