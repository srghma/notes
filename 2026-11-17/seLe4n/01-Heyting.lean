module

prelude
public import Std.Internal.Order.OfProp
public import Std.Internal.Order.PreservesSup
public import Init.ByCases
import Init.Classical

@[expose] public section

/-!
# Heyting implication

`a ⇨ b` is the upper adjoint of the lattice meet `a ⊓ ·`. A complete lattice whose meet preserves
suprema is a frame, and `⇨` then satisfies the laws of an implication: modus ponens, currying and
distribution of `⊓` over `⊔`.
-/

namespace Lean.Order

open PartialOrder Std.Internal.Order

universe u v

section Basic

-- /--
-- A partial order is a reflexive, transitive and antisymmetric relation.
--
-- This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
-- -/
-- class PartialOrder (α : Sort u) where
--   /--
--   A “less-or-equal-to” or “approximates” relation.
--
--   This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
--   -/
--   rel : α → α → Prop
--   /-- The “less-or-equal-to” or “approximates” relation is reflexive. -/
--   rel_refl : ∀ {x}, rel x x
--   /-- The “less-or-equal-to” or “approximates” relation is transitive. -/
--   rel_trans : ∀ {x y z}, rel x y → rel y z → rel x z
--   /-- The “less-or-equal-to” or “approximates” relation is antisymmetric. -/
--   rel_antisymm : ∀ {x y}, rel x y → rel y x → x = y
-- @[inherit_doc] scoped infix:50 " ⊑ " => PartialOrder.rel

----- c means "is collection?"
----- s means "proposed supremum"

-- direction -> : if x is more than s (not possible, can only be equal. right?)
--    then such x should be more than all other elements of collection
--
--      Example: let collection be {2,4,6} over N (from 0 to inf)
--      - proposed supremum is inf:
--         does it give `s ⊑ x → (∀ y, c y → y ⊑ x)`? s inf , x inf, YES
--         does it give `(∀ y, c y → y ⊑ x) → s ⊑ x`? NO, counterexample is 6 or 7
--      - proposed supremum is 2:
--         does it give `s ⊑ x → (∀ y, c y → y ⊑ x)`? NO (x is 2 breaks, how about 1? 0?)
--         does it give `(∀ y, c y → y ⊑ x) → s ⊑ x`? YES
--      - proposed supremum is 4:
--         does it give `s ⊑ x → (∀ y, c y → y ⊑ x)`? NO (x is 2 or 4 breaks)
--         does it give `(∀ y, c y → y ⊑ x) → s ⊑ x`? YES
--      - proposed supremum is 6:
--         does it give `s ⊑ x → (∀ y, c y → y ⊑ x)`? YES
--         does it give `(∀ y, c y → y ⊑ x) → s ⊑ x`? YES
--
--
--     Compare Nat, Rat, and Real in lean (ConditionallyCompleteLinearOrderBot):
--       Every bounded nonempty subset has a supremum?
--       Nat - yes (though unbounded - no, inf doesnt exist)
--       Rat - no (bc from 0 to square root of 2 - the sepremum is not in Rat, its in Real)
--       Rat - yes (bc from 0 to square root of 2 - the sepremum is in Real)

-- namespace PartialOrder
-- @[expose] def is_sup {α : Sort u} [PartialOrder α] (c : α → Prop) (s : α) : Prop :=
--   ∀ x, s ⊑ x ↔ (∀ y, c y → y ⊑ x)


--------- x and y are walls, w is floow below both walls
---------   two elements "meet" ∧ at their greatest lower bound
---------   A={1,2,3}  B={2,3,4}
---------   - Meet = intersection: A∧B=A∩B={2,3} (is sub of {1,2,3} and of {2,3,4} and all that ...)
---------   - Join = union:        A∨B=A∪B={1,2,3,4}

--------- is_meet ({1, 2, 3} : Set Nat) ({2, 3, 4} : Set Nat) {2, 3} := by...
--------- is_meet 6 4 4 := by...


---------------   two elements "join" v at their smallest upper bound

-- @[expose] def is_meet (x y w : α) : Prop :=
--   w ⊑ x ∧
--   w ⊑ y ∧
--   ∀ z, z ⊑ x → z ⊑ y → z ⊑ w
---------------   "Whatever number z you choose, if it's below BOTH 6 and 4, it must also be below 4."

-- end PartialOrder

-- class CompleteLattice (α : Sort u) extends PartialOrder α where
--   /--
--   The least upper bound of an arbitrary subset exists.
--   -/
--   has_sup (c : α → Prop) : Exists (is_sup c)

-- noncomputable def CompleteLattice.sup (c : α → Prop) : α :=
--   Classical.choose (CompleteLattice.has_sup c)

variable {α : Type u} [CompleteLattice α]

------------- f is mapper
------------- s is collection (same as c in is_sup)

------------- "supremum of collection s" after f
------------- is equal to
------------- supremum of the collection you get after applying f to every element of the original collection s

------------- E.g.
------------- x={2,4,6}
------------- f(x) = 2x
------------- y={4,8,12}
-------------
------------- `fun y => ∃ x, s x ∧ y = f x` is a new collection maker
-------------
------------- sup{2,4,6}=6
------------- sup{4,8,12}=12


-- class PreservesSup {α : Type u} [CompleteLattice α] (f : α → α) : Prop where
--   /-- `f` preserves joins. -/
--   map_sup (s : α → Prop) :
--     f (CompleteLattice.sup s) = CompleteLattice.sup (fun y => ∃ x, s x ∧ y = f x)


------------------- f (Classical.choose
-------------------     (show ∃ a,
-------------------       ∀ x, a ⊑ x ↔ (∀ y, s y → y ⊑ x)
-------------------       from CompleteLattice.has_sup s))
------------------- =
------------------- Classical.choose
-------------------   (show ∃ b,
-------------------     ∀ x, b ⊑ x ↔
-------------------       (∀ y, (∃ x, s x ∧ y = f x) → y ⊑ x)
-------------------     from CompleteLattice.has_sup
-------------------       (fun y => ∃ x, s x ∧ y = f x))

-- NOT `Infimum of a = Supremum of "a in the reversed order"`
-- BUT
--   1. Collect every valid floor of {5, 7, 10}: ..., 1, 2, 3, 4, 5
--   (Every one of these is ≤ 5, ≤ 7, and ≤ 10.)
--   2. Feed all those floors into your ceiling machine (sup):
--   The ceiling of {..., 1, 2, 3, 4, 5} is 5!
--
-- noncomputable def inf (c : α → Prop) : α := CompleteLattice.sup (fun x => ∀ y, c y → x ⊑ y)

-- /-- Binary meet (infimum) -/
-- `fun z => z = x ∨ z = y` will return just 2-element set `{x, y}`
-- ### Concrete examples
-- - **Numbers** (ordered by `≤`): `meet 5 8` = `inf {5, 8}` = `5` (i.e. `min`).
-- - **Sets** (ordered by `⊆`): `meet A B` = `inf {A, B}` = A ∩ B (intersection — the biggest set inside both A and B).
Suppose A = {1,2}, B = {2,3}, The order ⊑ is ⊆ (is inside / subset of).
CompleteLattice.sup (fun x => fun y = y = {1,2} ∨ y = {2,3} → x ⊑ y)
CompleteLattice.sup (fun x => x ⊑ {1,2} ∨ x ⊑ {2,3})

the `fun x => x ⊑ {1,2} ∨ x ⊑ {2,3}` filter pass only {} and {2}
then `CompleteLattice.sup` unions {} and {2} together
-------- fun z => z = x ∨ z = y will return
-- noncomputable def meet (x y : α) : α := inf (fun z => z = x ∨ z = y)
--
-- @[inherit_doc meet]
-- scoped infixl:70 " ⊓ " => meet

/-- A complete lattice whose meets preserve suprema. The Heyting implication `⇨` is then a right
adjoint, and `⊓` distributes over suprema of arbitrary families. The literature also calls such a
lattice a frame. -/
abbrev Heyting (α : Type u) [CompleteLattice α] : Prop := ∀ a : α, PreservesSup (meet a)

/-- Heyting implication: the upper adjoint of the lattice meet. For `Prop` it is `→`. -/
noncomputable def himp {α : Type u} [CompleteLattice α] (a b : α) : α :=
  PreservesSup.upperAdjoint (meet a) b

@[inherit_doc himp] scoped infixr:60 " ⇨ " => himp

/-- Unit for `⇨`, the meet specialization of `PreservesSup.le_upperAdjoint`: `a ⊓ x ⊑ b → x ⊑ a ⇨ b`. -/
theorem le_himp {a b x : α} (h : a ⊓ x ⊑ b) : x ⊑ a ⇨ b := by
  sorry

/-- Counit for `⇨`, the meet specialization of `PreservesSup.upperAdjoint_le`: `a ⊓ (a ⇨ b) ⊑ b`. -/
theorem meet_himp_le {a b : α} [PreservesSup (meet a)] : a ⊓ (a ⇨ b) ⊑ b := by
  sorry

@[simp] theorem himp_prop_eq_imp (a b : Prop) : ((a ⇨ b : Prop) = (a → b)) := by
  apply propext
  sorry

/-- Pointwise characterization of Heyting implication on function lattices. -/
@[simp] theorem himp_apply
    {σ : Type v} {β : Type u} [CompleteLattice β]
    (a b : σ → β) (s : σ) :
    (a ⇨ b) s = (a s ⇨ b s) := by
  classical
  sorry

end Basic

/-! ## Derived laws -/

section Derived

set_option linter.unusedSectionVars false

variable {l : Type u} [CompleteLattice l] {P P' Q Q' R R' T : l} {φ φ₁ φ₂ : Prop}
-- variable [∀ a : l, PreservesSup (meet a)]
variable [Heyting l]

/-- `⊤ ⊑ (P ⇨ Q)` iff `P ⊑ Q`. -/
@[simp] theorem top_le_himp_iff {l : Type u} [CompleteLattice l]
    --[∀ a : l, PreservesSup (meet a)] (P Q : l) :
    [Heyting l] (P Q : l) :
    ((⊤ : l) ⊑ P ⇨ Q) ↔ (P ⊑ Q) :=
  ⟨fun h => rel_trans
