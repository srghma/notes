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

direction -> : if x is more than s (not possible, can only be equal. right?)
   then such x should be more than all other elements of collection

     Example: let collection be {2,4,6} over N (from 0 to inf)
     - proposed supremum is inf:
        does it give `s ⊑ x → (∀ y, c y → y ⊑ x)`? s inf , x inf, YES
        does it give `(∀ y, c y → y ⊑ x) → s ⊑ x`? NO, counterexample is 6 or 7
     - proposed supremum is 2:
        does it give `s ⊑ x → (∀ y, c y → y ⊑ x)`? NO (x is 2 breaks, how about 1? 0?)
        does it give `(∀ y, c y → y ⊑ x) → s ⊑ x`? YES
     - proposed supremum is 4:
        does it give `s ⊑ x → (∀ y, c y → y ⊑ x)`? NO (x is 2 or 4 breaks)
        does it give `(∀ y, c y → y ⊑ x) → s ⊑ x`? YES
     - proposed supremum is 6:
        does it give `s ⊑ x → (∀ y, c y → y ⊑ x)`? YES
        does it give `(∀ y, c y → y ⊑ x) → s ⊑ x`? YES


    Compare Nat, Rat, and Real in lean (ConditionallyCompleteLinearOrderBot):
      Every bounded nonempty subset has a supremum?
      Nat - yes (though unbounded - no, inf doesnt exist)
      Rat - no (bc from 0 to square root of 2 - the sepremum is not in Rat, its in Real)
      Rat - yes (bc from 0 to square root of 2 - the sepremum is in Real)

-- namespace PartialOrder
-- @[expose] def is_sup {α : Sort u} [PartialOrder α] (c : α → Prop) (s : α) : Prop :=
--   ∀ x, s ⊑ x ↔ (∀ y, c y → y ⊑ x)
-- /--
-- `is_meet x y w` states that `w` is a greatest lower bound of `x` and `y`.
--
-- This is intended to be used in the construction of the strong induction principles of
-- `inductive_fixpoint` and `coinductive_fixpoint`, and not meant to be used otherwise.
-- -/
-- @[expose] def is_meet (x y w : α) : Prop :=
--   w ⊑ x ∧ w ⊑ y ∧ ∀ z, z ⊑ x → z ⊑ y → z ⊑ w
-- end PartialOrder

-- class CompleteLattice (α : Sort u) extends PartialOrder α where
--   /--
--   The least upper bound of an arbitrary subset exists.
--   -/
--   has_sup (c : α → Prop) : Exists (is_sup c)

-- noncomputable def CompleteLattice.sup (c : α → Prop) : α :=
--   Classical.choose (CompleteLattice.has_sup c)

variable {α : Type u} [CompleteLattice α]

-- class PreservesSup {α : Type u} [CompleteLattice α] (f : α → α) : Prop where
--   /-- `f` preserves joins. -/
--   map_sup (s : α → Prop) :
--     f (CompleteLattice.sup s) = CompleteLattice.sup (fun y => ∃ x, s x ∧ y = f x)

-- /-- Binary meet (infimum) -/
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
