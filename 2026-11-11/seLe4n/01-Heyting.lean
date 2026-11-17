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

variable {α : Type u} [CompleteLattice α]

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
  ...

/-- Counit for `⇨`, the meet specialization of `PreservesSup.upperAdjoint_le`: `a ⊓ (a ⇨ b) ⊑ b`. -/
theorem meet_himp_le {a b : α} [PreservesSup (meet a)] : a ⊓ (a ⇨ b) ⊑ b := by
  ...

@[simp] theorem himp_prop_eq_imp (a b : Prop) : ((a ⇨ b : Prop) = (a → b)) := by
  apply propext
  ...

/-- Pointwise characterization of Heyting implication on function lattices. -/
@[simp] theorem himp_apply
    {σ : Type v} {β : Type u} [CompleteLattice β]
    (a b : σ → β) (s : σ) :
    (a ⇨ b) s = (a s ⇨ b s) := by
  classical
  ...

end Basic

/-! ## Derived laws -/

section Derived

set_option linter.unusedSectionVars false

variable {l : Type u} [CompleteLattice l] {P P' Q Q' R R' T : l} {φ φ₁ φ₂ : Prop}
-variable [∀ a : l, PreservesSup (meet a)]
+variable [Heyting l]

...
/-- `⊤ ⊑ (P ⇨ Q)` iff `P ⊑ Q`. -/
@[simp] theorem top_le_himp_iff {l : Type u} [CompleteLattice l]
    -[∀ a : l, PreservesSup (meet a)] (P Q : l) :
    +[Heyting l] (P Q : l) :
    ((⊤ : l) ⊑ P ⇨ Q) ↔ (P ⊑ Q) :=
  ⟨fun h => rel_trans
