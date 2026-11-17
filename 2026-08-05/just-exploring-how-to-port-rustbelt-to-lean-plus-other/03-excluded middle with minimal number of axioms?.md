```lean
/-!
# Excluded middle from choice + quotients, without `funext`
This file completes the development sketched by the user: a Diaconescu-style
derivation of the law of excluded middle from `Classical.choice` (used through
`Classical.indefiniteDescription`) together with quotient types (`Quot.sound`).
The final theorem `EMQuot.em_via_quotient` depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`; in particular **`funext` is not
used**.  `propext` is still needed: it is what makes the map `test` below
respect the relation `boolRel p`, since `Quot.lift` into `Prop` requires an
*equality* of propositions.
-/
namespace EMQuot
/-- 1. Relation on `Bool` parameterized by `p`: it is equality, collapsed to the
total relation as soon as `p` holds. -/
def boolRel (p : Prop) (b1 b2 : Bool) : Prop :=
  b1 = b2 ∨ p
/-- 2. Quotient type over `Bool`. -/
def BoolQuot (p : Prop) : Type :=
  Quot (boolRel p)
/-- 3. Constructors for quotient terms. -/
def qFalse (p : Prop) : BoolQuot p := Quot.mk (boolRel p) false
/-- 3. Constructors for quotient terms. -/
def qTrue (p : Prop) : BoolQuot p := Quot.mk (boolRel p) true
/-- 4. Non-constructive representative extraction via
`Classical.indefiniteDescription`. -/
noncomputable def out {p : Prop} (q : BoolQuot p) : Bool :=
  (Classical.indefiniteDescription _ (Quot.exists_rep q)).val
theorem out_spec {p : Prop} (q : BoolQuot p) : Quot.mk (boolRel p) (out q) = q :=
  (Classical.indefiniteDescription _ (Quot.exists_rep q)).property
/-- 5. Main theorem: excluded middle from choice + quotients, without `funext`. -/
theorem em_via_quotient (p : Prop) : p ∨ ¬p := by
  let f_out := out (qFalse p)
  let t_out := out (qTrue p)
  if h_eq : f_out = t_out then
    -- Branch 1: the extracted representatives are equal.
    -- Then `qFalse p = qTrue p`, and lifting a predicate extracts `p`.
    have h_q_eq : qFalse p = qTrue p := by
      have h1 : qFalse p = Quot.mk (boolRel p) f_out := (out_spec (qFalse p)).symm
      have h2 : qTrue p = Quot.mk (boolRel p) t_out := (out_spec (qTrue p)).symm
      rw [h1, h2, h_eq]
    -- A predicate mapping `Bool` to `Prop` that evaluates to `p` on `true`.
    let test (b : Bool) : Prop := if b = true then p else True
    have test_respects : ∀ b1 b2, boolRel p b1 b2 → (test b1 = test b2) := by
      intro b1 b2 hrel
      cases hrel with
      | inl h_eq_bool => rw [h_eq_bool]
      | inr hp => cases b1 <;> cases b2 <;> simp [test, hp]
    let testQuot : BoolQuot p → Prop := Quot.lift test test_respects
    have h_eval_f : testQuot (qFalse p) = True := rfl
    have h_eval_t : testQuot (qTrue p) = p := rfl
    have h_p_eq_true : p = True := by
      calc p = testQuot (qTrue p) := h_eval_t.symm
        _ = testQuot (qFalse p) := by rw [← h_q_eq]
        _ = True := h_eval_f
    exact Or.inl (h_p_eq_true ▸ trivial)
  else
    -- Branch 2: the extracted representatives differ.
    -- If `p` held, the relation would be total, so `qFalse p = qTrue p` and
    -- hence the representatives would agree — contradiction.
    refine Or.inr (fun hp => h_eq ?_)
    exact congrArg out (Quot.sound (Or.inr hp) : qFalse p = qTrue p)
-- Axiom audit: `propext`, `Classical.choice`, `Quot.sound`.  No `funext`.
#print axioms em_via_quotient
end EMQuot
```


```lean
/-!
# Excluded middle from the smallest axiom set we could achieve: `Classical.choice` + `propext`
The file `EMViaQuotient.lean` derives excluded middle from
`Classical.choice`, `Quot.sound` and `propext` (no `funext`; recall that in Lean 4
`funext` is *not* an axiom — it is a theorem whose only axiom is `Quot.sound`).
Here we push further and remove `Quot.sound` as well: the theorem
`EMMin.em_two_axioms` below depends on exactly two axioms,
```
[propext, Classical.choice]
```
so it uses neither `Quot.sound` nor (a fortiori) `funext`.
## The idea
The usual Diaconescu argument chooses elements from the two subsets
`U = {b : Bool | b = false ∨ p}` and `V = {b : Bool | b = true ∨ p}` of `Bool`,
and proves `U = V` from `p` by `funext` + `propext`.  We avoid `funext` by
*presenting a subset of `Bool` by its two membership propositions*: the pair
`(q₀, q₁)` denotes `{b | if b then q₀ else q₁}`.  With this presentation `U` is
the pair `(p, True)` and `V` is the pair `(True, p)`, and once `propext` turns
`p` into `True` the two pairs are literally the same *arguments* of the same
function `Sub`, so `congrArg`/`subst` suffices — no function extensionality is
needed anywhere, and no quotients are involved.
Choice is applied through `Classical.choice`, whose argument is a `Nonempty`
proof; since `Prop` is definitionally proof irrelevant, the chosen element
depends only on the type, which is exactly what makes the argument work.
-/
namespace EMMin
/-- Membership predicate of the "subset of `Bool`" presented by the pair of
propositions `(q₀, q₁)`: `true` belongs to it iff `q₀`, and `false` belongs to
it iff `q₁`. -/
def Mem (q₀ q₁ : Prop) (b : Bool) : Prop := cond b q₀ q₁
/-- The subtype of `Bool` cut out by the pair of propositions `(q₀, q₁)`. -/
def Sub (q₀ q₁ : Prop) : Type := {b : Bool // Mem q₀ q₁ b}
/-- Choice: pick an element of `Sub q₀ q₁` out of a `Nonempty` proof, and return
its underlying boolean.  Because `Nonempty` is a proof-irrelevant `Prop`, the
result depends only on the propositions `q₀` and `q₁`. -/
noncomputable def pick (q₀ q₁ : Prop) (h : Nonempty (Sub q₀ q₁)) : Bool :=
  (Classical.choice h).val
theorem pick_mem (q₀ q₁ : Prop) (h : Nonempty (Sub q₀ q₁)) : Mem q₀ q₁ (pick q₀ q₁ h) :=
  (Classical.choice h).property
/-- `{b | b = false ∨ p}` in pair presentation: it always contains `false`. -/
theorem nonempty_left (p : Prop) : Nonempty (Sub p True) := ⟨⟨false, trivial⟩⟩
/-- `{b | b = true ∨ p}` in pair presentation: it always contains `true`. -/
theorem nonempty_right (p : Prop) : Nonempty (Sub True p) := ⟨⟨true, trivial⟩⟩
/-- The chosen element of the "left" subset. -/
noncomputable def u (p : Prop) : Bool := pick p True (nonempty_left p)
/-- The chosen element of the "right" subset. -/
noncomputable def v (p : Prop) : Bool := pick True p (nonempty_right p)
/-- Easy direction (uses only `Classical.choice`): the witnesses can only agree
if `p` holds. -/
theorem p_or_ne (p : Prop) : p ∨ u p ≠ v p := by
  have hu : Mem p True (u p) := pick_mem p True (nonempty_left p)
  have hv : Mem True p (v p) := pick_mem True p (nonempty_right p)
  revert hu hv
  cases hcu : u p <;> cases hcv : v p <;> intro hu hv
  · exact Or.inl hv          -- `u = false`, `v = false`: `v`'s membership is `p`
  · exact Or.inr Bool.noConfusion
  · exact Or.inl hu          -- `u = true`: `u`'s membership is `p`
  · exact Or.inl hu
/-- Hard direction (uses `propext`): if `p` holds then both subsets are the pair
`(True, True)`, hence the very same type, hence choice returns the same
element. -/
theorem eq_of_p (p : Prop) (hp : p) : u p = v p := by
  have hpt : p = True := propext ⟨fun _ => trivial, fun _ => hp⟩
  subst hpt
  rfl
/-- **Excluded middle from two axioms**: `Classical.choice` and `propext`.
In particular neither `Quot.sound` nor `funext` is used. -/
theorem em_two_axioms (p : Prop) : p ∨ ¬p :=
  if h : u p = v p then
    Or.inl ((p_or_ne p).resolve_right fun hne => hne h)
  else
    Or.inr fun hp => h (eq_of_p p hp)
-- Axiom audit: `[propext, Classical.choice]`.
#print axioms em_two_axioms
end EMMin
```
