import Std.Internal.Order.Heyting
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Rat.Init
import Mathlib.Tactic

section Equivalence

/-- Every Mathlib `CompleteLattice` gives a `Lean.Order.CompleteLattice` with the same order. -/
@[instance_reducible]
noncomputable def completeLatticeToLeanCompleteLattice (α : Type u) [CompleteLattice α] :
    Lean.Order.CompleteLattice α where
  rel := (· ≤ ·)
  rel_refl := fun {x} => le_refl x
  rel_trans := fun h₁ h₂ => le_trans h₁ h₂
  rel_antisymm := fun h₁ h₂ => le_antisymm h₁ h₂
  has_sup c :=
    ⟨sSup {y | c y}, fun _ => ⟨fun h _ hy => (le_sSup hy).trans h, fun h => sSup_le h⟩⟩

/-- Every Mathlib `Order.Frame` gives a `Lean.Order.CompleteLattice` with the same order. -/
@[instance_reducible]
noncomputable def frameToLeanCompleteLattice (α : Type u) [Order.Frame α] :
    Lean.Order.CompleteLattice α :=
  completeLatticeToLeanCompleteLattice α

private lemma completeLattice_sup_eq_sSup {α : Type u} [CompleteLattice α] (s : α → Prop) :
    @Lean.Order.CompleteLattice.sup α (completeLatticeToLeanCompleteLattice α) s =
      sSup {y | s y} := by
  apply le_antisymm
  · apply @Lean.Order.sup_le α (completeLatticeToLeanCompleteLattice α)
    intro _ hy
    exact le_sSup hy
  · apply sSup_le
    intro y hy
    exact @Lean.Order.le_sup α (completeLatticeToLeanCompleteLattice α) s y hy

private lemma completeLattice_meet_eq_inf {α : Type u} [CompleteLattice α] (a b : α) :
    @Lean.Order.meet α (completeLatticeToLeanCompleteLattice α) a b = a ⊓ b := by
  dsimp [Lean.Order.meet, Lean.Order.inf]
  apply le_antisymm
  · apply @Lean.Order.sup_le α (completeLatticeToLeanCompleteLattice α)
    intro _ hw
    exact le_inf (hw a (Or.inl rfl)) (hw b (Or.inr rfl))
  · apply @Lean.Order.le_sup α (completeLatticeToLeanCompleteLattice α)
    intro _ hz
    exact hz.elim (fun h => h ▸ inf_le_left) (fun h => h ▸ inf_le_right)

/-- Direction 1: Every Mathlib `Order.Frame` satisfies `Lean.Order.Heyting`. -/
theorem frame_to_leanHeyting (α : Type u) [Order.Frame α] :
    @Lean.Order.Heyting α (frameToLeanCompleteLattice α) := by
  intro a
  refine @Lean.Order.PreservesSup.mk α (frameToLeanCompleteLattice α) _ fun s => ?_
  simp only [completeLattice_meet_eq_inf, completeLattice_sup_eq_sSup]
  apply le_antisymm
  · rw [inf_comm]
    refine le_himp_iff.mp (sSup_le fun x hx => le_himp_iff.mpr ?_)
    rw [inf_comm]
    exact le_sSup ⟨x, hx, rfl⟩
  · apply sSup_le
    rintro y ⟨x, hx, rfl⟩
    exact le_inf inf_le_left (inf_le_right.trans (le_sSup hx))

/-- Direction 2: Every `Lean.Order.CompleteLattice` + `Lean.Order.Heyting` forms an `Order.Frame`. -/
@[instance_reducible]
noncomputable def leanHeytingToFrame (α : Type u) [inst : Lean.Order.CompleteLattice α]
    (H : Lean.Order.Heyting α) : Order.Frame α :=
  letI : PartialOrder α :=
    { le := Lean.Order.PartialOrder.rel
      le_refl := fun _ => Lean.Order.PartialOrder.rel_refl
      le_trans := fun _ _ _ => Lean.Order.PartialOrder.rel_trans
      le_antisymm := fun _ _ => Lean.Order.PartialOrder.rel_antisymm }
  letI : CompleteLattice α :=
    { sup := fun a b => Lean.Order.CompleteLattice.sup (fun z => z = a ∨ z = b)
      le_sup_left := fun _ _ => Lean.Order.le_sup _ (Or.inl rfl)
      le_sup_right := fun _ _ => Lean.Order.le_sup _ (Or.inr rfl)
      sup_le := fun _ _ _ ha hb => Lean.Order.sup_le _ fun _ hy => hy.elim (· ▸ ha) (· ▸ hb)
      inf := Lean.Order.meet
      inf_le_left := fun a _ => Lean.Order.sup_le _ fun _ hw => hw a (Or.inl rfl)
      inf_le_right := fun _ b => Lean.Order.sup_le _ fun _ hw => hw b (Or.inr rfl)
      le_inf := fun _ _ _ ha hb => Lean.Order.le_sup _ fun _ hz => hz.elim (· ▸ ha) (· ▸ hb)
      sSup := fun s => Lean.Order.CompleteLattice.sup (· ∈ s)
      isLUB_sSup := fun s =>
        ⟨fun _ ha => Lean.Order.le_sup (· ∈ s) ha,
         fun _ ha => Lean.Order.sup_le (· ∈ s) fun _ hy => ha hy⟩
      sInf := fun s => Lean.Order.inf (· ∈ s)
      isGLB_sInf := fun s =>
        ⟨fun _ ha =>
          Lean.Order.sup_le (fun x => ∀ y, y ∈ s → Lean.Order.PartialOrder.rel x y)
            fun _ hw => hw _ ha,
         fun _ ha =>
          Lean.Order.le_sup (fun x => ∀ y, y ∈ s → Lean.Order.PartialOrder.rel x y)
            fun _ hy => ha hy⟩
      top := Lean.Order.CompleteLattice.sup (fun _ => True)
      le_top := fun _ => Lean.Order.le_sup _ trivial
      bot := Lean.Order.CompleteLattice.sup (fun _ => False)
      bot_le := fun _ => Lean.Order.sup_le _ fun _ h => False.elim h }
  { toCompleteLattice := inferInstance
    himp := Lean.Order.himp
    compl := fun a => Lean.Order.himp a ⊥
    himp_bot := fun _ => rfl
    le_himp_iff := fun a b c => by
      have := H b
      constructor
      · intro h
        have h1 : a ⊓ b ≤ b ⊓ a := le_inf inf_le_right inf_le_left
        have h2 : b ⊓ a ≤ b ⊓ Lean.Order.himp b c := le_inf inf_le_left (inf_le_right.trans h)
        exact h1.trans (h2.trans Lean.Order.meet_himp_le)
      · intro h
        exact Lean.Order.le_himp_of_meet_le_left ((le_inf inf_le_right inf_le_left).trans h) }

/-- Over a fixed Mathlib `CompleteLattice α`, `Lean.Order.Heyting` is equivalent to
    `Order.Frame.MinimalAxioms` (which recovers `Order.Frame α` via `Order.Frame.ofMinimalAxioms`). -/
def leanHeytingEquivFrameMinimalAxioms (α : Type u) [CompleteLattice α] :
    @Lean.Order.Heyting α (completeLatticeToLeanCompleteLattice α) ≃
      Order.Frame.MinimalAxioms α where
  toFun H := by
    refine ⟨fun a s => ?_⟩
    have hsup := (H a).map_sup (· ∈ s)
    simp only [completeLattice_meet_eq_inf, completeLattice_sup_eq_sSup] at hsup
    exact hsup.le.trans (sSup_le (by
      rintro y ⟨b, hb, rfl⟩
      exact (le_iSup (fun (_ : b ∈ s) => a ⊓ b) hb).trans
        (le_iSup (fun b => ⨆ (_ : b ∈ s), a ⊓ b) b)))
  invFun m := @frame_to_leanHeyting α (Order.Frame.ofMinimalAxioms m)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A `Lean.Order.CompleteLattice` bundled with `Lean.Order.Heyting`. -/
structure LeanHeyting (α : Type u) where
  completeLattice : Lean.Order.CompleteLattice α
  heyting : @Lean.Order.Heyting α completeLattice

/-- Two `LeanHeyting` structures are order-equivalent when they induce the same `≤`. -/
def LeanHeyting.OrderSetoid (α : Type u) : Setoid (LeanHeyting α) where
  r x y := ∀ a b, x.completeLattice.rel a b ↔ y.completeLattice.rel a b
  iseqv :=
    { refl := fun _ _ _ => Iff.rfl
      symm := fun h a b => (h a b).symm
      trans := fun h₁ h₂ a b => (h₁ a b).trans (h₂ a b) }

/-- Two Mathlib `Order.Frame` structures are order-equivalent when they induce the same `≤`. -/
def FrameOrderSetoid (α : Type u) : Setoid (Order.Frame α) where
  r F₁ F₂ := ∀ a b, F₁.le a b ↔ F₂.le a b
  iseqv :=
    { refl := fun _ _ _ => Iff.rfl
      symm := fun h a b => (h a b).symm
      trans := fun h₁ h₂ a b => (h₁ a b).trans (h₂ a b) }

/-- Type-level equivalence between `(Lean.Order.CompleteLattice + Lean.Order.Heyting)`
    and Mathlib's `Order.Frame`, up to having the same underlying order `≤`. -/
noncomputable def leanHeytingOrderEquivFrame (α : Type u) :
    Quotient (LeanHeyting.OrderSetoid α) ≃ Quotient (FrameOrderSetoid α) where
  toFun := Quotient.lift
    (fun x => Quotient.mk _ (@leanHeytingToFrame α x.completeLattice x.heyting))
    (fun _ _ h => Quotient.sound h)
  invFun := Quotient.lift
    (fun F => Quotient.mk _
      ⟨@frameToLeanCompleteLattice α F, @frame_to_leanHeyting α F⟩)
    (fun _ _ h => Quotient.sound h)
  left_inv := Quotient.ind fun _ => Quotient.sound fun _ _ => Iff.rfl
  right_inv := Quotient.ind fun _ => Quotient.sound fun _ _ => Iff.rfl

/-- Over a fixed `PartialOrder α`, having a compatible `Lean.Order.CompleteLattice` with
    `Lean.Order.Heyting` is equivalent to having a compatible Mathlib `Order.Frame`. -/
def existsLeanHeytingEquivExistsFrame (α : Type u) [PartialOrder α] :
    (∃ C : Lean.Order.CompleteLattice α,
      (∀ x y, C.rel x y ↔ x ≤ y) ∧ @Lean.Order.Heyting α C) ≃
    (∃ F : Order.Frame α, ∀ x y, F.le x y ↔ x ≤ y) where
  toFun := fun ⟨C, hrel, H⟩ => ⟨@leanHeytingToFrame α C H, hrel⟩
  invFun := fun ⟨F, hord⟩ => ⟨@frameToLeanCompleteLattice α F, hord, @frame_to_leanHeyting α F⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Equivalence

section Counterexample

/-- `WithTop (WithBot ℚ)` is a bounded linear order, hence a `HeytingAlgebra`. -/
abbrev QBound := WithTop (WithBot ℚ)

@[instance_reducible]
noncomputable def qBoundHeytingAlgebra : HeytingAlgebra QBound :=
  (LinearOrder.toBiheytingAlgebra QBound).toHeytingAlgebra

theorem qBound_is_heytingAlgebra : Nonempty (HeytingAlgebra QBound) :=
  ⟨qBoundHeytingAlgebra⟩

private def qEmbed (q : ℚ) : QBound := ((q : WithBot ℚ) : QBound)

@[simp] private lemma qEmbed_le_iff {p q : ℚ} : qEmbed p ≤ qEmbed q ↔ p ≤ q := by
  simp [qEmbed]

@[simp] private lemma qEmbed_lt_iff {p q : ℚ} : qEmbed p < qEmbed q ↔ p < q := by
  simp [qEmbed]

private lemma rat_mul_self_ne_two (r : ℚ) : r * r ≠ 2 := by
  intro h
  have hq : ((r.num : ℚ) / r.den) * ((r.num : ℚ) / r.den) = 2 := by
    simpa [Rat.num_div_den] using h
  have hd : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  have hq' : (r.num : ℚ) ^ 2 = 2 * (r.den : ℚ) ^ 2 := by
    field_simp at hq
    linarith
  have hz : r.num ^ 2 = 2 * (r.den : ℤ) ^ 2 := by exact_mod_cast hq'
  have hn : r.num.natAbs ^ 2 = 2 * r.den ^ 2 := by
    have h1 : ((r.num.natAbs ^ 2 : ℕ) : ℤ) = ((2 * r.den ^ 2 : ℕ) : ℤ) := by
      rw [Nat.cast_pow, Int.natAbs_sq, hz]
      norm_cast
    exact Int.ofNat.inj h1
  have two_dvd_sq : ∀ n : ℕ, 2 ∣ n ^ 2 → 2 ∣ n := by
    intro n hdiv
    rcases Nat.mod_two_eq_zero_or_one n with hm | hm
    · exact Nat.dvd_of_mod_eq_zero hm
    · exfalso
      have hk : n = 2 * (n / 2) + 1 := by omega
      have hsq : n ^ 2 = 2 * (2 * (n / 2) ^ 2 + 2 * (n / 2)) + 1 := by
        calc n ^ 2 = (2 * (n / 2) + 1) ^ 2 := by rw [← hk]
          _ = 2 * (2 * (n / 2) ^ 2 + 2 * (n / 2)) + 1 := by ring
      omega
  have h2n : 2 ∣ r.num.natAbs := two_dvd_sq r.num.natAbs ⟨r.den ^ 2, hn⟩
  obtain ⟨k, hk⟩ := h2n
  have hm : r.den ^ 2 = 2 * k ^ 2 := by
    rw [hk] at hn
    linarith
  have h2m : 2 ∣ r.den := two_dvd_sq r.den ⟨k ^ 2, hm⟩
  have hgcd : 2 ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd ⟨k, hk⟩ h2m
  rw [r.reduced] at hgcd
  omega

/-- `WithTop (WithBot ℚ)` has NO `Lean.Order.CompleteLattice` agreeing with `≤`
    (hence no `Lean.Order.Heyting` either). -/
theorem qBound_not_leanCompleteLattice
    (C : Lean.Order.CompleteLattice QBound)
    (hrel : ∀ x y : QBound, C.rel x y ↔ x ≤ y) : False := by
  let s : QBound → Prop := fun x => ∃ q : ℚ, x = qEmbed q ∧ q * q < 2
  let u : QBound := @Lean.Order.CompleteLattice.sup QBound C s
  have hub : ∀ q : ℚ, q * q < 2 → qEmbed q ≤ u := fun q hq =>
    (hrel _ _).mp (@Lean.Order.le_sup QBound C s (qEmbed q) ⟨q, rfl, hq⟩)
  have hlub : ∀ b : QBound, (∀ y, s y → y ≤ b) → u ≤ b := fun b hb =>
    (hrel _ _).mp (@Lean.Order.sup_le QBound C b s fun y hy => (hrel _ _).mpr (hb y hy))
  have h1u : qEmbed 1 ≤ u := hub 1 (by norm_num)
  have hu_le_2 : u ≤ qEmbed 2 := by
    apply hlub
    rintro y ⟨q, rfl, hq⟩
    rw [qEmbed_le_iff]
    nlinarith
  have hu_ne_top : u ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hu_le_2 (WithTop.coe_lt_top _))
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hu_ne_top
  have hv_ne_bot : v ≠ ⊥ := by
    intro hbot
    rw [hbot] at hv
    have hle : ((1 : ℚ) : WithBot ℚ) ≤ ⊥ := by
      have : (((1 : ℚ) : WithBot ℚ) : QBound) ≤ ((⊥ : WithBot ℚ) : QBound) := by
        simpa [qEmbed, hv] using h1u
      exact WithTop.coe_le_coe.mp this
    exact (not_le_of_gt (WithBot.bot_lt_coe (1 : ℚ))) hle
  obtain ⟨r, hr_eq⟩ := WithBot.ne_bot_iff_exists.mp hv_ne_bot
  have hu_eq : u = qEmbed r := by rw [← hv, ← hr_eq]; rfl
  have hr1 : 1 ≤ r := by
    rw [hu_eq, qEmbed_le_iff] at h1u
    exact h1u
  rcases lt_or_gt_of_ne (rat_mul_self_ne_two r) with hlt | hgt
  · -- If r^2 < 2, we can find a strictly larger rational q with q^2 < 2
    let d : ℚ := (2 - r * r) / (2 * r + 2)
    let q : ℚ := r + d
    have hden : 0 < 2 * r + 2 := by linarith
    have hd_pos : 0 < d := div_pos (by linarith) hden
    have hd_lt_one : d < 1 := by
      rw [div_lt_one hden]
      nlinarith
    have hq_sq : q * q < 2 := by
      have hmul : d * (2 * r + 2) = 2 - r * r := div_mul_cancel₀ _ (ne_of_gt hden)
      have h1 : d * (2 * r + d) < d * (2 * r + 2) := by
        nlinarith
      dsimp [q]
      nlinarith
    have hqr : qEmbed q ≤ qEmbed r := hu_eq ▸ hub q hq_sq
    rw [qEmbed_le_iff] at hqr
    dsimp [q] at hqr
    linarith
  · -- If 2 < r^2, Newton's step q = (r + 2 / r) / 2 is a strictly smaller upper bound
    let q : ℚ := (r + 2 / r) / 2
    have hr_pos : 0 < r := by linarith
    have hq_lt : q < r := by
      have hdiv : 2 / r < r := (div_lt_iff₀ hr_pos).mpr (by nlinarith)
      dsimp [q]
      linarith
    have hq_pos : 0 < q := by
      have : 0 < 2 / r := div_pos (by norm_num) hr_pos
      dsimp [q]
      linarith
    have hq_sq : 2 < q * q := by
      have hr0 : r ≠ 0 := ne_of_gt hr_pos
      have hid : q * q - 2 = ((r * r - 2) / (2 * r)) ^ 2 := by
        dsimp [q]
        field_simp
        ring
      have hsq_pos : 0 < ((r * r - 2) / (2 * r)) ^ 2 := by
        have : 0 < (r * r - 2) / (2 * r) := div_pos (by linarith) (by linarith)
        exact sq_pos_of_pos this
      linarith
    have hq_ub : ∀ y, s y → y ≤ qEmbed q := by
      rintro y ⟨t, rfl, ht⟩
      rw [qEmbed_le_iff]
      by_contra hnot
      have hqt : q < t := lt_of_not_ge hnot
      have : 2 < t * t := by nlinarith
      linarith
    have hr_le_q : qEmbed r ≤ qEmbed q := hu_eq ▸ hlub (qEmbed q) hq_ub
    rw [qEmbed_le_iff] at hr_le_q
    linarith

/-- Consequently, `WithTop (WithBot ℚ)` has NO `Order.Frame` agreeing with its order either. -/
theorem qBound_not_frame (F : Order.Frame QBound)
    (hord : ∀ x y : QBound, F.le x y ↔ x ≤ y) : False :=
  qBound_not_leanCompleteLattice (@frameToLeanCompleteLattice QBound F) hord

end Counterexample

-- We have proved that
-- 1. Lean.Order.Heyting same as Order.Frame
-- and
-- 2. Lean.Order.Heyting is not same as HeytingAlgebra
-- ?
