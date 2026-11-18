Heyting's key property is $a \sqcap \bigvee_i b_i = \bigvee_i(a\sqcap b_i).$

```lean
-- mathlib
theorem map_iSup
  {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Sort u_6}
  [FunLike F α β] [SupSet α] [SupSet β] [sSupHomClass F α β]
  (f : F) (g : ι → α) :
  f (⨆ (i : ι), g i) = ⨆ (i : ι), f (g i)
```

This is equivalent to the existence of a right adjoint to mee


```lean
theorem le_himp_iff {α : Type u_2} [GeneralizedHeytingAlgebra α] {a b c : α} : a ≤ b ⇨ c ↔ a ⊓ b ≤ c -- p → q → r ↔ p ∧ q → r
```

```lean
theorem himp_eq_sSup : a ⇨ b = sSup {w : α | w ⊓ a ≤ b} -- b⇒c=⋁{x∣x∧b≤c} -- himp_eq_sSup
```
