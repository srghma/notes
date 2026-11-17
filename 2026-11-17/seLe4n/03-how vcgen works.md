```lean
-- https://leanprover-community.github.io/mathlib4_docs/Std/WP/Triple/Basic.html#Std.WP.Triple
-- https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/Std/WP/Triple/Basic.lean#L35-L42
structure Triple {Pred : Type w} {EPosts : Type w'} {Prog : Type u} {Value : Type v} [Assertion Pred] [Assertion EPosts] (x : Prog) [WP Prog Value Pred EPosts] (pre : Pred) (post : Value → Pred) (eposts : EPosts) : Prop where
  intro ::
  le_wp : pre ⊑ wp x post eposts
```

```lean
-- https://github.com/sgraf812/kraken/blob/829c9468974ea0f725abc268baa6dbb9403ccd36/Kraken/X64/Examples/P3.lean#L85-L95
theorem p3_correct (d : MachineData) (h_bounds : p3_spec d < 2 ^ 64)
    (h_rax : d.regs.rax = 0) :
    ⦃ fun s => s = d ⦄
      p3
    ⦃ fun _ s => s.regs.rdx.toNat = p3_spec d ∧ s.regs.rax = 0 ⦄ := by
  simp only [p3_spec] at h_bounds ⊢
  apply MachineWP.cfg (p3_table d) (fun _ s => s.regs.rbx.toNat)
  cfg_cases [p3]
  · vcgen with finish
  · vcgen with finish
  · vcgen with finish
```
