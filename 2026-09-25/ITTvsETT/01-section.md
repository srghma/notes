Option A: Executable via partial def (Standard way to run general loops)
Lean provides partial def for functions that may not terminate. This bypasses termination checks and can be evaluated directly in the interpreter:
code
Lean
-- Executable directly in Live Lean:
partial def repeatM (f : α → α ⊕ β) (a : α) : β :=
  match f a with
  | Sum.inl a' => repeatM f a'
  | Sum.inr b  => b

-- Example: Halts after 5 steps
def countToFive (n : Nat) : Nat ⊕ String :=
  if n >= 5 then
    Sum.inr s!"Done! Reached {n}."
  else
    Sum.inl (n + 1)

#eval repeatM countToFive 0
-- Output: "Done! Reached 5."
(Note: If you pass an infinite loop to partial def, #eval will run until it hits the runtime step/memory limit).
Option B: The Classical Definition (Mathematical, Noncomputable)
This is how classical logic defines the function theoretically using Classical.em and Classical.choice:
code
Lean
import Mathlib.Data.Sum.Basic

-- Helper: run f for n steps
def stepN (f : α → α ⊕ β) : Nat → α → α ⊕ β
  | 0,     a => f a
  | n + 1, a => match f a with
    | Sum.inl a' => stepN f n a'
    | Sum.inr b  => Sum.inr b

open Classical

noncomputable def repeatMClassical [Nonempty β] (f : α → α ⊕ β) (a : α) : β :=
  -- By Excluded Middle: either it halts eventually, or it doesn't
  if h : ∃ (n : Nat) (b : β), stepN f n a = Sum.inr b then
    -- It halted: extract the result
    h.choose_spec.choose
  else
    -- It looped forever: return an arbitrary element from [Nonempty β]
    Classical.choice ‹Nonempty β›
If you try to run #eval repeatMClassical ..., Lean will reject it with:
code
Text
cannot evaluate code because it depends on 'Classical.choice'
