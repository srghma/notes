```lean
-- ## 1. Impredicative Booleans (Bool)

def CBool : Prop := ∀ (A : Prop), A → A → A

theorem cTrue : CBool := fun (A : Prop) (t : A) (f : A) => t

theorem cFalse : CBool := fun (A : Prop) (t : A) (f : A) => f

theorem cNot (b : CBool) : CBool := b CBool cFalse cTrue

-- ## 2. Impredicative Natural Numbers (Nat)

def CNat : Prop := ∀ (A : Prop), (A → A) → A → A

theorem cZero : CNat := fun (A : Prop) (f : A → A) (x : A) => x

theorem cOne : CNat := fun (A : Prop) (f : A → A) (x : A) => f x

theorem cSucc (n : CNat) : CNat :=
  fun (A : Prop) (f : A → A) (x : A) => f (n A f x)

-- With impredicativity in Prop, the system folds in on itself

```
