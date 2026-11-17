```lean
-- 1. Declare the Person structure
structure Person where
  name   : String
  height : Nat  -- height in centimeters, for example

-- 2. Define the IsTallest predicate
def IsTallest (x : Person) : Prop := ∀ (p : Person), x.height ≥ p.height

-- Create two instance persons
def Alice : Person := { name := "Alice", height := 180 }
def Bob   : Person := { name := "Bob",   height := 170 }

-- 'IsTallest Alice' is now a proposition (Prop)
#check IsTallest Alice
-- Output: IsTallest Alice : Prop

-- If we assume the universe of people consists only of Alice and Bob:
theorem alice_is_tallest (h : ∀ p : Person, p = Alice ∨ p = Bob) : IsTallest Alice := by
  intro p
  rcases h p with rfl | rfl
  · -- Case p = Alice
    exact Nat.le_refl 180
  · -- Case p = Bob
    exact Nat.le_of_lt (by decide)

```
