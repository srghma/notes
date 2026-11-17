```lean
import Mathlib

-- 1. Define the type: Vector of length 2 of Booleans
abbrev BoolVec2 := Fin 2 → Bool

-- 2. Prove/check that its cardinality is 4 (2^2)
#eval Fintype.card BoolVec2  -- Outputs: 4

-- 3. Get the finite set (or list) containing all variants
def allBoolVecs2 : Finset BoolVec2 := Finset.univ

#check Fintype.elems

#eval (0 : Fin 2)
#eval (1 : Fin 2)
#eval (2 : Fin 2)
#eval (3 : Fin 2)
#eval (4 : Fin 2)

-- 4. Convert it to a List/Vector if needed
noncomputable def allBoolVecs2List : List BoolVec2 := Finset.univ.toList -- depends Quot.ind + Classical.choose
```


so can write like `def all: List := ...` then proove that its correct Fintype
