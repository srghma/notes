---- If you give Quot a relation r that isn't symmetric or transitive, Quot will force it to become symmetric and transitive anyway!
-- A simple Directed Graph with 4 nodes
inductive Node
  | A
  | B
  | C
  | Isolated  -- Node with no edges

-- Directed Edges: A -> B and B -> C
inductive Edge : Node → Node → Prop
  | ab : Edge .A .B
  | bc : Edge .B .C

-- ----------------------------------------------------
-- Proof that Edge is NOT an Equivalence Relation:
-- 1. Not Reflexive: No (Edge .A .A)
-- 2. Not Symmetric: (Edge .A .B) exists, but (Edge .B .A) does not
-- 3. Not Transitive: (Edge .A .B) and (Edge .B .C) exist, but no direct (Edge .A .C)
-- ----------------------------------------------------

-- We can STILL use `Quot` directly on `Edge`!
def ConnectedComponent := Quot Edge

-- 1. A = B because of direct edge
theorem a_eq_b : Quot.mk Edge Node.A = Quot.mk Edge Node.B :=
  Quot.sound Edge.ab

-- 2. B = C because of direct edge
theorem b_eq_c : Quot.mk Edge Node.B = Quot.mk Edge Node.C :=
  Quot.sound Edge.bc

-- 3. A = C because `Quot` AUTOMATICALLY handles Transitivity!
theorem a_eq_c : Quot.mk Edge Node.A = Quot.mk Edge Node.C := by
  rw [a_eq_b, b_eq_c]

-- 4. B = A because `Quot` AUTOMATICALLY handles Symmetry!
theorem b_eq_a : Quot.mk Edge Node.B = Quot.mk Edge Node.A := by
  rw [a_eq_b]
