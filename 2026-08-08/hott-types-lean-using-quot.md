#### 1. Standard Inductive Types = Discrete Spaces / 0-Cell Structures

In traditional type theory, inductive types only allow constructors for **elements** (points). In topology, these correspond to **discrete spaces** or 0-dimensional collections of points:

* **`Bool`** $\approx$ A space consisting of 2 disjoint points ($S^0$).
* **`Nat` ($\mathbb{N}$)** $\approx$ A space with countably infinitely many discrete points.
* **`A + B` (Sum type)** $\approx$ The disjoint union of two spaces $A \sqcup B$.
* **`A × B` (Product type)** $\approx$ The cartesian product space $A \times B$.

Standard inductive types can build trees and discrete structures, but they **cannot** construct continuous spaces with non-trivial loops or higher-dimensional shapes (like a circle or a torus).

---

### 2. Higher Inductive Types (HITs) = CW-Complexes (Cell Complexes)

To build continuous topological spaces, HoTT introduces **Higher Inductive Types (HITs)**. A HIT allows constructors not just for *points*, but also for *paths* (equalities) and *higher paths* (equalities between equalities).

In topology, this is **cell attachment** (building a CW-complex):

| HoTT Constructor Level | Type-Theoretic Construct | Topological Meaning |
| :--- | :--- | :--- |
| **0-Constructors** | Point constructors (`a : A`) | **0-cells** (Vertices / Points) |
| **1-Constructors** | Path constructors (`p : a = b`) | **1-cells** (Edges / Lines) |
| **2-Constructors** | Path-equality constructors (`α : p = q`) | **2-cells** (Faces / Disks) |
| **$n$-Constructors** | Higher path constructors | **$n$-cells** ($n$-dimensional balls) |

---

### Topological Examples Defined as HITs

#### A. The Circle ($S^1$)
Topologically, a circle is constructed by taking a single vertex (0-cell) and gluing a single edge (1-cell) from that vertex back to itself.

In HoTT, $S^1$ is defined as a HIT:
```hoTT
data S¹ : Type where
  base : S¹           -- 0-cell (point)
  loop : base = base  -- 1-cell (loop path)
```

```lean
-- 1. Define a relation on a single point (Unit)
inductive S1Rel : Unit → Unit → Prop where
  | loop : S1Rel () ()

-- 2. Take the quotient (glues () to () along S1Rel)
def S1 : Type := Quot S1Rel

-- 3. Define 'base' and 'loop'
def S1.base : S1 := Quot.mk S1Rel ()

def S1.loop : S1.base = S1.base := Quot.sound S1Rel.loop
```

#### B. The Unit Interval ($I = [0, 1]$)
Topologically, the interval $[0,1]$ consists of two endpoints connected by a path.
```hoTT
data Interval : Type where
  zero : Interval
  one  : Interval
  seg  : zero = one   -- 1-cell connecting the two points
```
*(In HoTT, this space is contractible, matching the topological interval $[0,1]$).*

```lean
-- Raw 0-cells (points)
inductive IntervalRaw : Type where
  | zero : IntervalRaw
  | one  : IntervalRaw

-- Relation for 1-cell (seg)
inductive IntervalRel : IntervalRaw → IntervalRaw → Prop where
  | seg : IntervalRel .zero .one

-- HIT Definition
def Interval : Type := Quot IntervalRel

def Interval.zero : Interval := Quot.mk IntervalRel .zero
def Interval.one  : Interval := Quot.mk IntervalRel .one

-- 1-cell constructor
def Interval.seg : Interval.zero = Interval.one :=
  Quot.sound IntervalRel.seg
```

#### C. The Torus ($T^2 = S^1 \times S^1$)
Topologically, a 2D torus is built from 1 vertex, 2 loops ($p$ and $q$), and 1 face attached via the commutator $p \cdot q = q \cdot p$.
```hoTT
data Torus : Type where
  base : Torus
  p    : base = base                   -- 1-cell
  q    : base = base                   -- 1-cell
  surf : p ⬝ q = q ⬝ p                 -- 2-cell (face)
```

```lean
-- First, define the Circle (S¹) via Quot
inductive S1Rel : Unit → Unit → Prop where
  | loop : S1Rel () ()

def S1 : Type := Quot S1Rel
def S1.base : S1 := Quot.mk S1Rel ()
def S1.loop : S1.base = S1.base := Quot.sound S1Rel.loop

-- Topologically, Torus = S¹ × S¹
def Torus : Type := S1 × S1

def Torus.base : Torus := (S1.base, S1.base)

-- 1-cell 'p' (loop along the first S¹)
def Torus.p : Torus.base = Torus.base :=
  congrArg (fun x => (x, S1.base)) S1.loop

-- 1-cell 'q' (loop along the second S¹)
def Torus.q : Torus.base = Torus.base :=
  congrArg (fun y => (S1.base, y)) S1.loop

-- 2-cell 'surf' : p ⬝ q = q ⬝ p
-- Proved axiom-free via path commutativity in product spaces!
def Torus.surf : Torus.p.trans Torus.q = Torus.q.trans Torus.p := by
  have path_comm (p q : S1.base = S1.base) :
    (congrArg (fun x => (x, S1.base)) p).trans (congrArg (fun y => (S1.base, y)) q) =
    (congrArg (fun y => (S1.base, y)) q).trans (congrArg (fun x => (x, S1.base)) p) := by
    cases p; cases q; rfl
  exact path_comm S1.loop S1.loop
```

#### D. Homotopy Pushouts (Suspensions, Mapping Cones, Wedge Sums)
General topological pushouts (gluing spaces together along a subspace) are HITs. For example, the **Suspension** ($\Sigma A$) of a space $A$:
```hoTT
data Susp (A : Type) : Type where
  north : Susp A
  south : Susp A
  merid : A → north = south   -- A family of 1-cells parameterized by A
```
*(For $A = S^1$, $\text{Susp}(S^1) \simeq S^2$, the 2-sphere!)*

```lean
-- Raw 0-cells (North and South poles)
inductive SuspRaw : Type where
  | north : SuspRaw
  | south : SuspRaw

-- Relation for 1-cells: one path (meridian) for each point a : A
inductive SuspRel (A : Type) : SuspRaw → SuspRaw → Prop where
  | merid (a : A) : SuspRel A .north .south

-- HIT Definition
def Susp (A : Type) : Type := Quot (SuspRel A)

def Susp.north {A : Type} : Susp A := Quot.mk (SuspRel A) .north
def Susp.south {A : Type} : Susp A := Quot.mk (SuspRel A) .south

-- 1-cell constructor (meridians)
def Susp.merid {A : Type} (a : A) : Susp.north (A := A) = Susp.south :=
  Quot.sound (SuspRel.merid a)
```

---

### 3. Truncations = Postnikov Stages

HITs can also be used to define **Homotopy Truncations** ($\|A\|_n$), which inductively add higher path constructors to "kill" all homotopy groups above dimension $n$:

* **$\|A\|_{-1}$ (Propositional Truncation)**: Adds paths between all pairs of points, turning any space into a contractible space or empty space ($0$-truncated / truth value). Topologically, this is making a space **path-connected**.
* **$\|A\|_n$ ($n$-Truncation)**: Kills all homotopy above dimension $n$ ($\pi_k(A) = 0$ for $k > n$). In algebraic topology, this constructs **Postnikov stages** and **Eilenberg–MacLane spaces** $K(G, n)$.

---

### Summary: Synthetic Topology

In HoTT, inductive types provide a framework for **Synthetic Homotopy Theory**:
* **Standard Inductive Types** = Discrete topology / 0-dimensional spaces.
* **Higher Inductive Types (HITs)** = Continuous spaces defined as **CW-complexes**, **homotopy pushouts**, and **cell attachments**.

This allows topologists to prove theorems about topological spaces (e.g., computing $\pi_1(S^1) = \mathbb{Z}$ or $\pi_3(S^2) = \mathbb{Z}$) **purely logic-wise using induction**, without ever needing real numbers ($\mathbb{R}$), open sets, or point-set topology metrics!
