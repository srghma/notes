### 1. Which types are supported as indices?

In Granule, type indices are values from the **grade / sort / index** universe that can appear in types. Because Granule integrates coeffects and indexed types under the same constraint framework, the supported index sorts are the ones Granule can represent and solve symbolically:

* **`Nat`** (natural numbers, $\mathbb{N} \ge 0$): The primary index sort used for length-indexed vectors (`Vec (n : Nat) a`), finite sets ([`Fin (n : Nat)`](file:///home/srghma/projects/granule/StdLib/Fin.gr#L16)), matrix dimensions, etc.
* **`Q` / `Fraction`**: Rational / fractional quantities (used for fractional permissions and probabilities).
* **`Ext k`**: Extensions with infinity ($\infty$), e.g., `Ext Nat`.
* **`Interval k`**: Lower- and upper-bound intervals over another index sort $k$.
* **`(k1, k2)`**: Products / tuples of index sorts.
* **`Set k`**: Finite sets of constructors over closed types.
* **Discrete / Lattice sorts**:
  * **`Sec` / `Level`**: Security classifications (`Public`, `Private`, `Hi`, `Lo`).
  * **`LNL`**: Linear / non-linear modalities (`Zero`, `One`, `Many`).
  * **`OOZ`**: $\mathbb{Z}_2$ (`0` or `1`).
* **`Type`**: Standard GADT-style type equality indexing (e.g. indexing by `Int`, `Bool`, etc.).

---

### 2. Where is the code for it?

#### A. Detecting and Classifying Indices vs Parameters
* [`Language/Granule/Syntax/Def.hs:L184-206`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Syntax/Def.hs#L184-L206):
  `typeIndices` and `findIndices` inspect the return type of each constructor in a `data` declaration. Any type parameter that does not appear as a plain invariant variable across all constructors is identified as an **index** (e.g. `n + 1` in `FS : Fin n -> Fin (n + 1)` marks position 0 as an index).
* [`Language/Granule/Checker/DataTypes.hs:L211-225`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/DataTypes.hs#L211-L225):
  `discriminateTypeIndicesOfDataType` partitions the data declaration's arguments into `(tyParams, tyIndices)`.
* [`Language/Granule/Checker/DataTypes.hs:L67-108`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/DataTypes.hs#L67-L108):
  `checkDataCon` type-checks constructors with index positions and registers existential variables.

#### B. Index Equations During Pattern Matching
* [`Language/Granule/Checker/Patterns.hs:L193-240`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Patterns.hs#L193-L240):
  When pattern matching on an indexed constructor (like `FS`), `checkPattern` instantiates the index equalities/coercions (e.g., `m ~ n + 1`) and registers them as assumptions in the constraint context.

#### C. Mapping Index Types to SMT Variables
* [`Language/Granule/Checker/Constraints.hs:L217-285`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Constraints.hs#L217-L285):
  `freshSolverVarScoped` maps index sorts to their symbolic SMT representations:
  * `"Nat"` $\to$ integer variable with condition `v .>= 0`
  * `"Q"` $\to$ non-NaN SMT float/real
  * `isInterval` $\to$ pair of `.lower` and `.upper` variables
  * `isSet` $\to$ SMT bit-vectors / set representation
  * `extendedNat` $\to$ `SNatX` (natural number or $\infty$)

---

### 3. Is Z3 called? Where?

**Yes.** Granule relies on the Haskell [SBV (Symbolic Bit-Vector)](https://hackage.haskell.org/package/sbv) library, which by default targets **Z3**.

* **Calling the SMT solver**:
  In [`Language/Granule/Checker/Constraints.hs:L57-63`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Constraints.hs#L57-L63):
  ```haskell
  let cfg = if debugging then defaultSMTCfg { verbose = True } else defaultSMTCfg
  ThmResult thmRes <- proveWith cfg $ do
    case solverTimeoutMillis of
      n | n <= 0 -> return ()
      n -> setTimeOut n
    sbvTheorem
  ```
  `defaultSMTCfg` comes from `Data.SBV`, which uses Z3 on your `$PATH`. `proveWith` spawns Z3, feeds it the SMT2 formulas generated from the type checker constraints, and parses back `Unsatisfiable` (which means the theorem is valid, i.e., `QED`) or a counterexample model.

* **Formula translation**:
  [`compileToSBV`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Constraints.hs#L103-L180) in `Constraints.hs` recursively transforms all Granule predicates (`Conj`, `Disj`, `Impl`, `Exists`, inequalities like `.<=`, `>=`) into an `SBool` theorem passed directly to `proveWith`.
