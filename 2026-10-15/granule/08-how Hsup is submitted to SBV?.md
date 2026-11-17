### What is `Hsup` ($\⨱$)?

`Hsup` stands for **Homomorphic supremum / "pushable" condition**. 

It represents the condition under which a graded modal box $[c]$ can be **pushed / distributed** over a multi-ary data constructor or pair:
$$\text{push} : (A \times B)[c] \to A[c] \times B[c]$$

In Granule:
* `{Pushable c}` in the stdlib ([`Prelude.gr:L113`](file:///home/srghma/projects/granule/StdLib/Prelude.gr#L113)) is syntactic sugar for `{c ⨱ c}` (defined in [`Primitives.hs:L29`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Primitives.hs#L29)).
* When you pattern match on a boxed data constructor with multiple arguments ($> 1$), Granule emits an `Hsup` constraint ([`Patterns.hs:L201`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Patterns.hs#L201)):
  ```haskell
  -- Hsup if you only have more than one premise (and have an enclosing grade)
  Just (coeff, coeffTy) | length ps > 1 ->
    addConstraintToNextFrame (Hsup s coeff coeff coeffTy)
  ```

---

### How `Hsup` is compiled and submitted to SBV

The compilation to SBV happens in **3 stages**:

#### 1. In the Constraint Compiler ([`Constraints.hs:L301-303`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Constraints.hs#L301-L303))
When `compile` visits an `Hsup` constraint:
```haskell
compile vars (Hsup _ c1 c2 t) =
  bindM2And' (\c1' c2' -> pure (symGradeHsup c1' c2'))
             (compileCoeffect (normalise c1) t vars)
             (compileCoeffect (normalise c2) t vars)
```
1. `c1` and `c2` are compiled to symbolic grades (`SGrade`).
2. They are passed to `symGradeHsup c1' c2'`, which returns an SBV boolean expression (`SBool`).

---

#### 2. The `symGradeHsup` Function ([`SymbolicGrades.hs:L434-443`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Constraints/SymbolicGrades.hs#L434-L443))
This is where the actual SBV formula is generated depending on the semiring:

```haskell
symGradeHsup :: SGrade -> SGrade -> SBool
-- | For LNL grades, when both grades are linear allow pushing, otherwise, pushing is disallowed.
-- | Check the grades are concrete to disallow hsup on grades which are polymorphic within the LNL semiring.
symGradeHsup (SLNL n) (SLNL m) | isConcrete m, isConcrete n = n .== literal oneRep .&& m .== literal oneRep
symGradeHsup (SLNL n) (SLNL m) = sFalse

-- | Disallow hsup for polymorphic grades
symGradeHsup (SUnknown s1) (SUnknown s2) = sFalse

-- | For extended grades (Ext r), recurse into the base grade
symGradeHsup (SExt r _) (SExt r' _) = symGradeHsup r r'

-- | For all other grades, allow pushing
symGradeHsup s1 s2 = sTrue
```

The logic submitted to SBV is:
* **For `LNL` (Linear / Non-Linear semiring)**:
  * Pushing a non-linear or zero box is unsound because distributing it alters resource bounds.
  * If concrete, it generates an SBV equality assertion:
    $$\mathtt{n == 1 \land m == 1}$$
    (i.e. pushing is **only allowed if both are strictly linear `One`**).
  * If not concrete, it yields SBV `sFalse`.
* **For unknown / polymorphic grades (`SUnknown`)**:
  * Pushing cannot be guaranteed sound in general, so it yields SBV `sFalse` (unless eliminated earlier by [`handleHsupPoly`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Checker.hs#L2417)).
* **For standard semirings (`Nat`, `Q`, `Interval`, etc.)**:
  * Pushing is always sound, so it returns SBV `sTrue`.

---

#### 3. Solving with Z3 via SBV ([`Constraints.hs:L58`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Constraints.hs#L58))
The generated `SBool` becomes part of the full predicate formula:
```haskell
ThmResult thmRes <- proveWith cfg $ do
  ...
  sbvTheorem
```
SBV serializes this to SMT-LIB2 format and passes it to **Z3** to check whether the theorem (including the `Hsup` conditions) holds under all quantified variables.
