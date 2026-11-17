### Concrete Examples in the Repo

#### 1. In `frontend/tests/cases/positive/unique/`
* [copyUniqueArray.gr](file:///home/srghma/projects/granule/frontend/tests/cases/positive/unique/copyUniqueArray.gr#L1-L15):
  ```granule
  fill : forall {id : Name} . *(FloatArray id) -> !Int -> *(FloatArray id)
  ```
* [cloneLaw.gr](file:///home/srghma/projects/granule/frontend/tests/cases/positive/unique/cloneLaw.gr#L1-L3):
  ```granule
  unitL : forall {a b : Type, id : Name} .
          *(FloatArray id) -> (exists {id1 : Name} . *(FloatArray id1) -> b) -> b
  unitL t f = clone (share t) as x in f x
  ```

#### 2. Borrowing & Fractional Permissions in [`examples/parallelWithMutation.gr`](file:///home/srghma/projects/granule/examples/parallelWithMutation.gr#L23-L56)
This file demonstrates splitting a borrow `& 1` into two read-only fractional borrows `& 1/2` to perform parallel computation, then re-joining them:

```haskell
import Parallel
import Prelude
import Vec

--- Convert an indexed natural number to an untyped int
natToInt'
  : forall {n : Nat}
  . N n -> Int
natToInt' Z = 0;
natToInt' (S m) = 1 + natToInt' m

toFloatArray : forall {n : Nat} . Vec n Float -> exists {id : Name} . *(FloatArray id)
toFloatArray v =
  let (n', v) = length' v
  in unpack <id, arr> = newFloatArray (natToInt' n')
  in pack <id, (toFloatArrayAux arr [0] v)> as exists {id : Name} . *(FloatArray id)

toFloatArrayAux : forall {n : Nat, id : Name} . *(FloatArray id) -> Int [n] -> Vec n Float -> *(FloatArray id)
toFloatArrayAux a [n] Nil = a;
toFloatArrayAux a [n] (Cons x xs) =
  toFloatArrayAux (writeFloatArray a n x) [n + 1] xs

sumFromTo : forall {id : Name, f : Fraction} . & f (FloatArray id) ->  !Int -> !Int -> (Float, & f (FloatArray id))
sumFromTo array [i] [n] =
  if i == n
    then (0.0, array)
    else
      let (x, a) = readFloatArray array i;
          (y, arr) = sumFromTo a [i+1] [n]
      in  (x + y, arr)

-- A reference to a droppable value can be written to without violating linearity
writeRef : forall {a : Type, id : Name} . {Dropable a} => a -> & 1 (Ref id a) -> & 1 (Ref id a)
writeRef x r = let
    (y, r') = swapRef r x;
    () = drop@a y in r'

parSum : forall {id id' : Name} . *(FloatArray id) -> *(Ref id' Float) -> *(Ref id' Float, FloatArray id)
parSum array ref = let
     ([n], array) : (!Int, *(FloatArray id))     = lengthFloatArray array;
     compIn                                      = borrowPull (ref, array)
  in flip withBorrow compIn (\compIn ->

                let (ref, array)      = borrowPush compIn;
                    (array1, array2)  = split array;

                    -- Compute in parallel
                    ((x, array1), (y, array2)) =
                                par (\() -> sumFromTo array1 [0] [div n 2])
                                    (\() -> sumFromTo array2 [div n 2] [n]);

                    -- Update the reference
                    ref'        = writeRef ((x : Float) + y) ref;
                    compOut     = borrowPull (ref', join (array1, array2))

                  in compOut)

main : Float
main =
  unpack <id , arr> = toFloatArray (Cons 10.0 (Cons 20.0 (Cons 30.0 (Cons 40.0 Nil)))) in
  unpack <id', ref> = newRef 0.0 in
  let
      (result, array) = borrowPush (parSum arr ref);
      () = deleteFloatArray array
  in freezeRef result
```
*(Also see [`work-in-progress/Fractional.gr`](file:///home/srghma/projects/granule/work-in-progress/Fractional.gr#L12-L53) for `& 2/4 Colour -> & 1/2 Colour` equivalence tests).*

---

### Part 2: `TyRational` vs `TyFraction`

Both wrap Haskell's `Rational` in the AST, but they inhabit completely different type kinds and serve different purposes:

| Feature | `TyRational` | `TyFraction` |
| :--- | :--- | :--- |
| **AST Constructor** | `TyRational :: Rational -> Type` | `TyFraction :: Rational -> Type` |
| **Kind** | `Q` / `Float` (Coeffect Semiring) | `Permission` / `Fraction` |
| **Parser Syntax** | Floats like `0.5`, `1.5` | Fractional ratios `1/2`, `2/4`, `1` |
| **Domain** | **Resource coeffects** (Differential privacy, sensitivity analysis, continuous consumption) | **Borrowing permissions** (Fractional permissions for shared read vs exclusive write) |
| **Example** | `a [0.5]` (e.g. in differential privacy or metric spaces) | `& 1/2 a` (e.g. read-only borrowed alias) |

---

### Part 3: Complete Breakdown of `data Type`

```haskell
data Type where
```

#### Core & Functional Syntax
* **`Type :: Int -> Type`**
  * Universe levels ($Type_0, Type_1, \dots$). In Granule, kinds are themselves types. `Type 0` is the universe of standard types.
* **`FunTy :: Maybe Id -> Maybe Coeffect -> Type -> Type -> Type`**
  * Function arrow $A \to B$.
  * `Maybe Id`: For dependent function binders `(x : A) -> B`.
  * `Maybe Coeffect`: The grade on the arrow in `GradedBase` mode (`A % r -> B`). If `Nothing`, it is standard linear `A -> B`.
* **`TyCon :: Id -> Type`**
  * Type constructor constant (e.g., `Int`, `Float`, `Vec`, `Unique`, `Nat`, `IO`).
* **`TyVar :: Id -> Type`**
  * Type variable identifier (e.g., `a`, `b`, `n`, `r`).
* **`TyApp :: Type -> Type -> Type`**
  * Type application `T1 T2` (e.g., `Vec n a` is `TyApp (TyApp (TyCon "Vec") (TyVar "n")) (TyVar "a")`).

#### Modalities: Coeffects, Effects, Ownership
* **`Box :: Coeffect -> Type -> Type`**
  * Graded modal necessity $\Box_r A$, written `a [r]`. Represents coeffects (e.g. usage demand, sensitivity, privacy).
* **`Diamond :: Effect -> Type -> Type`**
  * Graded modal possibility $\Diamond_e A$, written `a <e>` (e.g. `Int <IO>`, `a <{Stdout}>`). Represents computational monads/effects.
* **`Star :: Guarantee -> Type -> Type`**
  * Uniqueness guarantee: `*a` or `a *{Unique}`. Guarantees no existing aliases in the heap.
* **`Borrow :: Permission -> Type -> Type`**
  * Borrowed reference: `& p a`. Represents an alias with access permission $p$.

#### Type-Level Numbers & Quantities
* **`TyInt :: Int -> Type`**
  * Type-level natural/integer literal (e.g., vector length `Vec 3 Int`, or discrete grade `a [2]`).
* **`TyRational :: Rational -> Type`**
  * Continuous numeric coeffect (parsed from floats, e.g. `a [0.5]`).
* **`TyFraction :: Rational -> Type`**
  * Fractional borrow permission (parsed from `n/d`, e.g. `& 1/2 a`).
* **`TyGrade :: Maybe Type -> Int -> Type`**
  * A grade literal explicitly or implicitly tagged with its semiring kind (e.g., `1 : Nat`, `0 : ExtNat`).
* **`TyInfix :: TypeOperator -> Type -> Type -> Type`**
  * Infix type-level operators:
    * *Semiring algebra:* `+`, `*`, `-`, `^`, `/\` (meet), `\/` (join), `..` (intervals `[0..1]`).
    * *Type operators:* `×` (pair type), `&` (additive product).
    * *Predicate constraints:* `==`, `<=`, `. <=`, `=>`.

#### Sets & Type Families
* **`TySet :: Polarity -> [Type] -> Type`**
  * Type-level set: `{Stdout, Stderr}`.
  * `Polarity`:
    * `Normal`: Standard set ordered by subset inclusion (e.g., effects produced).
    * `Opposite` (written `{...}.`): Dual ordering where larger sets are lower in the lattice (used for capability requirements and security clearance).
* **`TyCase :: Type -> [(Type, Type)] -> Type`**
  * Type-level pattern matching (type-level `case T of P1 -> T1; P2 -> T2`).

#### Signatures & Quantifiers
* **`TySig :: Type -> Kind -> Type`**
  * Explicit kind annotations at the type level: `T : K` (e.g., `0 : s` or `r : Nat`).
* **`TyExists :: Id -> Kind -> Type -> Type`**
  * Existential quantification: `exists {id : K} . T`.
  * Widely used with `unpack <id, x> = ... in ...` to pack unique resources with an unforgeable identity token (`exists {id : Name} . *(FloatArray id)`).
* **`TyForall :: Id -> Kind -> Type -> Type`**
  * Universal quantification / Rank-N polymorphism: `forall {a : Type} . T`.
* **`TyName :: Int -> Type`**
  * Internal compiler-generated unique type variable index.
