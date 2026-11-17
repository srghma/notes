Here is a comprehensive breakdown of Granule's `data Type` from [`Language/Granule/Syntax/Type.hs`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Syntax/Type.hs#L44-L69), covering all constructors, the uniqueness & borrowing system (`Star` vs `Borrow`, `Guarantee` vs `Permission`), the distinction between `TyRational` and `TyFraction`, and concrete code examples from the repository.

---

### Part 1: Deep Dive into `Star`, `Borrow`, `Guarantee`, and `Permission`

In Granule, **Uniqueness** and **Borrowing** form an ownership-and-permission subsystem alongside coeffects.

#### `Star` vs `Borrow`
* **`Star :: Guarantee -> Type -> Type`**:
  * **What it is:** The **uniqueness / ownership guarantee** modality.
  * **Syntax:** `*a` or `a *{Guarantee}` (defaulting to `a *{Unique}`).
  * **Meaning:** Signifies that the value has an absolute invariant or guarantee on its reference topology. Most commonly: *"This is the sole reference to this object in the entire heap (no aliases exist)."*
* **`Borrow :: Permission -> Type -> Type`**:
  * **What it is:** The **borrowed reference** type.
  * **Syntax:** `& p a` (e.g., `& 1 a`, `& 1/2 a`, `& f a`).
  * **Meaning:** A temporary capability/reference to an object `a` with access permission `p`. It allows accessing or mutating an object without destroying its unique ownership.

#### `Guarantee` vs `Permission`
In Granule's kind system ([`Primitives.hs:L113-L116`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Primitives.hs#L113-L116)):
```haskell
-- In Primitives.hs:
(mkId "Uniqueness", (kguarantee, [], []))
(mkId "Unique",     (tyCon "Uniqueness", [], []))
(mkId "Fraction",   (tyCon "Permission", [], []))
```
* **`Guarantee` (Kind of `Star`):**
  * Describes **what is guaranteed** about the reference in isolation.
  * Built-in guarantees:
    * `Unique`: Absolute unaliased ownership.
    * `Trusted`: Used in information-flow control ([`reveal : a *{Trusted} -> a [Lo]`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Primitives.hs#L673)).
* **`Permission` (Kind of `Borrow`):**
  * Describes **what access rights** the borrower currently holds using **fractional permissions** (Boyland's fractional permission model):
    * Permission `1` (or `Star` permission): **Full permission** $\implies$ Allows **in-place mutation and reading** (`{mut f}`).
    * Permission `f < 1` (e.g. `1/2`, `1/4`): **Read-only permission** $\implies$ Can be split and shared among concurrent threads!
