### 1. Where is the Grammar of Granule Defined?

The grammar and AST of Granule are defined in the `frontend` package:

* **Concrete Grammar (Happy parser):**
  [`Language/Granule/Syntax/Parser.y`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Syntax/Parser.y)
  * Defines the BNF-style productions for expressions, types, patterns, coeffects, effects, uniqueness guarantees, and language extensions.
* **Lexer (Alex lexer):**
  [`Language/Granule/Syntax/Lexer.x`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Syntax/Lexer.x)
* **Abstract Syntax Trees (AST):**
  * **Types:** [`Language/Granule/Syntax/Type.hs`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Syntax/Type.hs#L45-L69) (defines `Type`, `FunTy`, `Box`, `Star`, `Borrow`, etc.)
  * **Expressions & Values:** [`Language/Granule/Syntax/Expr.hs`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Syntax/Expr.hs)
  * **Definitions & Top-level:** [`Language/Granule/Syntax/Def.hs`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Syntax/Def.hs)

---

### 2. Does Granule Allow Unique Function Arguments?

**Yes, absolutely.**

Granule has first-class support for **uniqueness types and borrowing**:

* **Syntax for Unique Types:**
  * Shorthand: `*a`
  * Explicit guarantee: `a *{Unique}` (represented in the AST as [`Star (TyCon "Unique") a`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Syntax/Type.hs#L52)).
* **Unique function arguments in practice:**
  You can pass unique types as function arguments just like any other type. For example, from Granule's test suite ([copyUniqueArray.gr:L1](file:///home/srghma/projects/granule/frontend/tests/cases/positive/unique/copyUniqueArray.gr#L1) and [share.gr:L2-L6](file:///home/srghma/projects/granule/frontend/tests/cases/positive/unique/share.gr#L2-L6)):
  ```granule
  -- Takes a unique array argument (*), an unrestricted int (!), and returns a unique array
  fill : forall {id : Name} . *(FloatArray id) -> !Int -> *(FloatArray id)

  -- Duplicate or discard a unique argument by sharing it
  dup : forall {p : Type} . *p -> (p, p)
  dup a = let !u = share a in (u, u)

  fst : forall {p q : Type} . (p, *q) -> p
  fst (a, b) = let !u = share b in a
  ```
* **Borrowing:** Granule also supports borrowing unique values via permissions: `& permission a` with primitives like `withBorrow` and `split` ([Primitives.hs:L683-L690](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Primitives.hs#L683-L690)).

---

### 3. Linearity vs Uniqueness: "Future" vs "Past" ($R \le 1$)

Your intuition is **spot on**, and Granule’s typechecker is designed explicitly around this distinction:

#### The Duality: Future vs Past
* **Linearity / Coeffects ($R \le 1$ or $R = 1$) are about the FUTURE:**
  A linear type judgment $\Gamma \vdash e : A$ is a contract on the **continuation** (how $e$ will be consumed downstream).
  It says: *"I promise that whoever holds this reference will evaluate/consume it at most once."*
* **Uniqueness ($*A$) is about the PAST / Topology:**
  A uniqueness guarantee is a statement about **heap aliasing and sharing history**.
  It says: *"At this moment, this pointer is the sole incoming reference to this object in the entire heap."*

#### Why $R \le 1$ does NOT equal Uniqueness
Suppose object $O$ in memory has two pointers, $x$ and $y$:
* You can give $x$ the type $A [0..1]$ (or $R \le 1$). $x$ guarantees that *it* will only be read once.
* But $O$ is **not unique**, because pointer $y$ also exists!
* If you perform an in-place mutation on $x$ under the mistaken belief that $R \le 1 \implies \text{Unique}$, you will destroy the value under pointer $y$, violating referential transparency.

#### How Granule Formalizes This
Granule does **not** model uniqueness as a coeffect semiring ($R \le 1$). Instead:
1. Coeffects are comonadic modalities ($\Box_r A$ / `a [r]`) tracking **future usage**.
2. Uniqueness is a guarantee modality (`*A` / `a *{Unique}`) tracking **reference isolation**.

Granule's typechecker explicitly enforces this separation. In [`Language/Granule/Checker/Monad.hs:L867`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Monad.hs#L867), if you attempt to treat uniqueness as a coeffect, the compiler throws:
> *"Cannot promote non-unique value of type `t` to unique, **since uniqueness is not a coeffect**."*

You can safely convert a unique reference into a linear/graded reference because absence of aliases implies $\le 1$ future use ([`uniqueReturn : *a -> a [r]`](file:///home/srghma/projects/granule/frontend/src/Language/Granule/Checker/Primitives.hs#L662)), but the reverse is strictly prohibited.
