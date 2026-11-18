I tried to understand how to reduce `f (CompleteLattice.sup s) = CompleteLattice.sup (fun y => ∃ x, s x ∧ y = f x)`

to its buiding blocks

got

```lean
 f (Classical.choose
     (show ∃ a,
       ∀ x, a ⊑ x ↔ (∀ y, s y → y ⊑ x)
       from CompleteLattice.has_sup s))
 =
 Classical.choose
   (show ∃ b,
     ∀ x, b ⊑ x ↔
       (∀ y, (∃ x, s x ∧ y = f x) → y ⊑ x)
     from CompleteLattice.has_sup
       (fun y => ∃ x, s x ∧ y = f x))
```

but can this be improved? make several proposals

Dont use notation - only constructors . E.g. `∃` will become `Sigma.mk`?

--------------------------------

### 1. First: `∃` vs `Sigma.mk` (and notation vs constructors)

In Lean 4, **`∃` is not `Sigma` (`Sigma.mk`)**:

* **`∃ x, P x`** lives in `Prop`. Its type constructor is **`Exists`** (`Exists (fun x => P x)`), and its proof constructor is **`Exists.intro`**.
* **`Σ x, P x`** (`Sigma`) lives in `Type`/`Sort`. Its type constructor is **`Sigma`**, and its value constructor is **`Sigma.mk`**.

Also note the difference between a **type** and its **value constructor** when reducing a statement (which is itself a type/proposition):

| Notation | Underlying type / function | Proof / value constructor |
| :--- | :--- | :--- |
| `a = b` | `Eq a b` | `Eq.refl` |
| `a ⊑ b` | `PartialOrder.rel a b` | *(depends on the `PartialOrder` instance)* |
| `P ↔ Q` | `Iff P Q` | `Iff.intro` |
| `P ∧ Q` | `And P Q` | `And.intro` |
| `∃ x, P x` | `Exists (fun x => P x)` | `Exists.intro` |
| `∀ x, P x` / `P → Q` | `(x : α) → P x` / `P → Q` | *(primitive dependent function type; `fun` is lambda abstraction)* |
| `show T from e` | `(e : T)` | *(type ascription syntax; redundant if `e` already has type `T`)* |

In your expression, `=`, `⊑`, `↔`, `∧`, and `∃` appear at the **proposition/type level**, so removing notation replaces them with **`Eq`**, **`PartialOrder.rel`**, **`Iff`**, **`And`**, and **`Exists`**.

---

### 2. What can be improved in your current expansion

1. **`show ... from ...` is redundant**: `CompleteLattice.has_sup s` *already* has the type `Exists (is_sup s)`. Using `show` only served to make the implicit predicate `p` of `Classical.choose` visible. Instead, pass `p` explicitly with `@Classical.choose α p (...)`.
2. **Variable shadowing**: In `(∀ y, (∃ x, s x ∧ y = f x) → y ⊑ x)`, `x` is bound both outside and inside `∃ x`. Renaming the outer `x` to `ub` (upper bound) avoids confusion.
3. **`Classical.choose` is not primitive**: In `Init.Classical`, `Classical.choose` is defined in terms of `Classical.indefiniteDescription`, which itself reduces to **`Classical.choice`**, **`Exists.elim`**, **`Nonempty.intro`**, **`Subtype.mk`**, and **`Subtype.val`**.
4. **Typeclass fields are still hidden**: `@CompleteLattice.has_sup` and `@PartialOrder.rel` implicitly pull from `[CompleteLattice α]`.

Below are **four proposals**, ordered from exact syntactic unfolding to deeper kernel reduction and cleaner mathematical reformulations.

---

### Proposal 1: Clean syntactic desugaring (same term, zero notation)

This keeps your exact level of abstraction (`Classical.choose` + `CompleteLattice.has_sup`), removes all notation, drops `show ... from`, fixes the `x` shadowing (`ub`), and makes the predicate argument to `@Classical.choose` explicit:

```lean
Eq
  (f
    (@Classical.choose α
      (fun (a : α) =>
        (ub : α) →
          Iff
            (PartialOrder.rel a ub)
            ((y : α) → s y → PartialOrder.rel y ub))
      (CompleteLattice.has_sup s)))
  (@Classical.choose α
    (fun (b : α) =>
      (ub : α) →
        Iff
          (PartialOrder.rel b ub)
          ((y : α) →
            Exists (fun (x : α) => And (s x) (Eq y (f x))) →
            PartialOrder.rel y ub))
    (CompleteLattice.has_sup
      (fun (y : α) => Exists (fun (x : α) => And (s x) (Eq y (f x))))))
```

---

### Proposal 2: Reduce all the way down to `Classical.choice`, `Subtype`, and instance fields

If you want to see every primitive building block—removing `Classical.choose` and implicit `[CompleteLattice α]` arguments—`Classical.choose h` unfolds to:
`Subtype.val (Classical.choice (Exists.elim h (fun a ha => Nonempty.intro (Subtype.mk a ha))))`

Writing `inst : CompleteLattice α` explicitly and naming `rel := @PartialOrder.rel α (@CompleteLattice.toPartialOrder α inst)`:

```lean
-- Every step of `CompleteLattice.sup` unfolded to kernel primitives + `Classical.choice`:
Eq
  (f
    (Subtype.val
      (Classical.choice
        (Exists.elim
          (@CompleteLattice.has_sup α inst s)
          (fun (a : α)
               (ha : (ub : α) →
                 Iff
                   (@PartialOrder.rel α (@CompleteLattice.toPartialOrder α inst) a ub)
                   ((y : α) → s y →
                     @PartialOrder.rel α (@CompleteLattice.toPartialOrder α inst) y ub)) =>
            Nonempty.intro (Subtype.mk a ha))))))
  (Subtype.val
    (Classical.choice
      (Exists.elim
        (@CompleteLattice.has_sup α inst
          (fun (y : α) => Exists (fun (x : α) => And (s x) (Eq y (f x)))))
        (fun (b : α)
             (hb : (ub : α) →
               Iff
                 (@PartialOrder.rel α (@CompleteLattice.toPartialOrder α inst) b ub)
                 ((y : α) →
                   Exists (fun (x : α) => And (s x) (Eq y (f x))) →
                   @PartialOrder.rel α (@CompleteLattice.toPartialOrder α inst) y ub)) =>
          Nonempty.intro (Subtype.mk b hb)))))
```

Why this is insightful:
* `Exists` is in `Prop`, so you cannot extract `a : α` directly out of `Exists` into `Type`.
* Instead, `Exists.elim` moves `Exists` into `Nonempty (Subtype ...)` (still in `Prop`, via `Nonempty.intro` + `Subtype.mk`).
* `Classical.choice` crosses from `Prop` (`Nonempty`) into `Type` (`Subtype`).
* `Subtype.val` projects out the element `a : α`.

---

### Proposal 3: Eliminate `Classical.choose` completely via `is_sup` (logically equivalent)

For actually *working* with `PreservesSup`, unfolding `CompleteLattice.sup` into `Classical.choose` is usually painful because you can't inspect `Classical.choose` directly—you always have to go through `Classical.choose_spec` and `rel_antisymm`.

Since suprema are unique by antisymmetry, `f (sup s) = sup { f x | s x }` is **logically equivalent** to saying that `f` maps any supremum of `s` to a supremum of `{ f x | s x }`—with **zero `Classical.choose` or `CompleteLattice.has_sup` needed**:

```lean
(a : α) →
  ((ub : α) →
    Iff
      (PartialOrder.rel a ub)
      ((y : α) → s y → PartialOrder.rel y ub)) →
  ((ub : α) →
    Iff
      (PartialOrder.rel (f a) ub)
      ((y : α) →
        Exists (fun (x : α) => And (s x) (Eq y (f x))) →
        PartialOrder.rel y ub))
```

---

### Proposal 4: Simplify the image predicate (logically equivalent, removes `Exists`, `And`, and `Eq`)

Look at the sub-expression on the right-hand side of `Iff`:
`(y : α) → Exists (fun (x : α) => And (s x) (Eq y (f x))) → PartialOrder.rel y ub`

Saying "for all `y`, if there exists `x` such that `s x` and `y = f x`, then `y ⊑ ub`" is logically equivalent to simply:
`(x : α) → s x → PartialOrder.rel (f x) ub`

Applying this to Proposal 3 gives the cleanest possible "first-principles" version of `PreservesSup`:

```lean
(a : α) →
  ((ub : α) →
    Iff
      -- `mp : PartialOrder.rel a ub → ((x : α) → s x → PartialOrder.rel x ub)`
      -- (meaning: a ⊑ ub)
      (PartialOrder.rel a ub)
      -- `mpr : ((x : α) → s x → PartialOrder.rel x ub) → PartialOrder.rel a ub`
      -- (meaning: ∀ x, s x → x ⊑ ub)
      ((x : α) → s x → PartialOrder.rel x ub)) →
  ((ub : α) →
    Iff
      (PartialOrder.rel (f a) ub)
      ((x : α) → s x → PartialOrder.rel (f x) ub))
```

In plain English: *"Whenever `a` has the exact same upper bounds as `s`, `f a` has the exact same upper bounds as `{ f x | x ∈ s }`."*

### Summary of which to choose
* **Proposal 1** if you want the exact original statement rewritten strictly without notation.
* **Proposal 2** if you want to see how `sup` bottoms out at Lean's choice axiom and `Subtype`/`Nonempty`.
* **Proposals 3 & 4** if your goal is to understand or prove properties of `PreservesSup` without fighting `Classical.choose`.
