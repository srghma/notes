| Question                                       | Answer                                                                         |
| ---------------------------------------------- | ------------------------------------------------------------------------------ |
| Is `Eq` a primitive like `Quot`?               | **No.** `Eq` is an ordinary `inductive` type. `Quot` is kernel-special.        |
| Is `Eq.ndrec` a primitive like `Quot.mk`?      | **No.** It's a plain Lean `abbrev` over `Eq.rec`, the auto-generated recursor. |
| Is `Eq` part of the kernel?                    | Only as generic inductive machinery. There's no `Eq`-specific "add" code.      |
| Does `Eq` have an `add_quot_impl` equivalent?  | **No.** It goes through the generic `add_inductive` path.                      |
| Does `Eq` have a `quot_reduce_rec` equivalent? | **No.** It reduces via the generic recursor/iota path all inductives use.      |

The one-line summary: **`Quot` is a hand-built kernel primitive; `Eq` is just a normal inductive type. Everything special about `Quot` exists *because* it isn't an inductive.**

---

## What `Eq.ndrec` actually is

`src/Init/Prelude.lean:80`:

```lean
@[simp] abbrev Eq.ndrec {α : Sort u2} {a : α} {motive : α → Sort u1}
    (m : motive a) {b : α} (h : Eq a b) : motive b :=
  h.rec m
```

It's **transport / substitution**: given a value `m : motive a` and a proof `h : a = b`, it hands you back a `motive b`. "nd" = *non-dependent*: the `motive` depends only on the element (`α → Sort`), not on the proof `h`. It's a thin convenience wrapper — the body is literally `h.rec m`, i.e. `Eq.rec` applied to `m`.

That's exactly why it appears in `Quot.rec`'s coherence hypothesis (`Core.lean:1872`): `Eq.ndrec (f a) (sound p) = f b` transports `f a` along the equality `sound p : Quot.mk r a = Quot.mk r b`.

The real layering for `Eq`:

- `Eq` — the inductive type (`Prelude.lean:73`), `inductive Eq : α → α → Prop`
- `Eq.refl` — its single constructor, added automatically by the inductive machinery
- `Eq.rec` — its recursor, **auto-generated** by the inductive machinery (not hand-written, not `opaque`)
- `Eq.ndrec` — a library `abbrev` over `Eq.rec`

Compare with `Quot`, where `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` are `opaque` signatures materialized by the kernel's bespoke `add_quot_impl`. `Eq` has none of that.

---

## Why `Eq` needs no `add_quot` and no `quot_reduce_rec`

**Adding it.** `Quot` needs `add_quot_impl` (`kernel_type_checker.rs:5889`) because it is *not* an inductive — the kernel has to synthesize four constants by hand. `Eq` is a genuine inductive, so it's registered through the same generic `add_inductive` path as `List`/`Nat`, and its constructor + recursor are generated automatically. There is no `add_eq`.

The *only* `Eq`-specific code in the kernel is `check_eq_type_for_quot` (`kernel_type_checker.rs:5781`, porting `check_eq_type` in `quot.cpp:19`). And it does **not add `Eq`** — it only *validates* that `Eq` already exists with the expected shape before `Quot` is added, because `Quot.lift`'s type mentions `Eq`.

**Reducing it.** `Quot` needs the bespoke `quot_reduce_rec` (`kernel_type_checker.rs:3085`) precisely because it has no real constructor for the generic iota rule to fire on — `Quot.lift f h (Quot.mk r a) ↝ f a` is a special rule. `Eq.rec` has a real constructor (`Eq.refl`), so it reduces through the **generic** recursor/iota path, `inductive_reduce_rec_impl` (`kernel_type_checker.rs:4790`) — the same function that reduces every inductive recursor. Note the dispatch order in `reduce_recursor` (`:3070`): quotient reduction is tried first, then falls through to the generic inductive reduction that handles `Eq.rec`, `Nat.rec`, etc.

---

## The one genuinely special thing about `Eq`: K-like reduction

`Eq.rec` is flagged as a **K recursor** (`lean_recursor_val_is_k`, `kernel_type_checker.rs:937`). In `inductive_reduce_rec_impl` (`:4830`):

```rust
if lean_recursor_val_is_k(rec_val) {
    major = to_cnstr_when_K_impl(env, rec_val, major, tc)?;
}
```

K-like reduction lets `Eq.rec` reduce even when the major premise isn't *syntactically* `Eq.refl` — if its type says it's an equality proof, the kernel synthesizes the constructor. This is definitional "Axiom K" / uniqueness of identity proofs, set up by `init_k_target` (`:6870`).

Two things to note:
1. This is a **generic recursor feature** keyed off the `is_k` flag, not `Eq`-bespoke code. Any qualifying subsingleton-like inductive gets it.
2. Related: because `Eq a b : Prop`, all its proofs are definitionally equal via **proof irrelevance** (`is_def_eq_proof_irrel`, `:4023`) — again a generic `Prop` rule, not `Eq`-specific.

So `Eq` is "special" only in that it happens to be a subsingleton `Prop`-valued inductive whose recursor qualifies for K — all handled by generic machinery — whereas `Quot` is special because the kernel author literally carved out dedicated add/reduce code paths for it.
