The short answer is: **No.** In terms of **trait bounds** (like `T: Clone` or `T: Debug`), **`Sized` is the only one** that the Rust compiler automatically inserts into a generic function signature.

However, there are **three "shadow rules"** that act like implicit bounds, even if they aren't written in the `T: Bound` syntax.

---

### 1. The "Outlives" Bound (Lifetimes)
If you use a reference to `T`, there is an implicit **lifetime bound** added to ensure memory safety.

```rust
fn func<'a, T>(item: &'a T) { ... }
```

The compiler implicitly adds: **`T: 'a`**
*   **What it means:** The type `T` must live at least as long as the reference `'a`. 
*   **Why:** If `T` contained a reference that expired *before* `'a`, you would have a "dangling pointer" inside your reference. Rust prevents this silently.

---

### 2. `Self: Sized` in Traits
This is like the function rule, but applied to traits. When you define a trait:

```rust
trait MyTrait {
    fn foo(&self);
}
```

The compiler implicitly adds: **`where Self: Sized`** to the trait's methods (usually).
*   **The Catch:** If you want to use your trait as a **Trait Object** (`dyn MyTrait`), you often have to explicitly opt-out of this in the trait definition using `: ?Sized`.

---

### 3. Associated Types are `Sized`
If you define a trait with an associated type:

```rust
trait Container {
    type Item; // Implicitly: type Item: Sized;
}
```

Just like generic parameters in functions, the **associated types** inside a trait are assumed to be `Sized` by default. If you want to store a slice (`[u8]`) as an `Item`, you have to write `type Item: ?Sized;`.

---

### 🛑 What is NOT added implicitly? (Common Misconceptions)

Many beginners assume other things are "default," but they are strictly **opt-in**:

1.  **`Send` and `Sync` (Thread Safety):** 
    While most types *are* `Send` and `Sync` automatically, a **generic function** does *not* assume `T` is thread-safe. If you want to move `T` into a thread, you **must** write `fn func<T: Send>(item: T)`.
    
2.  **`Copy` / `Clone`:** 
    Generics are never assumed to be copyable. They always follow **Move** semantics unless you add the bound.

3.  **`'static`:**
    A generic `T` is **not** assumed to live forever. `T` can be a short-lived reference unless you explicitly bound it with `T: 'static`.

4.  **`Unpin`:**
    This is an "auto-trait" related to async/pointers. Most types implement it automatically, but it is not added as a default bound to generic arguments.

### Summary Table of Implicit "Injections"

| Target | What is injected? | How to opt-out |
| :--- | :--- | :--- |
| `fn foo<T>` | `T: Sized` | `T: ?Sized` |
| `fn foo<'a, T>(&'a T)` | `T: 'a` | Impossible (Core Safety) |
| `trait Foo` | `Self: Sized` | `trait Foo: ?Sized` |
| `type Item` (in trait) | `Item: Sized` | `type Item: ?Sized` |

**Basically: `Sized` is the only "Trait Bound" bully in the playground.** Everything else requires you to type it out.
