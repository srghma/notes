### 3. Why are `str`, `[u8]`, and `dyn Trait` considered `!Sized`?

A type is `!Sized` (Unsized) if the compiler **cannot know its size at compile-time.**

#### `[u8]` (The Slice)
Imagine you have a function that processes a list of bytes:
```rust
fn process(data: [u8]) { ... } // Error!
```
The type `[u8]` represents a sequence of bytes. But how many? 5? 5,000? 5 million? 
If the compiler allowed `data: [u8]`, it wouldn't know how much space to reserve on the **Stack** for that function call. Therefore, `[u8]` is `!Sized`.
*   **The Fix:** We use `&[u8]`. The reference has a known size (two words: pointer + length).

#### `str` (The String Slice)
`str` is just a `[u8]` that is guaranteed to be valid UTF-8. Just like a slice, a "String" could be one letter or an entire book. Because the length is not part of the type (it's not `str<10>`), the compiler sees it as having an unknown size.

#### `dyn Trait` (The Trait Object)
This is the most interesting case. A Trait Object is a stand-in for **any** type that implements a trait.
```rust
trait Speaker { fn speak(&self); }

struct Cat; // Size 0
struct Elephant { weight: u32, trunk_length: u32 } // Size 8

// Which one is this? The compiler doesn't know!
fn make_it_speak(speaker: dyn Speaker) { ... } // Error!
```
Because `dyn Speaker` could be a `Cat` (0 bytes) or an `Elephant` (8 bytes), the type `dyn Speaker` itself has no fixed size. It is `!Sized`.

---

### 💡 Summary: The "Stack" Rule
The reason `!Sized` types exist is to prevent you from putting things on the **Stack** that would break the "Fixed Stack Frame" model.

If you can't answer the question **"Exactly how many bytes is this?"** by looking only at the source code (without running it), the type is `!Sized`.

| Type | Size known at compile-time? | Sizedness |
| :--- | :--- | :--- |
| `u32` | Yes (4 bytes) | `Sized` |
| `[u32; 5]` | Yes (20 bytes) | `Sized` |
| `&[u32]` | Yes (16 bytes on 64-bit: ptr + len) | `Sized` |
| `[u32]` | **No** (Depends on data) | **`!Sized`** |
| `str` | **No** (Depends on text length) | **`!Sized`** |
| `dyn MyTrait`| **No** (Depends on underlying struct) | **`!Sized`** |
