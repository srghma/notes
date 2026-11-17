```rs
pub enum Cow<'a, B> where
    B: 'a + ToOwned + ?Sized, {
    Borrowed(&'a B),
    Owned(<B as ToOwned>::Owned),
}

pub trait ToOwned {
    type Owned: Borrow<Self>;
    fn to_owned(&self) -> Self::Owned;
}

impl ToOwned for str {
    type Owned = String;

    #[inline]
    fn to_owned(&self) -> String {
        unsafe { String::from_utf8_unchecked(self.as_bytes().to_owned()) }
    }
}

pub trait Borrow<Borrowed> where
    Borrowed: ?Sized,
{
    // Required method
    fn borrow(&self) -> &Borrowed;
}

impl Borrow<str> for String {
    #[inline]
    fn borrow(&self) -> &str {
        &self[..]
    }
}

```

Examples of !Sized types:
- `str` (not `&str`, but the raw string data).
- `[u8]` (not `&[u8]`, but the raw slice data).
- `dyn Trait` (trait objects).

1. Sized is a requirement for a value to be stored directly on the Stack. The compiler needs to know exactly how many bytes to "move" the stack pointer when a function starts.

> Sized means can be put in rodata?

https://corecursive.com/016-moves-and-borrowing-in-rust-with-jim-blandy/

----
> You tell
> `fn func<T>(item: T) { ... }`
> is actually
> `fn func<T: Sized>(item: T) { ... }`
> are there any other 
> `fn func<T: Sized, XXX>(item: T) { ... }`
> added implicitly?
