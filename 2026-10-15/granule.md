```haskell
--- Push coeffects on a pair into the left and right elements. A distributive
--- law of graded necessity over products. Note however that this is not always
--- defined: the operation {c ⨱ c} is partial and is only defined if the semiring
--- k permits this behaviour at c. (An example of a semiring where this is not true
--- is for k = LNL and c = 1).
pushPair : forall {a : Type, b : Type, k : Coeffect, c : k} . {Pushable c} => (a × b) [c] -> a [c] × b [c]
pushPair = push @(,)
```

```haskell
(a × b) [1 : LNL] -> a [1 : LNL] × b [1 : LNL] --  **YES** *(corrected)* | `1 ⨱ 1` is valid; preserves exact $1$-to-$1$ linear lockstep.
(a × b) [Many : LNL] -> a [Many : LNL] × b [Many : LNL] -- ❌ **NO** | `Many ⨱ Many` is rejected; decouples lifecycles ($!(A \otimes B) \not\multimap !A \otimes !B$).
(a × b) [0 : LNL] -> a [0 : LNL] × b [0 : LNL] -- ❌ **NO** | `0 ⨱ 0` is rejected; cannot fabricate a linear pair from an erased box.
(a × b) [1 : LNL] -> a [1 : LNL] × b [0 : LNL] -- ❌ **NO** | Fails weakening: $0 \not\le 1$ in `LNL`.
(a × b) [1 : LNL] -> a × b -- **YES** | Dereliction (unboxing the linear pair).

------------

(a × b) [1 : Nat]   -> a [1 : Nat] × b [1 : Nat]     -- YES (meet / sharing: 1 ⊔ 1 = 1)
(a × b) [1 : Nat]   -> a [1 : Nat] × b [0 : Nat]     -- NO  (Nat forbids weakening: 0 ≰ 1)
(a × b) [100 : Nat] -> a [100 : Nat] × b [0 : Nat]   -- NO  (still requires weakening: 0 ≰ 100)
(a × b) [100 : Nat] -> a [100 : Nat] × b [100 : Nat] -- YES (sharing: 100 ⊔ 100 = 100)
(a × b) [1 : Nat]   -> a × b                         -- YES (dereliction)
(a × b) [2 : Nat]   -> a × b                         -- NO  (under-use / exact usage mismatch)
(a × b)             -> (a × b) [1 : Nat]             -- NO  (linear variables cannot cross into boxes)
(a × b)             -> (a × b) [2 : Nat]             -- NO  (cannot duplicate linear resource + cannot box)

----------

(a × b) [0..1]   -> a [0..1] × b [0..1]     -- YES
(a × b) [0..1]   -> a [0..1] × b [0..0]     -- YES  (Big change!)
(a × b) [0..100] -> a [0..100] × b [0..0]   -- YES
(a × b) [0..100] -> a [0..100] × b [0..100] -- YES
(a × b) [0..1]   -> a × b                   -- YES
(a × b) [0..2]   -> a × b                   -- YES  (Different from [2 : Nat]!)
(a × b)          -> (a × b) [0..1]          -- NO
(a × b)          -> (a × b) [0..2]          -- NO
a [0..1]         -> a [0..1] × a [0..1]     -- NO
```
