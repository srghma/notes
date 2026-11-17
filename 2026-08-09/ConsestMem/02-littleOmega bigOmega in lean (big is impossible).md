```lean
-- 1. Define T in Prop (impredicative type)
def T : Prop := ∀ (A : Prop), A → A

-- 2. Define ω₁ : T → T
theorem littleOmega : T → T := fun (x : T) => (x T) x

-- The polymorphic identity function (which has type T)
theorem idT : T := fun (A : Prop) (a : A) => a

-- Apply omega₁ to idT
#reduce littleOmega idT

-- Trying to make **Big Omega** (omega₁ applied to omega₁):
-- def bigOmega := littleOmega littleOmega   -- ❌ Type Error!

-- `Prop` is impredicative (you can quantify over all of `Prop` and land back in `Prop`,
-- which is what makes your `T` even expressible), but `Prop` itself lives in `Type`,
-- and `Type u` lives in `Type (u+1)` — the hierarchy never folds back on itself.
-- That asymmetry between "`Prop` quantifies over `Prop`" and "`Prop` is `Prop`" is exactly
-- what blocks **Big Omega**.

-- this works, but only `partial def` (not `theorem` or `partial theorem`)
partial def bigOmega : T := littleOmega bigOmega

-- ### Summary
-- * **Little $\omega$** ($\lambda x.\ x\ x$): Expressible as `omega₁ : T → T` in Lean because `Prop` is impredicative.
-- * **Big $\Omega$** ($\omega \, \omega$): **Impossible** to write in Lean because `omega₁` has type `T → T`, not `T`, preventing the infinite loop!

-- IF the Y combinator existed in Prop:
def Y : ∀ {A : Prop}, (A → A) → A := ...

-- We can easily construct an identity proof for False:
def false_id : False → False := fun h => h

-- Boom: A proof of False without any premises!
theorem proof_of_false : False := Y false_id

-- Y = \lambda f.\ (\lambda x.\ f\ (x\ x))\ (\lambda x.\ f\ (x\ x))

-- Works for programming, but CANNOT be used inside proofs!
partial def Y {A : Type} (f : A → A) : A :=
  f (Y f)
```


```lean
inductive NotBad : Prop
  | wrap : (∀ (P : Prop), P → P) → NotBad

-- 2. Trying to pattern-match on Bad to return a Type FAILS:
def extractType (b : NotBad) : Type :=
  match b with
  | NotBad.wrap f => Nat

-- The field `(Type → Prop)` lives in Type 1, NOT Prop
inductive Bad2 : Prop
  | wrap : (Type 0 → Prop) → Bad2

-- ❌ THIS FAILS WITH `induction` failed: recursor `Bad2.casesOn` can only eliminate into `Prop`
-- def extractType2 (b : Bad2) : Type :=
--   match b with
--   | Bad2.wrap f => Nat

-- def extractType2 (b : Bad2) : Prop :=
--   Bad2.casesOn b (fun _ => True)

-- def extractType2 (b : Bad2) : Prop := by
--   cases b
--   exact True

-- def extractType2 (b : Bad2) : Prop :=
--   Bad2.casesOn (motive := fun _ => True) b (fun _ => True)

-- def extractType21 (b : Bad2) : Prop :=
--   match (motive := Bad2 → Prop) b with
--   | Bad2.wrap f => True

-- ✅ WORKS PERFECTLY!
theorem extractProof2 (b : Bad2) : True :=
  match b with
  | Bad2.wrap _f => True.intro
```

```lean
def T : Prop := ∀ (A : Prop), A → A
def idT : T := fun A a => a

inductive Bad : Prop where
  | wrap : T → Bad

def bad : Bad := Bad.wrap idT


def unwrap : Bad → T
  | Bad.wrap x => x

partial def noBad : Bad → False
  | Bad.wrap x => noBad (x Bad bad)     -- ⚠️
```
