-- https://github.com/HigherOrderCO/HVM4/blob/main/docs/theory/interaction_calculus.md

-- Interaction Calculus formalized in Lean 4 with intrinsically scoped terms (Term n).

abbrev Label := Nat

inductive Ty where
  | arr  : Ty → Ty → Ty
  | nat  : Ty
  | prod : Ty → Ty → Ty
  | list : Ty → Ty
  deriving DecidableEq, Repr

abbrev Ctx := List Ty

-- Typed binary operators: takes `α` and `β`, produces `γ`
inductive BinOp : Ty → Ty → Ty → Type where
  | add  : BinOp .nat .nat .nat
  | cons : BinOp α (.list α) (.list α)
  deriving Repr


-- Proof that type `τ` appears in context `Γ` (like a typed de Bruijn index)
inductive HasType : Ctx → Ty → Type where
  | here  : HasType (τ :: Γ) τ
  | there : HasType Γ τ → HasType (σ :: Γ) τ
  deriving Repr

inductive Term : Ctx → Ty → Type where
  | var  : HasType Γ τ → Term Γ τ
  | lam  : Term (A :: Γ) B → Term Γ (.arr A B)
  | app  : Term Γ (.arr A B) → Term Γ A → Term Γ B
  | sup  : Label → Term Γ τ → Term Γ τ → Term Γ τ
  | dup  : Label → Term Γ A → Term (A :: A :: Γ) τ → Term Γ τ
  | num  : Nat → Term Γ .nat
  | op2  : BinOp α β γ → Term Γ α → Term Γ β → Term Γ γ
  | pair : Term Γ A → Term Γ B → Term Γ (.prod A B)
  | nil  : Term Γ (.list A)
  deriving Repr

abbrev ClosedTerm (τ : Ty) := Term [] τ

namespace TypedIC

-- Typed renaming map: every variable in `Γ` maps to a variable of the same type in `Δ`
def Ren (Γ Δ : Ctx) := ∀ {τ}, HasType Γ τ → HasType Δ τ

def Ren.id : Ren Γ Γ := fun h => h

def Ren.lift (ρ : Ren Γ Δ) : Ren (σ :: Γ) (σ :: Δ)
  | .here    => .here
  | .there h => .there (ρ h)

def Ren.lift2 (ρ : Ren Γ Δ) : Ren (σ :: σ :: Γ) (σ :: σ :: Δ) :=
  (ρ.lift).lift

def rename : Ren Γ Δ → Term Γ τ → Term Δ τ
  | ρ, .var h        => .var (ρ h)
  | ρ, .lam body     => .lam (rename ρ.lift body)
  | ρ, .app f a      => .app (rename ρ f) (rename ρ a)
  | ρ, .sup l a b    => .sup l (rename ρ a) (rename ρ b)
  | ρ, .dup l v body => .dup l (rename ρ v) (rename ρ.lift2 body)
  | _, .num k        => .num k
  | ρ, .op2 op a b   => .op2 op (rename ρ a) (rename ρ b)
  | ρ, .pair a b     => .pair (rename ρ a) (rename ρ b)
  | _, .nil          => .nil

def shift1 (t : Term Γ τ) : Term (σ :: Γ) τ :=
  rename .there t

def shift2 (t : Term Γ τ) : Term (σ :: σ :: Γ) τ :=
  rename (fun h => .there (.there h)) t

-- Typed substitution map: every variable of type `τ` in `Γ` maps to `Term Δ τ`
def Sub (Γ Δ : Ctx) := ∀ {τ}, HasType Γ τ → Term Δ τ

def Sub.lift (σ : Sub Γ Δ) : Sub (A :: Γ) (A :: Δ)
  | .here    => .var .here
  | .there h => shift1 (σ h)

def Sub.lift2 (σ : Sub Γ Δ) : Sub (A :: A :: Γ) (A :: A :: Δ)
  | .here           => .var .here
  | .there .here    => .var (.there .here)
  | .there (.there h) => shift2 (σ h)

def subst : Sub Γ Δ → Term Γ τ → Term Δ τ
  | σ, .var h        => σ h
  | σ, .lam body     => .lam (subst σ.lift body)
  | σ, .app f a      => .app (subst σ f) (subst σ a)
  | σ, .sup l a b    => .sup l (subst σ a) (subst σ b)
  | σ, .dup l v body => .dup l (subst σ v) (subst σ.lift2 body)
  | _, .num k        => .num k
  | σ, .op2 op a b   => .op2 op (subst σ a) (subst σ b)
  | σ, .pair a b     => .pair (subst σ a) (subst σ b)
  | _, .nil          => .nil

-- Single-variable beta substitution: `(λx:A. body) arg`
def betaSubst (body : Term (A :: Γ) B) (arg : Term Γ A) : Term Γ B :=
  subst (fun
    | .here    => arg
    | .there h => .var h) body

-- Two-variable duplication substitution: `! x &L= val; body` with `v0, v1 : Term Γ A`
def dupSubst (body : Term (A :: A :: Γ) τ) (v0 v1 : Term Γ A) : Term Γ τ :=
  subst (fun
    | .here           => v0
    | .there .here    => v1
    | .there (.there h) => .var h) body

inductive Step : Term Γ τ → Term Γ τ → Prop where
  | appLam {body : Term (A :: Γ) B} {arg : Term Γ A} :
      Step (.app (.lam body) arg) (betaSubst body arg)

  | dupSupSame {l : Label} {a b : Term Γ A} {t : Term (A :: A :: Γ) τ} :
      Step (.dup l (.sup l a b) t) (dupSubst t a b)

  | appSup {l : Label} {a b : Term Γ (.arr A B)} {c : Term Γ A} :
      Step (.app (.sup l a b) c)
        (.dup l (shift2 c) (.sup l
          (.app (shift2 a) (.var .here))
          (.app (shift2 b) (.var (.there .here)))))

  | dupLam {l : Label} {body : Term (A :: Γ) B} {t : Term (.arr A B :: .arr A B :: Γ) τ} :
      Step (.dup l (.lam body) t)
        (.dup l (shift2 body)
          (dupSubst
            (rename (fun
              | .here           => .here
              | .there .here    => .there .here
              | .there (.there h) => .there (.there (.there h))) t)
            (.lam (.var (.there .here)))
            (.lam (.var (.there (.there (.there .here)))))))

  | dupNum {l : Label} {k : Nat} {t : Term (.nat :: .nat :: Γ) τ} :
      Step (.dup l (.num k) t) (dupSubst t (.num k) (.num k))

  | op2Add {k1 k2 : Nat} :
      Step (.op2 .add (.num k1) (.num k2)) (.num (k1 + k2))

  | op2SupL {l : Label} {op : BinOp α β γ} {a b : Term Γ α} {c : Term Γ β} :
      Step (.op2 op (.sup l a b) c)
        (.dup l (shift2 c) (.sup l
          (.op2 op (shift2 a) (.var .here))
          (.op2 op (shift2 b) (.var (.there .here)))))

  | congAppL {f f' : Term Γ (.arr A B)} {a : Term Γ A} :
      Step f f' → Step (.app f a) (.app f' a)
  | congOp2L {op : BinOp α β γ} {a a' : Term Γ α} {b : Term Γ β} :
      Step a a' → Step (.op2 op a b) (.op2 op a' b)
  | congSupL {l : Label} {a a' b : Term Γ τ} :
      Step a a' → Step (.sup l a b) (.sup l a' b)
  | congSupR {l : Label} {a b b' : Term Γ τ} :
      Step b b' → Step (.sup l a b) (.sup l a b')
  | congDupV {l : Label} {v v' : Term Γ A} {t : Term (A :: A :: Γ) τ} :
      Step v v' → Step (.dup l v t) (.dup l v' t)

-- Typed Church numeral `2` at type `(A → A) → (A → A)`
def churchTwo (A : Ty) : ClosedTerm (.arr (.arr A A) (.arr A A)) :=
  .lam (.lam
    (.app (.var (.there .here))
          (.app (.var (.there .here)) (.var .here))))

-- Example: (&A{1, 2} + &A{10, 20}) : Term [] .nat
def exSameLabelSup : ClosedTerm .nat :=
  .op2 .add
    (.sup 1 (.num 1) (.num 2))
    (.sup 1 (.num 10) (.num 20))








namespace IC

def Fin.lift (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1)
  | ⟨0, _⟩     => ⟨0, Nat.zero_lt_succ m⟩
  | ⟨i + 1, h⟩ => (ρ ⟨i, Nat.lt_of_succ_lt_succ h⟩).succ

def Fin.liftK (k : Nat) (ρ : Fin n → Fin m) : Fin (n + k) → Fin (m + k) :=
  match k with
  | 0     => ρ
  | k + 1 =>
    -- Shift n + k + 1 into m + k + 1
    fun i =>
      if h : i.val < k then
        ⟨i.val, Nat.lt_trans h (Nat.lt_add_right _ (Nat.lt_succ_self k))⟩
      else
        let inner : Fin (n + k) := ⟨i.val - k, by
          have hle : k ≤ i.val := Nat.le_of_not_lt h
          have hlt : i.val < n + k + 1 := i.isLt
          omega⟩
        let mapped := Fin.liftK k ρ inner
        ⟨mapped.val + k, by omega⟩

def rename : (Fin n → Fin m) → Term n → Term m
  | ρ, .var i        => .var (ρ i)
  | ρ, .lam body     => .lam (rename (Fin.lift ρ) body)
  | ρ, .app f a      => .app (rename ρ f) (rename ρ a)
  | ρ, .sup l a b    => .sup l (rename ρ a) (rename ρ b)
  | ρ, .dup l v body => .dup l (rename ρ v) (rename (Fin.liftK 2 ρ) body)
  | _, .num k        => .num k
  | ρ, .op2 op a b   => .op2 op (rename ρ a) (rename ρ b)
  | ρ, .pair a b     => .pair (rename ρ a) (rename ρ b)
  | _, .nil          => .nil

def shift1 (t : Term n) : Term (n + 1) :=
  rename Fin.succ t

def shiftK (k : Nat) (t : Term n) : Term (n + k) :=
  rename (fun i => ⟨i.val + k, Nat.add_lt_add_right i.isLt k⟩) t

-- Substitution map: σ i gives the replacement term (in scope m) for variable i (in scope n).
def liftSub (σ : Fin n → Term m) : Fin (n + 1) → Term (m + 1)
  | ⟨0, _⟩     => .var ⟨0, Nat.zero_lt_succ m⟩
  | ⟨i + 1, h⟩ => shift1 (σ ⟨i, Nat.lt_of_succ_lt_succ h⟩)

def liftSubK (k : Nat) (σ : Fin n → Term m) : Fin (n + k) → Term (m + k) :=
  match k with
  | 0     => σ
  | k + 1 =>
    fun i =>
      if h : i.val < k then
        .var ⟨i.val, Nat.lt_trans h (Nat.lt_add_right _ (Nat.lt_succ_self k))⟩
      else
        let inner : Fin (n + k) := ⟨i.val - k, by omega⟩
        shiftK k (liftSubK k σ inner)

def subst : (Fin n → Term m) → Term n → Term m
  | σ, .var i        => σ i
  | σ, .lam body     => .lam (subst (liftSub σ) body)
  | σ, .app f a      => .app (subst σ f) (subst σ a)
  | σ, .sup l a b    => .sup l (subst σ a) (subst σ b)
  | σ, .dup l v body => .dup l (subst σ v) (subst (liftSubK 2 σ) body)
  | _, .num k        => .num k
  | σ, .op2 op a b   => .op2 op (subst σ a) (subst σ b)
  | σ, .pair a b     => .pair (subst σ a) (subst σ b)
  | _, .nil          => .nil

-- Substitute binder 0 with `arg` in `body : Term (n + 1)` → `Term n`.
def betaSubst (body : Term (n + 1)) (arg : Term n) : Term n :=
  subst (fun
    | ⟨0, _⟩     => arg
    | ⟨i + 1, h⟩ => .var ⟨i, Nat.lt_of_succ_lt_succ h⟩) body

-- Substitute `x₀` (index 0) and `x₁` (index 1) in `body : Term (n + 2)` → `Term n`.
def dupSubst (body : Term (n + 2)) (v0 v1 : Term n) : Term n :=
  subst (fun
    | ⟨0, _⟩     => v0
    | ⟨1, _⟩     => v1
    | ⟨i + 2, h⟩ => .var ⟨i, by omega⟩) body

inductive Step : Term n → Term n → Prop where
  -- APP-LAM: (λx. body) arg  -->  body[x := arg]
  | appLam {body : Term (n + 1)} {arg : Term n} :
      Step (.app (.lam body) arg) (betaSubst body arg)

  -- DUP-SUP (same label): ! x &L= &L{a, b}; t  -->  t[x₀ := a, x₁ := b]
  | dupSupSame {l : Label} {a b : Term n} {t : Term (n + 2)} :
      Step (.dup l (.sup l a b) t) (dupSubst t a b)

  -- DUP-SUP (different labels): ! x &L= &R{a, b}; t commutes
  | dupSupDiff {l r : Label} (hne : l ≠ r) {a b : Term n} {t : Term (n + 2)} :
      Step (.dup l (.sup r a b) t)
        (.dup l (shiftK 2 a)
          (.dup l (shiftK 4 b)
            (dupSubst
              (rename (fun i =>
                if i.val < 2 then i
                else ⟨i.val + 2, by omega⟩) t)
              (.sup r (.var ⟨2, by omega⟩) (.var ⟨4, by omega⟩))
              (.sup r (.var ⟨3, by omega⟩) (.var ⟨5, by omega⟩)))))

  -- APP-SUP: (&L{a, b}) c  -->  ! x &L= c; &L{a(x₀), b(x₁)}
  | appSup {l : Label} {a b c : Term n} :
      Step (.app (.sup l a b) c)
        (.dup l c (.sup l
          (.app (shiftK 2 a) (.var ⟨0, by omega⟩))
          (.app (shiftK 2 b) (.var ⟨1, by omega⟩))))

  -- DUP-LAM: ! f &L= λx. body; t
  -- Binds two fresh escaped variables at 0 and 1, with lambda binder at 2 inside body.
  | dupLam {l : Label} {body : Term (n + 1)} {t : Term (n + 2)} :
      Step (.dup l (.lam body) t)
        (.dup l (shiftK 2 body)
          (dupSubst
            (rename (fun i =>
              if i.val < 2 then i
              else ⟨i.val + 2, by omega⟩) t)
            (.lam (.var ⟨1, by omega⟩))
            (.lam (.var ⟨3, by omega⟩))))

  -- DUP-NUM: ! x &L= k; t  -->  t[x₀ := k, x₁ := k]
  | dupNum {l : Label} {k : Nat} {t : Term (n + 2)} :
      Step (.dup l (.num k) t) (dupSubst t (.num k) (.num k))

  -- DUP-NIL: ! x &L= []; t  -->  t[x₀ := [], x₁ := []]
  | dupNil {l : Label} {t : Term (n + 2)} :
      Step (.dup l .nil t) (dupSubst t .nil .nil)

  -- DUP-PAIR: ! x &L= (h, tVal); body
  | dupPair {l : Label} {h tVal : Term n} {body : Term (n + 2)} :
      Step (.dup l (.pair h tVal) body)
        (.dup l (shiftK 2 h)
          (.dup l (shiftK 4 tVal)
            (dupSubst
              (rename (fun i =>
                if i.val < 2 then i
                else ⟨i.val + 2, by omega⟩) body)
              (.pair (.var ⟨2, by omega⟩) (.var ⟨4, by omega⟩))
              (.pair (.var ⟨3, by omega⟩) (.var ⟨5, by omega⟩)))))

  -- OP2-NUM: (k₁ + k₂)  -->  (k₁ + k₂)
  | op2Add {k1 k2 : Nat} :
      Step (.op2 .add (.num k1) (.num k2)) (.num (k1 + k2))

  -- OP2-CONS: h <> t  -->  (h, t)
  | op2Cons {h t : Term n} :
      Step (.op2 .cons h t) (.pair h t)

  -- OP2-SUP (left): (&L{a, b} + c)  -->  ! x &L= c; &L{(a + x₀), (b + x₁)}
  | op2SupL {l : Label} {op : BinOp} {a b c : Term n} :
      Step (.op2 op (.sup l a b) c)
        (.dup l c (.sup l


infix:50 " ~1> " => Step

inductive MultiStep : Term n → Term n → Prop where
  | refl (t : Term n) : MultiStep t t
  | step {t u v : Term n} : (t ~1> u) → MultiStep u v → MultiStep t v

infix:50 " ~*> " => MultiStep

theorem MultiStep.single (h : t ~1> u) : t ~*> u :=
  .step h (.refl u)

theorem MultiStep.trans {t u v : Term n} : (t ~*> u) → (u ~*> v) → (t ~*> v)
  | .refl _, h2 => h2
  | .step h1 r1, h2 => .step h1 (r1.trans h2)

section Examples

-- Helper indices in scope `n + 2`
private def v0 : Term (n + 2) := .var ⟨0, by omega⟩
private def v1 : Term (n + 2) := .var ⟨1, by omega⟩

-- Example 1: ! x &= 2; (x₀ + x₁)  -->  4
def exDupNum : ClosedTerm :=
  .dup 0 (.num 2) (.op2 .add v0 v1)

theorem exDupNum_reduces : exDupNum ~*> .num 4 := by
  unfold exDupNum v0 v1
  refine .step .dupNum ?_
  simp [dupSubst, subst]
  exact .step .op2Add (.refl _)

-- Example 2: (&A{1, 2} + &A{10, 20})  -->  &A{11, 22}
def exSameLabelSup : ClosedTerm :=
  .op2 .add (.sup 1 (.num 1) (.num 2)) (.sup 1 (.num 10) (.num 20))

theorem exSameLabelSup_reduces : exSameLabelSup ~*> .sup 1 (.num 11) (.num 22) := by
  unfold exSameLabelSup v0 v1
  refine .step .op2SupL ?_
  refine .step (.congDupV .dupNum) ?_
  -- After DUP-NUM on inner dup, outer dup has .sup 1 (.op2 .add (.num 1) (.num 10)) (.op2 .add (.num 2) (.num 20))
  simp [dupSubst, subst, shiftK, rename]
  refine .step .dupSupSame ?_
  simp [dupSubst, subst]
  refine .step (.congSupL .op2Add) ?_
  refine .step (.congSupR .op2Add) ?_
  exact .refl _

-- Example 3: Duplicating a lambda containing (2 + 2) applied to 10 and 20
-- ! F &= (λx. λy. ! z &= x; ((z₀ + z₁), y) 2); (F₀(10), F₁(20))
def sharedBody : Term 2 :=
  -- In scope 2: index 0 is y, index 1 is x
  .dup 0 (.var ⟨1, by omega⟩)
    (.pair
      (.op2 .add (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩))
      (.var ⟨2, by omega⟩))

def exSharedLambda : ClosedTerm :=
  .dup 0
    (.app (.lam (.lam sharedBody)) (.num 2))
    (.pair
      (.app (.var ⟨0, by omega⟩) (.num 10))
      (.app (.var ⟨1, by omega⟩) (.num 20)))

-- Church numeral definition: λf. λx. f (f x)
def churchTwo : ClosedTerm :=
  .lam (.lam
    (.app (.var ⟨1, by omega⟩)
          (.app (.var ⟨1, by omega⟩) (.var ⟨0, by omega⟩))))

-- Church numeral 4: λf. λx. f (f (f (f x)))
def churchFour : ClosedTerm :=
  .lam (.lam
    (.app (.var ⟨1, by omega⟩)
      (.app (.var ⟨1, by omega⟩)
        (.app (.var ⟨1, by omega⟩)
          (.app (.var ⟨1, by omega⟩) (.var ⟨0, by omega⟩))))))

-- Interaction Calculus encoding of Church 2²:
-- (λf. ! F &L= f; λx.(F₀ (F₁ x))) (λg. ! G &K= g; λy.(G₀ (G₁ y)))
def churchTwoBody : Term 2 :=
  -- index 0 is x, index 1 is f
  .dup 1 (.var ⟨1, by omega⟩)
    (.app (.var ⟨0, by omega⟩)
          (.app (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩)))

def exChurch2Pow2 : ClosedTerm :=
  .app
    (.lam (.lam churchTwoBody))
    (.lam (.lam churchTwoBody))

end Examples


---------------

-- Interaction Calculus, intrinsically typed, global names, no raw layer, no fuel.
-- Source: HVM4 docs/theory/interaction_calculus.md
set_option autoImplicit true   -- only for implicit binder names in constructor signatures

namespace IC

variable {Λ : Type}

/-! ## Types, contexts, names -/

inductive Ty where
  | nat
  | arr  (a b : Ty)
  | prod (a b : Ty)
  | list (a : Ty)
  deriving DecidableEq, Repr

infixr:25 " ⇒ " => Ty.arr

/-- Global declaration context. The head is the most recently declared name. -/
abbrev Ctx := List Ty

/-- A name declared in `Γ` with type `τ`. -/
structure Var (Γ : Ctx) (τ : Ty) where
  idx : Nat
  ok  : Γ[idx]? = some τ

/-- Name by position; the type is inferred from `Γ` by `rfl`. -/
def nm {Γ : Ctx} {τ : Ty} (i : Nat) (h : Γ[i]? = some τ := by rfl) : Var Γ τ := ⟨i, h⟩

/-- Weakening along freshly declared names (they are consed at the front). -/
def Var.wk {Γ : Ctx} {τ : Ty} (Δ : Ctx) (x : Var Γ τ) : Var (Δ ++ Γ) τ :=
  ⟨x.idx + Δ.length, by
    rw [List.getElem?_append_right (Nat.le_add_left _ _)]
    simpa using x.ok⟩

/-- Equal indices force equal types. -/
theorem Var.ty_eq {Γ : Ctx} {A τ : Ty} {x : Var Γ A} {y : Var Γ τ}
    (h : y.idx = x.idx) : τ = A := by
  have h1 := y.ok
  have h2 := x.ok
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

inductive Op where
  | add | sub | mul
  deriving DecidableEq, Repr

def Op.eval : Op → Nat → Nat → Nat
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-! ## Terms: intrinsically typed, `Γ` declares every name that may occur

`dup l x₀ x₁ v t` is `! x &l= v; t`. There is no unlabeled form. -/

inductive Term (Λ : Type) (Γ : Ctx) : Ty → Type where
  | var  {τ : Ty}     : Var Γ τ → Term Λ Γ τ
  | lam  {A B : Ty}   : Var Γ A → Term Λ Γ B → Term Λ Γ (A ⇒ B)
  | app  {A B : Ty}   : Term Λ Γ (A ⇒ B) → Term Λ Γ A → Term Λ Γ B
  | sup  {τ : Ty}     : Λ → Term Λ Γ τ → Term Λ Γ τ → Term Λ Γ τ
  | dup  {A τ : Ty}   : Λ → Var Γ A → Var Γ A → Term Λ Γ A → Term Λ Γ τ → Term Λ Γ τ
  | num               : Nat → Term Λ Γ .nat
  | op2               : Op → Term Λ Γ .nat → Term Λ Γ .nat → Term Λ Γ .nat
  | nil  {A : Ty}     : Term Λ Γ (.list A)
  | cons {A : Ty}     : Term Λ Γ A → Term Λ Γ (.list A) → Term Λ Γ (.list A)
  | pair {A B : Ty}   : Term Λ Γ A → Term Λ Γ B → Term Λ Γ (.prod A B)

def Term.wk {Γ : Ctx} (Δ : Ctx) : {τ : Ty} → Term Λ Γ τ → Term Λ (Δ ++ Γ) τ
  | _, .var x           => .var (x.wk Δ)
  | _, .lam x b         => .lam (x.wk Δ) (b.wk Δ)
  | _, .app f a         => .app (f.wk Δ) (a.wk Δ)
  | _, .sup l a b       => .sup l (a.wk Δ) (b.wk Δ)
  | _, .dup l x0 x1 w t => .dup l (x0.wk Δ) (x1.wk Δ) (w.wk Δ) (t.wk Δ)
  | _, .num k           => .num k
  | _, .op2 o a b       => .op2 o (a.wk Δ) (b.wk Δ)
  | _, .nil             => .nil
  | _, .cons a b        => .cons (a.wk Δ) (b.wk Δ)
  | _, .pair a b        => .pair (a.wk Δ) (b.wk Δ)

/-- Relabel; for injective `f` this preserves zip / cross-product behaviour. -/
def Term.mapLabel {Λ' : Type} (f : Λ → Λ') {Γ : Ctx} : {τ : Ty} → Term Λ Γ τ → Term Λ' Γ τ
  | _, .var x           => .var x
  | _, .lam x b         => .lam x (b.mapLabel f)
  | _, .app g a         => .app (g.mapLabel f) (a.mapLabel f)
  | _, .sup l a b       => .sup (f l) (a.mapLabel f) (b.mapLabel f)
  | _, .dup l x0 x1 w t => .dup (f l) x0 x1 (w.mapLabel f) (t.mapLabel f)
  | _, .num k           => .num k
  | _, .op2 o a b       => .op2 o (a.mapLabel f) (b.mapLabel f)
  | _, .nil             => .nil
  | _, .cons a b        => .cons (a.mapLabel f) (b.mapLabel f)
  | _, .pair a b        => .pair (a.mapLabel f) (b.mapLabel f)

/-! ### Linearity (the one extrinsic invariant): each name has ≤ 1 binder and ≤ 1 use -/

def Term.uses {Γ : Ctx} (i : Nat) : {τ : Ty} → Term Λ Γ τ → Nat
  | _, .var x           => if x.idx = i then 1 else 0
  | _, .lam _ b         => b.uses i
  | _, .app f a         => f.uses i + a.uses i
  | _, .sup _ a b       => a.uses i + b.uses i
  | _, .dup _ _ _ w t   => w.uses i + t.uses i
  | _, .num _           => 0
  | _, .op2 _ a b       => a.uses i + b.uses i
  | _, .nil             => 0
  | _, .cons a b        => a.uses i + b.uses i
  | _, .pair a b        => a.uses i + b.uses i

def Term.binders {Γ : Ctx} (i : Nat) : {τ : Ty} → Term Λ Γ τ → Nat
  | _, .var _           => 0
  | _, .lam x b         => (if x.idx = i then 1 else 0) + b.binders i
  | _, .app f a         => f.binders i + a.binders i
  | _, .sup _ a b       => a.binders i + b.binders i
  | _, .dup _ x0 x1 w t =>
      (if x0.idx = i then 1 else 0) + (if x1.idx = i then 1 else 0) + w.binders i + t.binders i
  | _, .num _           => 0
  | _, .op2 _ a b       => a.binders i + b.binders i
  | _, .nil             => 0
  | _, .cons a b        => a.binders i + b.binders i
  | _, .pair a b        => a.binders i + b.binders i

def Term.Linear {Γ : Ctx} {τ : Ty} (t : Term Λ Γ τ) : Prop :=
  ∀ i, t.uses i ≤ 1 ∧ t.binders i ≤ 1

/-- Well-formed nets: the type that reduction is meant to preserve. -/
def Net (Λ : Type) (Γ : Ctx) (τ : Ty) := { t : Term Λ Γ τ // t.Linear }

/-! ## Global substitution `x ← v`: no binders to cross, so nothing to shift -/

def Term.subst1 {Γ : Ctx} {A : Ty} (x : Var Γ A) (a : Term Λ Γ A) :
    {τ : Ty} → Term Λ Γ τ → Term Λ Γ τ
  | _, .var y =>
      if h : y.idx = x.idx then
        cast (congrArg (Term Λ Γ) (Var.ty_eq h).symm) a
      else .var y
  | _, .lam y b         => .lam y (b.subst1 x a)
  | _, .app f c         => .app (f.subst1 x a) (c.subst1 x a)
  | _, .sup l p q       => .sup l (p.subst1 x a) (q.subst1 x a)
  | _, .dup l x0 x1 w t => .dup l x0 x1 (w.subst1 x a) (t.subst1 x a)
  | _, .num k           => .num k
  | _, .op2 o p q       => .op2 o (p.subst1 x a) (q.subst1 x a)
  | _, .nil             => .nil
  | _, .cons p q        => .cons (p.subst1 x a) (q.subst1 x a)
  | _, .pair p q        => .pair (p.subst1 x a) (q.subst1 x a)

/-- A typed binding `x ← v`. -/
structure Bind (Λ : Type) (Γ : Ctx) where
  {A : Ty}
  x : Var Γ A
  v : Term Λ Γ A

def Term.substAll {Γ : Ctx} {τ : Ty} : List (Bind Λ Γ) → Term Λ Γ τ → Term Λ Γ τ
  | [],      t => t
  | b :: bs, t => Term.substAll bs (t.subst1 b.x b.v)

/-- A rewrite: the new subterm, plus bindings to apply to the whole net. -/
structure Out (Λ : Type) (Γ : Ctx) (τ : Ty) where
  term  : Term Λ Γ τ
  binds : List (Bind Λ Γ)

/-- A rewrite result: fresh names `Δ` (types only) and an output living in `Δ ++ Γ`. -/
abbrev Res (Λ : Type) (Γ : Ctx) (τ : Ty) := Σ Δ : Ctx, Out Λ (Δ ++ Γ) τ

def Res.map {Γ : Ctx} {σ τ : Ty} (r : Res Λ Γ σ)
    (g : ∀ Δ : Ctx, Term Λ (Δ ++ Γ) σ → Term Λ (Δ ++ Γ) τ) : Res Λ Γ τ :=
  ⟨r.1, ⟨g r.1 r.2.term, r.2.binds⟩⟩

def Res.apply {Γ : Ctx} {τ : Ty} (r : Res Λ Γ τ) : Σ Δ : Ctx, Term Λ (Δ ++ Γ) τ :=
  ⟨r.1, r.2.term.substAll r.2.binds⟩

/-! ## Rule bodies, shared by the relation and the executable
Labels are only reused, never invented. Fresh names are typed by `Δ`. -/

abbrev Fresh2 (A : Ty) : Ctx := [A, A]
abbrev Fresh4 (X Y : Ty) : Ctx := [X, X, Y, Y]

namespace Rule
variable {Γ : Ctx}

/-- APP-SUP / OP2-SUP: `! y &l= c; &l{F a y₀, F b y₁}` -/
def distrib {X A τ : Ty} (l : Λ) (c : Term Λ Γ A) (a b : Term Λ Γ X)
    (F : ∀ {Γ' : Ctx}, Term Λ Γ' X → Term Λ Γ' A → Term Λ Γ' τ) : Res Λ Γ τ :=
  ⟨Fresh2 A,
   { term  := .dup l ⟨0, rfl⟩ ⟨1, rfl⟩ (c.wk (Fresh2 A))
                (.sup l (F (a.wk (Fresh2 A)) (.var ⟨0, rfl⟩))
                        (F (b.wk (Fresh2 A)) (.var ⟨1, rfl⟩)))
     binds := [] }⟩

/-- DUP-SUP (same label) and the atom rules: `x₀ ← a`, `x₁ ← b`. -/
def annihilate {A τ : Ty} (x0 x1 : Var Γ A) (a b : Term Λ Γ A) (t : Term Λ Γ τ) : Res Λ Γ τ :=
  ⟨[], ⟨t, [Bind.mk x0 a, Bind.mk x1 b]⟩⟩

/-- Binary constructor `mk` (`sup r` with `r ≠ l`, `cons`, `pair`):
    `! A &l= a; ! B &l= b; x₀ ← mk A₀ B₀; x₁ ← mk A₁ B₁; t` -/
def split2 {X Y A τ : Ty} (l : Λ) (x0 x1 : Var Γ A)
    (mk : ∀ {Γ' : Ctx}, Term Λ Γ' X → Term Λ Γ' Y → Term Λ Γ' A)
    (a : Term Λ Γ X) (b : Term Λ Γ Y) (t : Term Λ Γ τ) : Res Λ Γ τ :=
  ⟨Fresh4 X Y,
   { term  := .dup l ⟨0, rfl⟩ ⟨1, rfl⟩ (a.wk (Fresh4 X Y))
                (.dup l ⟨2, rfl⟩ ⟨3, rfl⟩ (b.wk (Fresh4 X Y)) (t.wk (Fresh4 X Y)))
     binds := [ Bind.mk (x0.wk (Fresh4 X Y)) (mk (.var ⟨0, rfl⟩) (.var ⟨2, rfl⟩)),
                Bind.mk (x1.wk (Fresh4 X Y)) (mk (.var ⟨1, rfl⟩) (.var ⟨3, rfl⟩)) ] }⟩

/-- DUP-LAM: `f₀ ← λ$X0.B₀`, `f₁ ← λ$X1.B₁`, `y ← &l{$X0,$X1}`, `! B &l= body; t`.
    The escaping `$X0`, `$X1` are ordinary global names `0`, `1` of the fresh block;
    `B₀`, `B₁` are `2`, `3`. -/
def dupLam {A B τ : Ty} (l : Λ) (f0 f1 : Var Γ (A ⇒ B)) (y : Var Γ A)
    (body : Term Λ Γ B) (t : Term Λ Γ τ) : Res Λ Γ τ :=
  ⟨Fresh4 A B,
   { term  := .dup l ⟨2, rfl⟩ ⟨3, rfl⟩ (body.wk (Fresh4 A B)) (t.wk (Fresh4 A B))
     binds := [ Bind.mk (f0.wk (Fresh4 A B)) (.lam ⟨0, rfl⟩ (.var ⟨2, rfl⟩)),
                Bind.mk (f1.wk (Fresh4 A B)) (.lam ⟨1, rfl⟩ (.var ⟨3, rfl⟩)),
                Bind.mk (y.wk  (Fresh4 A B)) (.sup l (.var ⟨0, rfl⟩) (.var ⟨1, rfl⟩)) ] }⟩

end Rule

/-! ## The semantics as a relation: `Rw t r` rewrites somewhere inside `t` -/

inductive Rw : {Γ : Ctx} → {τ : Ty} → Term Λ Γ τ → Res Λ Γ τ → Prop where
  -- the four core interactions
  | appLam {x : Var Γ A} {b : Term Λ Γ B} {a : Term Λ Γ A} :
      Rw (.app (.lam x b) a) ⟨[], ⟨b, [Bind.mk x a]⟩⟩
  | appSup {l : Λ} {a b : Term Λ Γ (A ⇒ B)} {c : Term Λ Γ A} :
      Rw (.app (.sup l a b) c) (Rule.distrib l c a b fun f y => .app f y)
  | dupSupSame {l : Λ} {x0 x1 : Var Γ A} {a b : Term Λ Γ A} {t : Term Λ Γ τ} :
      Rw (.dup l x0 x1 (.sup l a b) t) (Rule.annihilate x0 x1 a b t)
  | dupSupDiff {l r : Λ} (hne : l ≠ r) {x0 x1 : Var Γ A} {a b : Term Λ Γ A} {t : Term Λ Γ τ} :
      Rw (.dup l x0 x1 (.sup r a b) t) (Rule.split2 l x0 x1 (fun p q => .sup r p q) a b t)
  | dupLam {l : Λ} {f0 f1 : Var Γ (A ⇒ B)} {y : Var Γ A} {body : Term Λ Γ B} {t : Term Λ Γ τ} :
      Rw (.dup l f0 f1 (.lam y body) t) (Rule.dupLam l f0 f1 y body t)
  -- numbers
  | op2Num {o : Op} {a b : Nat} :
      Rw (Γ := Γ) (.op2 o (.num a) (.num b)) ⟨[], ⟨.num (o.eval a b), []⟩⟩
  | op2SupL {o : Op} {l : Λ} {a b c : Term Λ Γ .nat} :
      Rw (.op2 o (.sup l a b) c) (Rule.distrib l c a b fun s y => .op2 o s y)
  | op2SupR {o : Op} {k : Nat} {l : Λ} {a b : Term Λ Γ .nat} :
      Rw (.op2 o (.num k) (.sup l a b)) (Rule.distrib l (.num k) a b fun s y => .op2 o y s)
  | dupNum {l : Λ} {x0 x1 : Var Γ .nat} {k : Nat} {t : Term Λ Γ τ} :
      Rw (.dup l x0 x1 (.num k) t) (Rule.annihilate x0 x1 (.num k) (.num k) t)
  -- lists and pairs
  | dupNil {l : Λ} {x0 x1 : Var Γ (.list A)} {t : Term Λ Γ τ} :
      Rw (.dup l x0 x1 .nil t) (Rule.annihilate x0 x1 .nil .nil t)
  | dupCons {l : Λ} {x0 x1 : Var Γ (.list A)} {a : Term Λ Γ A} {b : Term Λ Γ (.list A)}
      {t : Term Λ Γ τ} :
      Rw (.dup l x0 x1 (.cons a b) t) (Rule.split2 l x0 x1 (fun p q => .cons p q) a b t)
  | dupPair {l : Λ} {x0 x1 : Var Γ (.prod A B)} {a : Term Λ Γ A} {b : Term Λ Γ B}
      {t : Term Λ Γ τ} :
      Rw (.dup l x0 x1 (.pair a b) t) (Rule.split2 l x0 x1 (fun p q => .pair p q) a b t)
  -- congruence, including under binders (siblings are weakened by the fresh names)
  | lam  {x : Var Γ A} {b : Term Λ Γ B} {r : Res Λ Γ B} :
      Rw b r → Rw (.lam x b) (r.map fun Δ b' => .lam (x.wk Δ) b')
  | appL {a : Term Λ Γ (A ⇒ B)} {b : Term Λ Γ A} {r : Res Λ Γ (A ⇒ B)} :
      Rw a r → Rw (.app a b) (r.map fun Δ a' => .app a' (b.wk Δ))
  | appR {a : Term Λ Γ (A ⇒ B)} {b : Term Λ Γ A} {r : Res Λ Γ A} :
      Rw b r → Rw (.app a b) (r.map fun Δ b' => .app (a.wk Δ) b')
  | supL {l : Λ} {a b : Term Λ Γ τ} {r : Res Λ Γ τ} :
      Rw a r → Rw (.sup l a b) (r.map fun Δ a' => .sup l a' (b.wk Δ))
  | supR {l : Λ} {a b : Term Λ Γ τ} {r : Res Λ Γ τ} :
      Rw b r → Rw (.sup l a b) (r.map fun Δ b' => .sup l (a.wk Δ) b')
  | dupV {l : Λ} {x0 x1 : Var Γ A} {w : Term Λ Γ A} {t : Term Λ Γ τ} {r : Res Λ Γ A} :
      Rw w r → Rw (.dup l x0 x1 w t)
        (r.map fun Δ w' => .dup l (x0.wk Δ) (x1.wk Δ) w' (t.wk Δ))
  | dupT {l : Λ} {x0 x1 : Var Γ A} {w : Term Λ Γ A} {t : Term Λ Γ τ} {r : Res Λ Γ τ} :
      Rw t r → Rw (.dup l x0 x1 w t)
        (r.map fun Δ t' => .dup l (x0.wk Δ) (x1.wk Δ) (w.wk Δ) t')
  | op2L {o : Op} {a b : Term Λ Γ .nat} {r : Res Λ Γ .nat} :
      Rw a r → Rw (.op2 o a b) (r.map fun Δ a' => .op2 o a' (b.wk Δ))
  | op2R {o : Op} {a b : Term Λ Γ .nat} {r : Res Λ Γ .nat} :
      Rw b r → Rw (.op2 o a b) (r.map fun Δ b' => .op2 o (a.wk Δ) b')
  | consL {a : Term Λ Γ A} {b : Term Λ Γ (.list A)} {r : Res Λ Γ A} :
      Rw a r → Rw (.cons a b) (r.map fun Δ a' => .cons a' (b.wk Δ))
  | consR {a : Term Λ Γ A} {b : Term Λ Γ (.list A)} {r : Res Λ Γ (.list A)} :
      Rw b r → Rw (.cons a b) (r.map fun Δ b' => .cons (a.wk Δ) b')
  | pairL {a : Term Λ Γ A} {b : Term Λ Γ B} {r : Res Λ Γ A} :
      Rw a r → Rw (.pair a b) (r.map fun Δ a' => .pair a' (b.wk Δ))
  | pairR {a : Term Λ Γ A} {b : Term Λ Γ B} {r : Res Λ Γ B} :
      Rw b r → Rw (.pair a b) (r.map fun Δ b' => .pair (a.wk Δ) b')

/-- One interaction on the whole net: rewrite, then apply `x ← v` globally. -/
def Step {Γ : Ctx} {τ : Ty} (t : Term Λ Γ τ) (u : Σ Δ : Ctx, Term Λ (Δ ++ Γ) τ) : Prop :=
  ∃ r : Res Λ Γ τ, Rw t r ∧ u = r.apply

/-- Many steps. The target context is a free index: it only ever grows by fresh names. -/
inductive Steps : {Γ Γ' : Ctx} → {τ : Ty} → Term Λ Γ τ → Term Λ Γ' τ → Prop where
  | refl {t : Term Λ Γ τ} : Steps t t
  | step {Δ : Ctx} {t : Term Λ Γ τ} {u : Term Λ (Δ ++ Γ) τ} {w : Term Λ Γ' τ} :
      Step t ⟨Δ, u⟩ → Steps u w → Steps t w

/-! ## Executable one-step function: total, structural, no fuel -/

def head? [DecidableEq Λ] {Γ : Ctx} : {τ : Ty} → Term Λ Γ τ → Option (Res Λ Γ τ)
  | _, .app (.lam x b) a            => some ⟨[], ⟨b, [Bind.mk x a]⟩⟩
  | _, .app (.sup l a b) c          => some (Rule.distrib l c a b fun f y => .app f y)
  | _, .op2 o (.num a) (.num b)     => some ⟨[], ⟨.num (o.eval a b), []⟩⟩
  | _, .op2 o (.sup l a b) c        => some (Rule.distrib l c a b fun s y => .op2 o s y)
  | _, .op2 o (.num k) (.sup l a b) => some (Rule.distrib l (.num k) a b fun s y => .op2 o y s)
  | _, .dup l x0 x1 (.sup r a b) t  =>
      if l = r then some (Rule.annihilate x0 x1 a b t)
      else some (Rule.split2 l x0 x1 (fun p q => .sup r p q) a b t)
  | _, .dup l x0 x1 (.lam y b) t    => some (Rule.dupLam l x0 x1 y b t)
  | _, .dup _ x0 x1 (.num k) t      => some (Rule.annihilate x0 x1 (.num k) (.num k) t)
  | _, .dup _ x0 x1 .nil t          => some (Rule.annihilate x0 x1 .nil .nil t)
  | _, .dup l x0 x1 (.cons a b) t   => some (Rule.split2 l x0 x1 (fun p q => .cons p q) a b t)
  | _, .dup l x0 x1 (.pair a b) t   => some (Rule.split2 l x0 x1 (fun p q => .pair p q) a b t)
  | _, _                            => none

/-- Outermost-first search for a redex anywhere, under binders included. -/
def rw? [DecidableEq Λ] {Γ : Ctx} : {τ : Ty} → Term Λ Γ τ → Option (Res Λ Γ τ)
  | _, .var _ => none
  | _, .num _ => none
  | _, .nil   => none
  | _, .lam x b => (rw? b).map fun r => r.map fun Δ b' => .lam (x.wk Δ) b'
  | _, t@(.app a b) =>
      head? t
        <|> (rw? a).map (fun r => r.map fun Δ a' => .app a' (b.wk Δ))
        <|> (rw? b).map (fun r => r.map fun Δ b' => .app (a.wk Δ) b')
  | _, .sup l a b =>
      (rw? a).map (fun r => r.map fun Δ a' => .sup l a' (b.wk Δ))
        <|> (rw? b).map (fun r => r.map fun Δ b' => .sup l (a.wk Δ) b')
  | _, t@(.dup l x0 x1 w u) =>
      head? t
        <|> (rw? w).map (fun r => r.map fun Δ w' => .dup l (x0.wk Δ) (x1.wk Δ) w' (u.wk Δ))
        <|> (rw? u).map (fun r => r.map fun Δ u' => .dup l (x0.wk Δ) (x1.wk Δ) (w.wk Δ) u')
  | _, t@(.op2 o a b) =>
      head? t
        <|> (rw? a).map (fun r => r.map fun Δ a' => .op2 o a' (b.wk Δ))
        <|> (rw? b).map (fun r => r.map fun Δ b' => .op2 o (a.wk Δ) b')
  | _, .cons a b =>
      (rw? a).map (fun r => r.map fun Δ a' => .cons a' (b.wk Δ))
        <|> (rw? b).map (fun r => r.map fun Δ b' => .cons (a.wk Δ) b')
  | _, .pair a b =>
      (rw? a).map (fun r => r.map fun Δ a' => .pair a' (b.wk Δ))
        <|> (rw? b).map (fun r => r.map fun Δ b' => .pair (a.wk Δ) b')

def step? [DecidableEq Λ] {Γ : Ctx} {τ : Ty} (t : Term Λ Γ τ) :
    Option (Σ Δ : Ctx, Term Λ (Δ ++ Γ) τ) :=
  (rw? t).map Res.apply

/-- Big-step normalisation as a derivation, which replaces fuel.
    `Eval t w`: `t` reaches the normal form `w`. -/
inductive Eval [DecidableEq Λ] : {Γ Γ' : Ctx} → {τ : Ty} → Term Λ Γ τ → Term Λ Γ' τ → Prop where
  | done {t : Term Λ Γ τ} : step? t = none → Eval t t
  | next {Δ : Ctx} {t : Term Λ Γ τ} {u : Term Λ (Δ ++ Γ) τ} {w : Term Λ Γ' τ} :
      step? t = some ⟨Δ, u⟩ → Eval u w → Eval t w

/-- Results are context-polymorphic constants, because the final context has extra fresh names. -/
def Reaches [DecidableEq Λ] {Γ : Ctx} {τ : Ty} (t : Term Λ Γ τ)
    (w : ∀ {Γ' : Ctx}, Term Λ Γ' τ) : Prop :=
  ∃ Γ' : Ctx, Eval t (w (Γ' := Γ'))

/-- For `#eval` only. `partial` because normalisation is undecidable; `Option` only
    satisfies the inhabitation check, and the result is always `some`. -/
partial def run [DecidableEq Λ] {Γ : Ctx} {τ : Ty} (t : Term Λ Γ τ) :
    Option (Σ Γ' : Ctx, Term Λ Γ' τ) :=
  match step? t with
  | some ⟨_, u⟩ => run u
  | none        => some ⟨Γ, t⟩

def Term.pp [ToString Λ] {Γ : Ctx} : {τ : Ty} → Term Λ Γ τ → String
  | _, .var x           => "x" ++ toString x.idx
  | _, .lam x b         => "λx" ++ toString x.idx ++ "." ++ b.pp
  | _, .app f a         => "(" ++ f.pp ++ " " ++ a.pp ++ ")"
  | _, .sup l a b       => "&" ++ toString l ++ "{" ++ a.pp ++ ", " ++ b.pp ++ "}"
  | _, .dup l x0 x1 w t => "! x" ++ toString x0.idx ++ "/x" ++ toString x1.idx ++ " &"
                             ++ toString l ++ "= " ++ w.pp ++ "; " ++ t.pp
  | _, .num k           => toString k
  | _, .op2 o a b       =>
      let s := match o with | .add => "+" | .sub => "-" | .mul => "*"
      "(" ++ a.pp ++ " " ++ s ++ " " ++ b.pp ++ ")"
  | _, .nil             => "[]"
  | _, .cons a b        => "(" ++ a.pp ++ " :: " ++ b.pp ++ ")"
  | _, .pair a b        => "(" ++ a.pp ++ ", " ++ b.pp ++ ")"

end IC

/-! ## Macros: global names declared in a typed header.
`ic[ (x₀ x₁ : nat) (f : nat ⇒ nat) ⊢ term ]` declares `Γ = [nat, nat, nat ⇒ nat]`.
Binders are `λ x . t` and `! x &L= v ; t` (which binds the declared names `x₀`, `x₁`).
A label is mandatory in `&L{a, b}` and in `! x &L= …`; there is no unlabeled form. -/

declare_syntax_cat ic
declare_syntax_cat icdecl

syntax ident                                      : ic
syntax num                                        : ic
syntax "(" ic ")"                                 : ic
syntax "(" ic "," ic ")"                          : ic
syntax "λ" ident " . " ic                         : ic
syntax:60 ic:60 ic:61                             : ic
syntax:50 ic:50 " + " ic:51                       : ic
syntax "&" ident "{" ic "," ic "}"                : ic
syntax "!" ident "&" ident "=" ic ";" ic          : ic
syntax "[" "]"                                    : ic
syntax:45 ic:46 " :: " ic:45                      : ic
syntax "(" ident+ " : " term ")"                  : icdecl
syntax "ic[" icdecl* " ⊢ " ic "]"                 : term

namespace IC.Syntax
open Lean

def idxOf (env : Array Name) (x : Name) : Option Nat := env.findIdx? (· == x)

partial def toTerm (env : Array Name) (stx : TSyntax `ic) : MacroM (TSyntax `term) := do
  let name (x : TSyntax `ident) (sfx : String := "") : MacroM (TSyntax `term) := do
    let n := Name.mkSimple (x.getId.toString ++ sfx)
    match idxOf env n with
    | some i => `(IC.nm $(Syntax.mkNumLit (toString i)))
    | none   => Macro.throwErrorAt x s!"undeclared name {n}"
  match stx with
  | `(ic| $x:ident) => do `(IC.Term.var $(← name x))
  | `(ic| $n:num) => `(IC.Term.num $n)
  | `(ic| ($t:ic)) => toTerm env t
  | `(ic| ($a:ic, $b:ic)) => do `(IC.Term.pair $(← toTerm env a) $(← toTerm env b))
  | `(ic| λ $x:ident . $b:ic) => do `(IC.Term.lam $(← name x) $(← toTerm env b))
  | `(ic| & $l:ident { $a:ic , $b:ic }) => do
      `(IC.Term.sup $l $(← toTerm env a) $(← toTerm env b))
  | `(ic| ! $x:ident & $l:ident = $w:ic ; $t:ic) => do
      `(IC.Term.dup $l $(← name x "₀") $(← name x "₁") $(← toTerm env w) $(← toTerm env t))
  | `(ic| [ ]) => `(IC.Term.nil)
  | `(ic| $a:ic :: $b:ic) => do `(IC.Term.cons $(← toTerm env a) $(← toTerm env b))
  | `(ic| $a:ic + $b:ic) => do
      `(IC.Term.op2 IC.Op.add $(← toTerm env a) $(← toTerm env b))
  | `(ic| $f:ic $a:ic) => do `(IC.Term.app $(← toTerm env f) $(← toTerm env a))
  | _ => Macro.throwUnsupported

end IC.Syntax

open Lean in
macro_rules
  | `(ic[ $ds:icdecl* ⊢ $t:ic ]) => do
      let mut env : Array Name := #[]
      let mut tys : Array (TSyntax `term) := #[]
      for d in ds do
        match d with
        | `(icdecl| ($xs:ident* : $ty:term)) =>
            for x in xs do
              env := env.push x.getId
              tys := tys.push ty
        | _ => Macro.throwUnsupported
      let body ← IC.Syntax.toTerm env t
      `(($body : IC.Term _ ([$tys,*] : IC.Ctx) _))

/-! ## Examples from the MD -/

namespace IC.Examples
open IC Ty

inductive Lab where
  | U | A | B | K | L
  deriving DecidableEq, Repr

instance : ToString Lab := ⟨fun l => reprStr l⟩
open Lab

macro "ic_eval" : tactic =>
  `(tactic| repeat (first | exact IC.Eval.done rfl | refine IC.Eval.next rfl ?_))

set_option maxRecDepth 100000

-- ! x &U= 2; (x₀ + x₁)  ⇒  4
def exDupNum := ic[ (x₀ x₁ : nat) ⊢ ! x &U= 2 ; x₀ + x₁ ]
theorem exDupNum_ok : Reaches exDupNum (.num 4) := ⟨_, by ic_eval⟩

-- (&A{1, 2} + 10)  ⇒  &A{11, 12}
def exOp2Sup := ic[ ⊢ &A{1, 2} + 10 ]
theorem exOp2Sup_ok : Reaches exOp2Sup (.sup A (.num 11) (.num 12)) := ⟨_, by ic_eval⟩

-- ! x &U= &U{1, 2}; (x₀ + x₁)  ⇒  3     (same label: annihilate)
def exDupSup := ic[ (x₀ x₁ : nat) ⊢ ! x &U= &U{1, 2} ; x₀ + x₁ ]
theorem exDupSup_ok : Reaches exDupSup (.num 3) := ⟨_, by ic_eval⟩

-- ! f &U= λy.(y + 1); (f₀ 10, f₁ 20)  ⇒  (11, 21)     (DUP-LAM: `y` escapes via a global name)
def exDupLam := ic[ (y : nat) (f₀ f₁ : nat ⇒ nat) ⊢ ! f &U= (λ y . y + 1) ; (f₀ 10, f₁ 20) ]
theorem exDupLam_ok : Reaches exDupLam (.pair (.num 11) (.num 21)) := ⟨_, by ic_eval⟩

-- (&A{1, 2} + &A{10, 20})  ⇒  &A{11, 22}     (same label: zip)
def exZip := ic[ ⊢ &A{1, 2} + &A{10, 20} ]
theorem exZip_ok : Reaches exZip (.sup A (.num 11) (.num 22)) := ⟨_, by ic_eval⟩

-- (&A{1, 2} + &B{10, 20})  ⇒  &A{&B{11, 21}, &B{12, 22}}     (different labels: cross product)
def exCross := ic[ ⊢ &A{1, 2} + &B{10, 20} ]
theorem exCross_ok :
    Reaches exCross (.sup A (.sup B (.num 11) (.num 21)) (.sup B (.num 12) (.num 22))) :=
  ⟨_, by ic_eval⟩

-- ! x &U= [1, 2]; (x₀, x₁)  ⇒  ([1, 2], [1, 2])     (DUP-CTR, layer by layer)
def exDupList := ic[ (x₀ x₁ : list nat) ⊢ ! x &U= (1 :: 2 :: []) ; (x₀, x₁) ]
theorem exDupList_ok :
    Reaches exDupList
      (.pair (.cons (.num 1) (.cons (.num 2) .nil)) (.cons (.num 1) (.cons (.num 2) .nil))) :=
  ⟨_, by ic_eval⟩

-- Optimal sharing: `(2 + 2)` is computed once although the λ is duplicated.
-- ! F &U= ((λx. λy. ! z &U= x; (z₀ + z₁, y)) 2); (F₀ 10, F₁ 20)  ⇒  ((4, 10), (4, 20))
def exShared :=
  ic[ (x y z₀ z₁ : nat) (F₀ F₁ : nat ⇒ prod nat nat) ⊢
        ! F &U= ((λ x . λ y . ! z &U= x ; (z₀ + z₁, y)) 2) ; (F₀ 10, F₁ 20) ]
theorem exShared_ok :
    Reaches exShared (.pair (.pair (.num 4) (.num 10)) (.pair (.num 4) (.num 20))) :=
  ⟨_, by ic_eval⟩

-- Church 2² applied to succ and 0  ⇒  4. The two numerals use different labels (L ≠ K)
-- and distinct names, as global scoping requires.
abbrev NN : Ty := nat ⇒ nat
def exChurch :=
  ic[ (f F₀ F₁ : NN ⇒ NN) (x : NN) (g G₀ G₁ : NN) (y n : nat) ⊢
        (((λ f . ! F &L= f ; λ x . F₀ (F₁ x))
          (λ g . ! G &K= g ; λ y . G₀ (G₁ y)))
          (λ n . n + 1)) 0 ]
theorem exChurch_ok : Reaches exChurch (.num 4) := ⟨_, by ic_eval⟩

-- Interactive exploration:
#eval (run exCross).map fun ⟨_, w⟩ => w.pp

end IC.Examples
