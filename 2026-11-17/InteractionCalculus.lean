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
