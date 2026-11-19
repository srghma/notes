-- https://github.com/HigherOrderCO/HVM4/blob/main/docs/theory/interaction_calculus.md

-- Interaction Calculus formalized in Lean 4 with intrinsically scoped terms (Term n).

abbrev Label := Nat

inductive BinOp where
  | add
  | cons
  deriving DecidableEq, Repr

inductive Term : Nat → Type where
  | var  : Fin n → Term n
  | lam  : Term (n + 1) → Term n
  | app  : Term n → Term n → Term n
  | sup  : Label → Term n → Term n → Term n
  | dup  : Label → Term n → Term (n + 2) → Term n
  | num  : Nat → Term n
  | op2  : BinOp → Term n → Term n → Term n
  | pair : Term n → Term n → Term n
  | nil  : Term n
  deriving Repr

abbrev ClosedTerm := Term 0


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
          (.op2 op (shiftK 2 a) (.var ⟨0, by omega⟩))
          (.op2 op (shiftK 2 b) (.var ⟨1, by omega⟩))))

  -- Congruence rules for evaluation under constructors / binders
  | congAppL {f f' a : Term n} : Step f f' → Step (.app f a) (.app f' a)
  | congAppR {f a a' : Term n} : Step a a' → Step (.app f a) (.app f a')
  | congOp2L {op : BinOp} {a a' b : Term n} : Step a a' → Step (.op2 op a b) (.op2 op a' b)
  | congOp2R {op : BinOp} {a b b' : Term n} : Step b b' → Step (.op2 op a b) (.op2 op a b')
  | congSupL {l : Label} {a a' b : Term n} : Step a a' → Step (.sup l a b) (.sup l a' b)
  | congSupR {l : Label} {a b b' : Term n} : Step b b' → Step (.sup l a b) (.sup l a b')
  | congDupV {l : Label} {v v' : Term n} {t : Term (n + 2)} :
      Step v v' → Step (.dup l v t) (.dup l v' t)
  | congDupB {l : Label} {v : Term n} {t t' : Term (n + 2)} :
      Step t t' → Step (.dup l v t) (.dup l v t')
  | congLam {body body' : Term (n + 1)} :
      Step body body' → Step (.lam body) (.lam body')

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
