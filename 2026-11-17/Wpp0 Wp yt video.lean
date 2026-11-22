-- https://youtu.be/lXt8_cPnRF0?si=MtEbLnXu5Bm-7s8T

abbrev var := String
abbrev valuation := List (var × Nat)

def lookup (x : var) : valuation → Option Nat
  | [] => none
  | (y, n) :: v' => if x = y then some n else lookup x v'

inductive arith where
  | Const (n : Nat)
  | Var (x : var)
  | Minus (e1 e2 : arith)
  | Times (e1 e2 : arith)
  deriving DecidableEq

inductive cmd where
  | Skip
  | Assign (x : var) (e : arith)
  | Sequence (c1 c2 : cmd)
  | Repeat (e_count : arith) (body : cmd)
  | AssignUnspecified (x : var)
  | UnreachableUndefined
  deriving DecidableEq

instance {n} : OfNat arith n where ofNat := .Const n
instance : Coe String arith where coe := .Var
instance : Sub arith where sub := .Minus
instance : Mul arith where mul := .Times

infixr:76 " ;; " => cmd.Sequence

def nat_iter {A} (n : Nat) (f : A → A) (x : A) : A :=
  match n with
  | 0 => x
  | n' + 1 => f (nat_iter n' f x)

def interp_arith (e : arith) (v : valuation) : Nat :=
  match e with
  | .Const n => n
  | .Var x =>
      match lookup x v with
      | none => 0
      | some n => n
  | .Minus e1 e2 => interp_arith e1 v - interp_arith e2 v
  | .Times e1 e2 => interp_arith e1 v * interp_arith e2 v

def interp_cmd (c : cmd) (v : valuation) : valuation :=
  match c with
  | .Skip => v
  | .Assign x e => (x, interp_arith e v) :: v
  | .Sequence c1 c2 => interp_cmd c2 (interp_cmd c1 v)
  | .Repeat e body => nat_iter (interp_arith e v) (interp_cmd body) v
  | .AssignUnspecified x => v
  | .UnreachableUndefined => v

-- Minimal operational step relation & reflexive-transitive closure (`rtc`)
inductive step : valuation × cmd → valuation × cmd → Prop where
  | assign (v : valuation) (x : var) (e : arith) :
      step (v, .Assign x e) ((x, interp_arith e v) :: v, .Skip)
  | assign_unspec (v : valuation) (x : var) (n : Nat) :
      step (v, .AssignUnspecified x) ((x, n) :: v, .Skip)
  | seq_step {v v' c1 c1' c2} :
      step (v, c1) (v', c1') →
      step (v, .Sequence c1 c2) (v', .Sequence c1' c2)
  | seq_skip (v : valuation) (c2 : cmd) :
      step (v, .Sequence .Skip c2) (v, c2)
  | repeat_zero (v : valuation) (body : cmd) :
      step (v, .Repeat (.Const 0) body) (v, .Skip)
  | repeat_succ (v : valuation) (n : Nat) (body : cmd) :
      step (v, .Repeat (.Const (n + 1)) body)
           (v, .Sequence body (.Repeat (.Const n) body))

inductive rtc {α : Type} (r : α → α → Prop) : α → α → Prop where
  | refl (a : α) : rtc r a a
  | tail {a b c : α} : rtc r a b → r b c → rtc r a c

def stuck (s : valuation × cmd) : Prop :=
  s.2 ≠ .Skip ∧ ∀ s', ¬ step s s'

-- Example program placeholders referenced by the theorems
def double_unspecified : cmd := .Skip
def maybe_undefined_behavior : cmd := .UnreachableUndefined
def maybe_double_unspecified : cmd := .UnreachableUndefined

-- Theorems from the screenshots (using `sorry` just like the slides)
theorem rtc_unspec_done v x v'
    (h : rtc step (v, .AssignUnspecified x) (v', .Skip)) :
    ∃ n, v' = (x, n) :: v := by
  sorry

theorem rtc_assign_done v x e v'
    (h : rtc step (v, .Assign x e) (v', .Skip)) :
    v' = (x, interp_arith e v) :: v := by
  sorry

theorem double_unspecified_skips v0 v :
    rtc step (v0, double_unspecified) (v, .Skip) ↔
    ∃ m, v = ("y", 2 * m) :: ("x", m) :: ("z", 0) :: v0 := by
  sorry

theorem maybe_undefined_loop_skips e v v'
    (hrun : rtc step (v, .Repeat e .UnreachableUndefined) (v', .Skip)) :
    interp_arith e v = 0 ∧ v' = v := by
  sorry

theorem maybe_undefined_skips v0 v :
    rtc step (v0, maybe_undefined_behavior) (v, .Skip) ↔
    v = ("z", 0) :: v0 := by
  sorry

theorem maybe_double_unspecified_skips v0 v :
    rtc step (v0, maybe_double_unspecified) (v, .Skip) ↔
    ∃ m, v = ("y", 2 * m) :: ("x", m) :: ("z", 0) :: v0 := by
  sorry

theorem reachable_skip_valuations_match v0 v :
    rtc step (v0, maybe_double_unspecified) (v, .Skip) ↔
    rtc step (v0, double_unspecified) (v, .Skip) := by
  sorry

theorem maybe_double_may_get_stuck :
    ∃ s cs, rtc step ([], maybe_double_unspecified) (s, cs) ∧ stuck (s, cs) := by
  sorry

theorem double_not_stuck s cs (hrun : rtc step ([], double_unspecified) (s, cs)) :
    ¬ stuck (s, cs) := by
  sorry

-- * Weakest-precondition semantics
def wp (c : cmd) (Q : valuation → Prop) : valuation → Prop :=
  match c with
  | .Skip => Q
  | .Assign x e => fun v => Q ((x, interp_arith e v) :: v)
  | .Sequence c1 c2 => wp c1 (fun v' => wp c2 Q v')
  | .Repeat e body => fun v => nat_iter (interp_arith e v) (wp body) Q v
  | .AssignUnspecified x => fun v => ∀ n, Q ((x, n) :: v)
  | .UnreachableUndefined => fun _ => False

theorem wp_double_unspecified_true v :
    wp double_unspecified
      (fun v' => ∃ m, v' = ("y", 2 * m) :: ("x", m) :: ("z", 0) :: v)
      v := by
  sorry

theorem no_wp_for_maybe_double_unspecified Q v :
    ¬ wp maybe_double_unspecified Q v := by
  sorry

theorem wp_mono c : ∀ Q1 Q2,
    (∀ v, Q1 v → Q2 v) →
    ∀ v, wp c Q1 v → wp c Q2 v := by
  sorry

theorem step_wp {s s'} (hstep : step s s') : ∀ Q,
    True := by
  sorry

-- Quick sanity check you can run right away:
#eval interp_arith ("x" + 3) [("x", 4)] -- 7
#eval interp_cmd (.Assign "x" ("x" * 2)) [("x", 5)] -- [("x", 10), ("x", 5)]
