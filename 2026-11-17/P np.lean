-- A deterministic Turing machine with `n + 2` states (`Fin (n + 2)`), ensuring at least
-- two distinct states (`0` and `1` can be used as reject / accept conventions).
-- Tape cells hold `Option Bool` (`none` = blank, `some b` = bit `b`).
-- Transition function takes `(state, cell)` and returns `none` to halt, or
-- `some (nextState, writeCell, moveRight)`.
abbrev TM (n : Nat) :=
  Fin (n + 2) → Option Bool → Option (Fin (n + 2) × Option Bool × Bool)

-- Runs machine `M` starting from step budget `t`, state `q`, head position `h`, and `tape`.
-- Returns `some true` for accept, `some false` for reject, or `none` on timeout (`0` steps left).
def run {n : Nat} (M : TM n) :
    Nat → Fin (n + 2) → Int → (Int → Option Bool) → Option Bool
  | _, q, _, _, none => some (q == 1)
  | t' + 1, _, h, tape, some (q', b, r) =>
      run M t' q' (if r then h + 1 else h - 1) (fun i => if i == h then b else tape i)
  | 0, _, _, _, some _ => none

-- Encodes a two-way infinite tape from input `w` (non-negative indices)
-- and witness/certificate `c` (negative indices: `-1` -> `c[0]?`, `-2` -> `c[1]?`, ...).
def input (w c : List Bool) (i : Int) : Option Bool :=
  if i < 0 then c[(-i - 1).toNat]? else w[i.toNat]?

-- Time complexity class P: there exist a machine `M` and polynomial exponent `k`
-- such that for every input `w`, `M` with empty certificate `[]` decides `L w`
-- within `w.length ^ k + k` steps.
def P (L : List Bool → Bool) : Prop :=
  ∃ (n : Nat) (M : TM n) (k : Nat),
    ∀ w, run M (w.length ^ k + k) 0 0 (input w []) = some (L w)

-- Time complexity class NP: there exist a machine `M` and polynomial exponent `k`
-- such that for every input `w`, `L w = true` holds iff there exists a certificate `c`
-- that `M` accepts (`some true`) within `w.length ^ k + k` steps.
def NP (L : List Bool → Bool) : Prop :=
  ∃ (n : Nat) (M : TM n) (k : Nat),
    ∀ w, L w = true ↔ ∃ c, run M (w.length ^ k + k) 0 0 (input w c) = some true

theorem P_eq_NP : P = NP := by sorry


----

-- A decision problem (language) over binary strings.
abbrev Language := List Bool → Bool

-- Tape contents (`none` = blank, `some b` = bit `b`), head movement (`true` = right, `false` = left),
-- and a two-way infinite tape indexed by integers.
abbrev Cell := Option Bool
abbrev MoveRight := Bool
abbrev Tape := Int → Cell

-- Machine state set with dedicated halting states (`reject`, `accept`) and `n` working states.
-- Using an inductive type makes halting states explicit in the type rather than magic `Fin` indices (`0` and `1`).
inductive State (n : Nat) where
  | reject  : State n
  | accept  : State n
  | working : Fin n → State n
  deriving DecidableEq, Repr

-- Converts a `State n` to `Bool` acceptance once halted (`true` for `accept`, `false` otherwise).
def State.isAccept {n : Nat} : State n → Bool
  | .accept => true
  | .reject => false
  | .working _ => false

-- Single transition action: next state, symbol written under the head, and head movement direction.
structure Action (n : Nat) where
  nextState : State n
  writeCell : Cell
  moveRight : MoveRight

-- Deterministic Turing machine transition function:
-- given current state and cell under the head, returns `none` to halt or `some action`.
abbrev TM (n : Nat) :=
  State n → Cell → Option (Action n)

-- Machine configuration: current state, tape head position, and tape contents.
structure Config (n : Nat) where
  state : State n
  head  : Int
  tape  : Tape

-- Updates a single tape cell at `pos` while leaving all other cells unchanged.
def Tape.write (tape : Tape) (pos : Int) (val : Cell) : Tape :=
  fun i => if i == pos then val else tape i

-- Advances one step if `M` has a transition; returns `none` if already halted.
def step {n : Nat} (M : TM n) (cfg : Config n) : Option (Config n) :=
  match M cfg.state (cfg.tape cfg.head) with
  | none => none
  | some act =>
      some {
        state := act.nextState
        head  := if act.moveRight then cfg.head + 1 else cfg.head - 1
        tape  := cfg.tape.write cfg.head act.writeCell
      }

-- Executes `M` from `cfg` for at most `fuel` steps.
-- * Halts with `fuel` remaining -> accepts iff `state.isAccept`.
-- * Still running when `fuel` reaches `0` -> returns `none` (time limit exceeded).
def run {n : Nat} (M : TM n) : Nat → Config n → Option Bool
  | _, cfg =>
      match step M cfg with
      | none => some cfg.state.isAccept
      | some nextCfg =>
          match ‹Nat› with
          | 0 => none
          | fuel' + 1 => run M fuel' nextCfg

-- Bounded evaluator using structural recursion on `fuel`.
def eval {n : Nat} (M : TM n) : Nat → Config n → Option Bool
  | 0, cfg =>
      match step M cfg with
      | none => some cfg.state.isAccept
      | some _ => none
  | fuel' + 1, cfg =>
      match step M cfg with
      | none => some cfg.state.isAccept
      | some nextCfg => eval M fuel' nextCfg

-- Builds the initial tape from input `w` (indices `0, 1, ...`) and certificate/witness `c`
-- (indices `-1, -2, ...` mapped to `c[0]?, c[1]?, ...`).
def makeTape (w c : List Bool) : Tape :=
  fun i => if i < 0 then c[(-i - 1).toNat]? else w[i.toNat]?

-- Polynomial time bound `|w|^k + k` used as a uniform step budget.
def polyBound (w : List Bool) (k : Nat) : Nat :=
  w.length ^ k + k

-- Initial machine configuration starting in `.working 0` (when `n > 0`), head `0`, on a given tape.
def initCfg (n : Nat) (tape : Tape) : Config (n + 1) :=
  { state := .working 0, head := 0, tape := tape }

-- `L ∈ P`: decidable in polynomial time with an empty certificate (`[]`).
def InP (L : Language) : Prop :=
  ∃ (n : Nat) (M : TM (n + 1)) (k : Nat),
    ∀ w, eval M (polyBound w k) (initCfg n (makeTape w [])) = some (L w)

-- `L ∈ NP`: `L w = true` iff some certificate `c` makes `M` accept (`some true`) in polynomial time.
def InNP (L : Language) : Prop :=
  ∃ (n : Nat) (M : TM (n + 1)) (k : Nat),
    ∀ w, L w = true ↔ ∃ c, eval M (polyBound w k) (initCfg n (makeTape w c)) = some true

-- Open conjecture (P vs. NP): placeholder `sorry` instead of the joke tactic `by claude`.
theorem P_eq_NP : InP = InNP := by
  sorry
  
  
