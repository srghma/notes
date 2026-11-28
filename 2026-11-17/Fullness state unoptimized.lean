-- https://github.com/leanprover/lean4/pull/15218/changes/46bc43f665c4b42ec88ccabad55a32d23892833f

structure FullnessState where
  isFullBefore    : Bool
  isFullAfter     : Bool
  isInitialBefore : Bool
  isInitialAfter  : Bool
  deriving Inhabited, BEq, Hashable, Repr

def FullnessState.withFullAfter (s : FullnessState) (v : Bool) : FullnessState :=
  { s with isFullAfter := v }

def FullnessState.withInitialBefore (s : FullnessState) (v : Bool) : FullnessState :=
  { s with isInitialBefore := v }

-- A set of FullnessState is just a membership test: does `s` belong to the set?
abbrev FullnessStateSet := FullnessState → Bool

def FullnessStateSet.contains (set : FullnessStateSet) (s : FullnessState) : Bool :=
  set s

def FullnessStateSet.ofPredBelow (p : FullnessState → Bool)
    (_limit : Nat) (acc : FullnessStateSet) : FullnessStateSet :=
  fun s => acc s || p s

def FullnessStateSet.ofPred (p : FullnessState → Bool) : FullnessStateSet :=
  p

def FullnessStateSet.finalAny (inner : FullnessStateSet) : FullnessStateSet :=
  fun s =>
    s.isFullAfter &&
      (inner (s.withFullAfter false) || inner (s.withFullAfter true))

def FullnessStateSet.finalAll (inner : FullnessStateSet) : FullnessStateSet :=
  fun s =>
    s.isFullAfter &&
      (inner (s.withFullAfter false) && inner (s.withFullAfter true))

def FullnessStateSet.initialAny (inner : FullnessStateSet) : FullnessStateSet :=
  fun s =>
    s.isInitialBefore &&
      (inner (s.withInitialBefore false) || inner (s.withInitialBefore true))

def FullnessStateSet.initialAll (inner : FullnessStateSet) : FullnessStateSet :=
  fun s =>
    s.isInitialBefore &&
      (inner (s.withInitialBefore false) && inner (s.withInitialBefore true))

def FullnessStateSet.anySplit (p : FullnessState → FullnessState → Bool) : FullnessStateSet :=
  fun s =>
    let midOptions : List (Bool × Bool) :=
      [(false, false), (false, true), (true, false), (true, true)]
    midOptions.any fun (isMidFull, isMidInitial) =>
      let stateA : FullnessState :=
        { s with isFullAfter := isMidFull, isInitialAfter := isMidInitial }
      let stateB : FullnessState :=
        { s with isFullBefore := isMidFull, isInitialBefore := isMidInitial }
      p stateA stateB

def newlineFails (state : FullnessState) : Bool :=
  state.isFullAfter || state.isInitialBefore

def newlineFailureSet : FullnessStateSet :=
  FullnessStateSet.ofPred newlineFails

def textEdgeFails (isEmpty before after : Bool) : Bool :=
  match before, after with
  | false, false => false
  | true,  false => true
  | false, true  => true
  | true,  true  => !isEmpty

def textFails (isEmpty : Bool) (state : FullnessState) : Bool :=
  textEdgeFails isEmpty state.isFullBefore state.isFullAfter ||
    textEdgeFails isEmpty state.isInitialBefore state.isInitialAfter

def textFailureSet (isEmpty : Bool) : FullnessStateSet :=
  FullnessStateSet.ofPred (textFails isEmpty)
