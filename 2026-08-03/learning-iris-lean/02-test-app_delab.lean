import Lean

open Lean PrettyPrinter Delaborator SubExpr

-- 1. Define a function with an implicit argument `{α : Type}`
def Box.mk {α : Type} (val : α) : α := val

-- 2. Define custom notation syntax: 📦(x)
syntax "📦(" term ")" : term
macro_rules
  | `(📦($x)) => `(Box.mk $x)


-------------------------------------------------------------
-- SCENARIO 1: WITHOUT app_delab
-------------------------------------------------------------

-- Lean can parse `📦(42)`, but prints it back as `Box.mk 42`
#check 📦(42)
-- OUTPUT: Box.mk 42 : Nat


-------------------------------------------------------------
-- SCENARIO 2: WITH app_delab
-------------------------------------------------------------

@[app_delab Box.mk]
def delabBoxMk : Delab := do
  -- GUARD 1: If the user turned on `pp.explicit`, do NOT use custom notation!
  if ← getPPOption getPPExplicit then failure

  -- GUARD 2: Extract the AST expression `Box.mk {α} val`
  let e ← getExpr
  let_expr Box.mk α val := e | failure

  -- GUARD 3: Only use box notation if the type `α` is `Nat`!
  if !α.isConstOf ``Nat then failure

  -- RECURSION: Delaborate the child expression `val` into syntax
  let valSyntax ← delab val

  -- RECONSTRUCT: Return custom syntax `📦(...)`
  `(📦($valSyntax))


-------------------------------------------------------------
-- TESTING THE BEHAVIOR
-------------------------------------------------------------

-- Test A: Type is `Nat` -> Uses custom syntax 📦(...)
#check Box.mk 42
-- OUTPUT: 📦(42) : Nat

-- Test B: Type is `String` -> Guard 3 triggers `failure`, falls back to default!
#check Box.mk "hello"
-- OUTPUT: Box.mk "hello" : String

-- Test C: User enabled `pp.explicit` -> Guard 1 triggers `failure`!
set_option pp.explicit true in
#check Box.mk 42
-- OUTPUT: @Box.mk Nat 42 : Nat
