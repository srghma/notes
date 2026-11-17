```lean
import Lean

open Lean PrettyPrinter

-- 1. Define a standard Lean function
def double (n : Nat) : Nat := n + n

-- 2. Define custom syntax for it: dbl(x)
syntax "dbl(" term ")" : term

-- 3. Tell Lean how to EXPAND the syntax into code (Parser/Macro)
macro_rules
  | `(dbl($x)) => `(double $x)

-------------------------------------------------------------
-- SCENARIO 1: WITHOUT app_unexpander
-------------------------------------------------------------

-- Lean understands `dbl(5)`, but when pretty-printing the result,
-- it prints the raw function `double 5`.
#check dbl(5)
-- OUTPUT: double 5 : Nat  <-- Notice `dbl(...)` is gone!

-------------------------------------------------------------
-- SCENARIO 2: WITH app_unexpander
-------------------------------------------------------------

-- Now we tell Lean: "Whenever you see `double x` in AST form,
-- pretty-print it back as `dbl(x)`."
@[app_unexpander double]
def unexpDouble : Unexpander
  | `($_ $x) => `(dbl($x))  -- `$_` matches the function `double`, `$x` matches its argument
  | _ => throw ()

-- Now test it again:
#check dbl(5)
-- OUTPUT: dbl(5) : Nat    <-- Custom syntax is preserved!

#check double 5
-- OUTPUT: dbl(5) : Nat    <-- Even raw function calls get pretty-printed

```
