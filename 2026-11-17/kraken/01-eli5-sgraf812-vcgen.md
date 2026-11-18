# `main` → `sgraf812/vcgen` Local Diff Summary (72 files)

- **Base (`main` / `upstream/main`):** `28e4ca6`
- **Head (`sgraf812/vcgen`):** `d7566c4` (sgraf812's `vcgen` branch with latest `upstream/main` merged in)
- **Net diff:** **72 files changed** (`+8977 / -155` lines): **22 Updated (`M`)**, **50 New (`A`)**, **0 Deleted (`D`)**

---

## High-Level Story (ELI5)

On `main`, Kraken had `Program.wp` as a tiny wrapper around raw single-instruction stepping (`Eventually (step1 Host.exe)`), with no `Std.WP`/`vcgen` integration, no function calls, no CFG loop rule, and mostly manual `kstep` / separation-logic proofs.

Over 357 commits, `sgraf812/vcgen` turns Kraken into a full **`Std.WP` + `vcgen` + `grind` verification framework for x86-64**:
1. **New `Program.wp` + `While`/`StepOver` semantics** (`WP/Basic`, `WP/Step`, `WP/Host`, `WP/Instance`, `WP/Spec`): supports function calls (via stack-deepening detection), internal vs. external jumps, and conjunction (`WPConjunctive`).
2. **CFG Loop & Function Call Frameworks** (`Blocks`, `StateCfg`, `FunSpec`): cuts programs into basic blocks at labels so `vcgen` can verify arbitrary loops with invariants/variants, and generates auto-framing function specs (`funspec` with `CallingConvention.SysV`/`Win64`, `Mem.Mapped`, `Mem.WritesOnly`, `Mem.havoc`).
3. **Automation & Fast State Folding** (`Registers`, `Specs`, `KVCGen`, `GrindFold`, `SeparationMem`, `KrakenTactics/*`): eliminates exponential blowup by rewriting register updates into struct literals, constant-folding `BitVec` additions in `grind`, and proving memory framing directly via `Mapped`/`Contains`/`WritesOnly`/`Disjoint`.
4. **FFmpeg FMA3 Case Study + Benchmarks + Examples**: adds IEEE-754 `Float32.fma` and 10 AVX/FMA3 instructions to verify FFmpeg's `ff_scalarproduct_float_fma3`, plus 14 WP examples and a standalone `bench/` suite.

---

## 1. Deleted Files (`0` net files)

There are **0 deleted files** in the net diff between `main` and `sgraf812/vcgen`.

*(Historical note from the branch graph: intermediate prototypes like the `X64M` spec monad, `MachineWP`, and the separation-logic `FrameWP`/`SepWP` experiment were both created and deleted **within** `sgraf812/vcgen`'s history before converging on the current CFG-invariant, `Mem.Mapped`/`WritesOnly`-based `Program.wp` design.)*

---

## 2. Updated Files (`M` — 22 files)

### Build, Toolchain & Root Exports
1. **`lean-toolchain`**
   - **Before:** Pinned to `leanprover/lean4:nightly-2026-09-21`.
   - **What changed:** Bumped to `leanprover/lean4:nightly-2026-11-18` (bringing in the newer `Std.WP`, `Sym.simp` normalizer, and `grind` features used by `vcgen`).
2. **`lakefile.toml`**
   - **Before:** Only defined `Kraken` and test/runner targets with default options.
   - **What changed:** Added `backward.grind.normalizer = false` (to use `grind`'s newer `Sym.simp` normalizer) and a new precompiled `KrakenTactics` library (`KrakenTactics.*`).
3. **`Kraken.lean`**
   - **Before:** Re-exported the baseline semantics, parser, tactics, and `Kraken/X64/Examples/Examples.lean`.
   - **What changed:** Updated the top-level docstring to explain the `vcgen` pipeline, publicly exported `Specs`, `Registers`, `WP`, `KVCGen`, `WP.Instance`, `WP.Spec`, `StateCfg`, and imported all 14 new `Kraken/X64/Examples/WP/*.lean` files.

### Core Utilities, Memory & Tactics
4. **`Kraken/Attribute.lean`**
   - **Before:** Defined `@[kstep]` and `ksimp`.
   - **What changed:** Registered a new simp attribute `@[natural]` used to automatically prove CPS naturality of instruction semantics in `WP/Step.lean`.
5. **`Kraken/Data/List/Infix.lean`**
   - **Before:** Basic `IsInfix` / `IsInfixAt` lemmas.
   - **What changed:** Added `nil_isInfixAt` (the empty list is an infix at any index), used when a `FunDecls` body is empty.
6. **`Kraken/Layout.lean`**
   - **Before:** Contained `Program.directivesAtAddress_addrOf`.
   - **What changed:** Added `dsimp only [Executable.directivesAtAddress]` before `rw` so the proof works under the newer Lean nightly's `rw` matching.
7. **`Kraken/ToBytes.lean`**
   - **Before:** `BitVec.ofInt_ofBytes_toBytes` only worked for `val.toInt` where `val : BitVec w`.
   - **What changed:** Generalized `BitVec.ofInt_ofBytes_toBytes` to work on any `v : Int`, and updated `UInt{8,16,32,64}.ofBytes_toBytes` to chain with `BitVec.ofInt_toInt`.
8. **`Kraken/Mem.lean`**
   - **Before:** Basic `Mem` (`ExtHashMap`), `loadBytes`, `loadInt`, `storeInt`, and `List.At`.
   - **What changed:** Added "Load after store" theorems (`loadBytes_storeBytes`, `loadInt_storeInt`, `loadInt_one`, `get?_storeInt_one`, `loadInt_congr`, `get?_storeInt_of_ne`) so proofs can show reading back a pushed/stored value gives the exact written value and untouched bytes stay unchanged.
9. **`Kraken/SeparationMem.lean`**
   - **Before:** ~125 lines of basic separation-logic `Eq (bs.At a)` load/store lemmas.
   - **What changed:** Grew by +954 lines into a full memory-reasoning toolkit:
     - Fixed `dif_pos` → `dite_eq_left` for the new toolchain.
     - Added region slicing (`At_slice_sep`, `loadInt_slice`, `storeInt_slice`) and `Block` / `Blocks` / `Blocks.Inside` (owning memory regions whose exact byte contents don't matter).
     - Added **non-separation** framing predicates (`Contains`, `Mapped`, `UnchangedOutside`, `DomainGrows`, `WritesOnly`, `Blocks.Disjoint`, `Block.ofStackSlots`, `restrict`, `havoc`) plus `grind_pattern` rules so `grind` can prove memory safety, disjointness, and frame preservation automatically across calls and loops.
10. **`Kraken/SeparationTactics.lean`**
    - **Before:** `ecancel` was hardcoded to cancel `Std.ExtHashMap.sep` / `emp` clauses.
    - **What changed:** Generalized `ecancel` via a `SepOps` record (leftover from the `sepwp` prototype, registered via `sepOpsRef`), added a fast syntactic pass before unfolding mismatches, and added support for solving `PartialOrder.rel` entailments.
11. **`Kraken/SeparationTests.lean`**
    - **Before:** Expected metavariable names `?m.54` in `#guard_msgs`.
    - **What changed:** Updated expected mvar index to `?m.46` due to the newer Lean elaborator/tactic changes.

### X64 Architecture, AVX/FMA3 & Runner
12. **`Kraken/X64/Syntax.lean`**
    - **Before:** Had basic SSE/AVX instructions (`movups`, `addps`, etc.) and `Directive`/`Program` aliases.
    - **What changed:** Added 10 VEX/AVX/FMA3 instructions to `AvxOperation` (`vmovaps`, `vxorps`, `vaddps`, `vmulps`, `vfmadd231ps`, `vshufps`, `vextractf128`, `vmovhlps`, `vmovss`, `vaddss`) plus `Program.labels` helpers and `List.Nodup.eq_of_getElem?_label` (unique labels live at unique indices).
13. **`Kraken/X64/Parser/Syntax.lean`**
    - **Before:** Parsed the older SSE/AVX instructions.
    - **What changed:** Added parser syntax rules for the 10 new 3-operand / immediate / XMM AVX/FMA3 mnemonics.
14. **`Kraken/X64/Parser/Elab.lean`**
    - **Before:** Elaborated the older AVX instructions.
    - **What changed:** Added elaborators (`elabAvx3Op`, `elabAvxXmm3Op`, `elabImm8`, and `elabInstr` branches) for the 10 new AVX/FMA3 instructions.
15. **`Kraken/X64/PrintATT.lean`**
    - **Before:** Printed the older AVX instructions in AT&T syntax.
    - **What changed:** Added AT&T printing cases for the 10 new AVX/FMA3 instructions.
16. **`Kraken/X64/PrintIntel.lean`**
    - **Before:** Printed the older AVX instructions in Intel syntax.
    - **What changed:** Added Intel printing cases for the 10 new AVX/FMA3 instructions.
17. **`Kraken/X64/Semantics.lean`**
    - **Before:** `Reg64s.get64`/`set64` returned `Width.W64.type`; `push` updated `rsp` before storing; `Directives.interp` only took `ret`; no FMA3 or 3-op AVX semantics.
    - **What changed:**
      - Changed `Reg64s.get64`/`set64` to literally use `BitVec 64` (avoiding `Width.W64.type` vs `BitVec 64` syntactic mismatches in `grind` and `bv_decide`).
      - Added `sseTernOp`, `BitVec.packedTernOp`, `BitVec.shufps128`, and semantics for the 10 new AVX/FMA3 instructions (using `Kraken.Float32.fma`).
      - Added 8/16/32/64-bit `Mem.loadInt_storeInt_*` and `BitVec.ofInt_ofBytes_toBytes_*` `@[vcgen_simp]`/`grind_pattern` lemmas.
      - Fixed `push` to store to `[rsp - w]` *before* committing the new `rsp` (matching hardware restartable faults).
      - Added a separate `jmp` continuation to `Directives.interp` so fallthrough vs. jump are cleanly distinguished.
18. **`KrakenRunnerX64.lean`**
    - **Before:** Had random generators (`Gen`) for hardware differential testing, without `UInt8`.
    - **What changed:** Added `instance : Gen UInt8` so the hardware test runner can fuzz the new `imm8` AVX instructions (`vshufps`, `vextractf128`).

### WP Core & Legacy Examples
19. **`Kraken/X64/WP/Host.lean`**
    - **Before:** Defined `Host` with `prog` and `layout`, plus `startAddr`/`endAddr`.
    - **What changed:** Added `Instr.IsPadding`, required `labels_nodup : (Program.labels prog).Nodup` in `Host`, and proved address/label resolution lemmas (`Host.label_eq`, `Host.label_ne`, `Host.addrOf_succ`, `Host.directivesAtAddress_addrOf`).
20. **`Kraken/X64/WP/Basic.lean`**
    - **Before:** Defined `Program.wp` simply as `∀ k, p.IsInfixAt Host.prog k → Eventually (step1 Host.exe) ...`.
    - **What changed:** Rebuilt `Program.wp` around a `While` loop over `Executable.StepOver` with `[FunDecls]`, `Embeds p`, and `ContinueOnInternalExit` (jumps stay inside `p` only if the target is an internal label AND stack pointer is at or below entry `StackAtOrBelow s`; calls step over callees via `FunDecls.at`), marked `inductive_fixpoint` for mutual recursion, and proved `wp_mono`, `wp_and`, `wp_cons`, `wp_single`, `step1_of_wp`, and `run_infix`.
21. **`Kraken/X64/Examples/Examples.lean`**
    - **Before:** Imported dependencies privately and used the old `BitVec.ofInt_ofBytes_toBytes` statement.
    - **What changed:** Added `public import` / `@[expose] public section` (module system compatibility) and updated 3 proofs (`p6_correct`, `move_2_regs_to_heap_correct`, `alu_mem_example_correct`) with `BitVec.ofInt_toInt`.
22. **`Kraken/AArch64/Examples/Examples.lean`**
    - **Before:** Used `grind` in `swap_correct`, old `BitVec.ofInt_ofBytes_toBytes`, and `.toBitVec` on `X2`.
    - **What changed:** Updated to `grind -ring`, explicit `BitVec.ofInt_toInt`, and `X2.toNat` for the newer Lean nightly.

---

## 3. New Files (`A` — 50 files)

### A. WP Semantics, CFG Control Flow & Function Specs (6 files)
1. **`Kraken/X64/WP/Step.lean`**
   - **Idea (ELI5):** Proves that Kraken's CPS `Effects` trees are *natural* (they don't inspect their continuations, so running one instruction for two postconditions `P₁` and `P₂` is the same as running it once for `P₁ ∧ P₂`). Uses this to define `Executable.StepIn`, `Executable.StepOut` (treats a jump as a call only if `StackBelow`, i.e., `rsp` moved strictly downward), and `Executable.StepOver` (one step, stepping *over* calls).
2. **`Kraken/X64/WP/Instance.lean`**
   - **Idea (ELI5):** Plugs `Program.wp` into Lean's `Std.WP` (`WP` and `WPConjunctive` typeclasses) so `vcgen` knows how to run on `Program` and `Directive`, defines `MachineData.retAddr`, and exposes `step1_of_wp` to turn a `WP.wp` proof back into a baseline `Eventually (step1 Host.exe)` theorem.
3. **`Kraken/X64/WP/Spec.lean`**
   - **Idea (ELI5):** A big library of `@[spec]` Hoare triples for individual x86-64 instructions (`mov`, `add`, `adc`, `sub`, `mulx`, `cmp`, `test`, `xor`, `dec`, `inc`, `and`, `shl`, `lea`, `push`, `pop`, `ret`, `jmp`, `jcc`, `call`, and AVX/FMA3 ops), plus the structural dispatchers (`Program.WP.Spec.cons`, `straight_nil`, `straight_instr`, etc.) that steer `vcgen` down straight-line code vs. CFG blocks.
4. **`Kraken/Blocks.lean`**
   - **Idea (ELI5):** Cuts a flat `Program` list at every `.label` directive into `Program.view` (an entry body + `(label, body)` blocks) and `Program.blocks`, and proves these match `Program.fromLabel` suffixes. This is how the verifier sees basic blocks instead of raw instruction lists.
5. **`Kraken/StateCfg.lean`**
   - **Idea (ELI5):** Implements `Program.WP.Spec.cfg` — the control-flow-graph rule for `vcgen`. Given a loop/block invariant (`CfgInvariant`) and termination measure (`CfgVariant`), it turns a program with jumps and loops into one straight-line `vcgen` goal per basic block, plus defines the `cfg_exit` tactic to resolve internal jump targets.
6. **`Kraken/FunSpec.lean`**
   - **Idea (ELI5):** Defines the `funspec` command macro (including `mutual ... end` support with `termination_by`!). You write a function's `requires`, `ensures`, and `autoframes` (e.g. `calling_conv SysV preserves ... writes ...`), and it automatically generates the `Frame` predicate, `Frame.havoc` helper, `.go` proof obligation, and an `@[spec]` theorem that `vcgen` uses at every `call` site.

### B. State Simplification, `grind` & Custom Tactics (9 files)
7. **`Kraken/X64/Registers.lean`**
   - **Idea (ELI5):** Teaching `vcgen`/`grind` how x86-64 registers, flags, bitmasks, and memory addresses behave: rewrites named register reads/writes into struct updates (`{ s with rax := ... }`), handles 8/16/32-bit partial register writes, turns flag computations into clean `StatusFlags.ofAdd`/`ofSub`/`ofDec`/`ofInc`/`ofLogic` lemmas, simplifies `isAligned`/masks, and unfolds `AddrExpr` (`disp(base)` and SIB `disp(base, idx, scale)`).
8. **`Kraken/Specs.lean`**
   - **Idea (ELI5):** The core read-over-write API for `Reg64s` and `MachineData`: maps each `Reg64` to a numeric `Reg64.idx` (so `r = r'` decides fast), provides `set64_set64`, `get64_set64`, per-field `rax_set64`..`r15_set64`, and `MachineData` projection lemmas so state literals never unfold unnecessarily.
9. **`Kraken/KVCGen.lean`**
   - **Idea (ELI5):** Configures the `@[vcgen_simp]` rewrite set (reassociating `BitVec` additions so literals sit next to each other for `evalGround`, collapsing `UInt64`/`Int64`/`Program.labels` boilerplate) and defines the `kfinish` grind tactic (`cfg_exit; finish`) used as `vcgen [...] with kfinish`.
10. **`Kraken/GrindFold.lean`**
    - **Idea (ELI5):** A custom `grind` upward propagator (`propagateBVAdd`) that immediately constant-folds `a + b` when both `BitVec` roots in `grind`'s E-graph are literals—preventing exponential case-splits in long carry chains.
11. **`Kraken/StateSimp.lean`**
    - **Idea (ELI5):** Lists the rewrite lemma arrays (`lemmaNames`, `stateLemmaNames`) used by the `kfold` tactic for normalizing machine-state chains.
12. **`KrakenTactics.lean`**
    - **Idea (ELI5):** Root module for the precompiled `KrakenTactics` library, re-exporting `ClearDead` and `Fold`.
13. **`KrakenTactics/ClearDead.lean`**
    - **Idea (ELI5):** Implements the `clear_dead` tactic: walks equation hypotheses backwards from the goal to throw away dead/stale state equations before calling `bv_decide` (keeping solver context size constant).
14. **`KrakenTactics/Fold.lean`**
    - **Idea (ELI5):** Implements the `kfold` / `kfold_discharge` tactics using `Sym.Simp` to fold a state chain in a single linear pass using `let`-bindings (avoiding `2^n` proof-term blowup) before running `clear_dead` and `bv_decide`. *(Companion to `StateSimp.lean`; modern examples mostly use `vcgen ... with kfinish`, while `KrakenTactics` stays available for linear folding + `bv_decide`.)*
15. **`Kraken/Float32Fma.lean`**
    - **Idea (ELI5):** Lean's core `Float32.Model` doesn't have fused multiply-add (`a * b + c` with a *single* rounding step). This file defines `Kraken.Float32.fma` using `Float.Model.UnpackedFloat` (`mulExact` + single `add`/`round`) so `vfmadd231ps` matches real x86 hardware.

### C. X64 WP Examples (`Kraken/X64/Examples/WP/` — 14 files)
16. **`Basic.lean`** — Re-proves baseline small examples (`p1`, `p2`, `p4`, `p5`, `swap`) using `vcgen` + `step1_of_wp`.
17. **`AluMem.lean`** — Re-proves baseline `alu_mem_example` (reading from `136(%rdx)`) using `Mem.loadInt_sep` + `vcgen`.
18. **`LoadStore.lean`** — Smoke tests for `Mem.Mapped` + `Mem.Blocks.Disjoint` across 64/32/16/8-bit stack loads/stores and two non-aliasing heap buffers.
19. **`Jumps.lean`** — Tests CFG control flow on tricky jump shapes: forward jumps, loops (`decMid`, `countdown`), dead code (`jmpOver`), adjacent labels (`jmpGap`), `jcc`, indirect register jumps (`fnReuse`), and `push; ret` jumps (`retJump`).
20. **`P3.lean`** — Re-proves the baseline's `p3` (`2 ^ 2 ^ rbx` squaring loop using `mulx`) cleanly via `vcgen` invariants and `kfinish`.
21. **`PushPopLoop.lean`** — Proves a loop that pushes `n` times onto the stack and pops `n` times back off, using `Mem.Blocks` and `BitVec.SerialLt` stack reasoning.
22. **`CallSwap.lean`** — First function-call example: defines `swap_spec` with `funspec` + `autoframes`, then verifies a caller (`pswap`) that calls `swap` twice.
23. **`EvenOdd.lean`** — Proves *mutually recursive* functions `even` and `odd` using `mutual funspec ... termination_by` and a stack reservation (`reserve s.regs.rdi.toNat`).
24. **`Memmove.lean`** — Verifies a full overlapping-buffer `memmove` (forward and backward byte-copy loops using `Mem.Contains` and `Mem.WritesOnly`) and proves a caller against `memmove_spec`.
25. **`FfScalarproductFloatFma3.lean`** — Real-world showcase: verifies memory safety and register/frame preservation of FFmpeg's disassembled `ff_scalarproduct_float_fma3` (all 4 vector/scalar tail loops: `.loop128`, `.loop64`, `.loop32`, `.loop16`).
26. **`Surprises.lean`** — Pedagogical counterexamples showing 3 subtle rules of `Program.wp`: (B1) releasing stack above start exits the fragment, (C1) `sub $8, %rsp; jmp f` is a jump not a call, (C2) tail-calls (`jmp f`) exit rather than return.
27. **`EventuallySurprises.lean`** — Contrasts `Eventually (step1 ...)` with `Program.wp`: shows cases where `Eventually` accepts accidental arrivals caused by surrounding host code, whereas `Program.wp` properly refutes them.
28. **`ManyCalls.lean`** — Scaling test: caller makes 8 sequential calls to a callee `touch` (which reads/returns, verifying frame preservation doesn't blow up).
29. **`ChangingFrames.lean`** — Scaling test: caller makes 8 calls to `poke` while incrementing `%rdi` by 8 each time, stressing `autoframes` when every call writes to a different address.

### D. Hardware / Interpreter Assembly Tests (`Kraken/X64/Test/asm/` — 5 files)
30. **`test_avx_arith.S`** — Tests `vxorps`, `vaddps`, `vmulps`, `vmovaps` on `xmm`/`ymm` and memory, checking upper-bit zeroing and subnormals/overflows.
31. **`test_avx_fma.S`** — Edge-case tests for `vfmadd231ps` (single rounding vs. unfused `vmulps+vaddps`, tie-to-even, subnormals, infinities, signed zeros).
32. **`test_avx_shuffle.S`** — Tests `vextractf128`, `vmovhlps`, `vmovss`, `vshufps`, `vaddss` and `xmm` upper-128-bit clearing.
33. **`test_scalarproduct_fma3.S`** — Calls FFmpeg's `ff_scalarproduct_float_fma3` on lengths 4, 8, 16, 32, 60, and 100 to exercise every loop/branch against real hardware.
34. **`test_vzeroupper_ymm.S`** — Tests that `vzeroupper` clears bits `255:128` of `ymm0`–`ymm15` while keeping `127:0`.

### E. Standalone Benchmark Suite (`bench/` — 16 files)
35. **`bench/.gitignore`** — Ignores `bench/.lake/`.
36. **`bench/README.md`** — Documents how to run benchmarks (`lake env lean adcchain.lean`), the 5 benchmark families, and baseline stepping/kernel timings.
37. **`bench/lakefile.toml`** — Independent Lake package depending on parent `..` (`Kraken`), defining `Driver`, `Cases`, and `Bench` (with `--tstack=102400`).
38. **`bench/lake-manifest.json`** — Path dependency manifest pointing to `..`.
39. **`bench/lean-toolchain`** — Pinned to `leanprover/lean4:nightly-2026-11-07`.
40. **`bench/lib/Driver.lean`** — `runBenchUsingTactic` harness: unfolds a recursive goal of size `n`, times tactic stepping, VC discharge, `instantiateMVars`, and kernel checking, and prints certificate DAG size, spine depth, and top head constants.
41. **`bench/Cases/AdcChain.lean`** — Parameterized straight-line `n`-step `adc` carry chain on concrete constants (`rax = 3 * n`).
42. **`bench/Cases/CarryFlags.lean`** — Parameterized `n`-step `adc` carry chain on *symbolic* registers checking `zf` and `sf`.
43. **`bench/Cases/CarryJumps.lean`** — Parameterized `n`-step `adc; jz out` chain on symbolic registers (one VC per conditional exit).
44. **`bench/Cases/ManyCalls.lean`** — Parameterized `n` calls to `touch` writing a fixed memory slot (`%rsi`).
45. **`bench/Cases/ChangingFrames.lean`** — Parameterized `n` calls to `poke` writing sequential 8-byte slots (`addq $8, %rdi`).
46. **`bench/adcchain.lean`** — Runner `#eval` for `AdcChain` at `n = 40, 160, 640`.
47. **`bench/carryflags.lean`** — Runner `#eval` for `CarryFlags` at `n = 8, 16, 32`.
48. **`bench/carryjumps.lean`** — Runner `#eval` for `CarryJumps` at `n = 8, 16, 32`.
49. **`bench/manycalls.lean`** — Runner `#eval` for `ManyCalls` at `n = 8, 16, 32`.
50. **`bench/changingframes.lean`** — Runner `#eval` for `ChangingFrames` at `n = 8, 16, 32` (with `kfinish (instances := 3000)`).
