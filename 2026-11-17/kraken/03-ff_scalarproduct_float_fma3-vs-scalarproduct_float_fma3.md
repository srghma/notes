### How `float_dsp.asm` differs from `FfScalarproductFloatFma3.lean`

The Lean file is a **formal verification model of the compiled x86-64 System V machine code** (disassembled into AT&T syntax), rather than the portable NASM source:

1. **Multi-target NASM macros vs. concrete x86-64 SysV AT&T disassembly**:
   - `float_dsp.asm` is Intel-syntax and supports `UNIX64`, `WIN64` (different argument registers), and `ARCH_X86_32` (notice the `%if ARCH_X86_64 == 0` blocks storing `xmm0` to stack and pushing it onto the x87 FPU stack with `fld dword r0m`).
   - `FfScalarproductFloatFma3.lean` is exclusively the expanded **x86-64 System V** object code in AT&T syntax (reversed operands, `%rdi/%rsi/%rdx/%rcx/%r8`, explicit `v`-prefixed instructions, `vfmadd231ps`, `sub $0xffffffffffffff80,%r8`, and `vzeroupper`).

2. **Four `RET`s vs. `jmp done` + single `ret`**:
   - In `float_dsp.asm`, each of the four tail paths ends directly with `RET` (`vzeroupper; ret`).
   - In `FfScalarproductFloatFma3.lean`, `scalarproduct_fma3_prog` replaces the first three `ret` instructions with `jmp done` (after `vzeroupper`) targeting `done: nop`, and `scalarproduct_fma3` appends a single `ret` at the end (`scalarproduct_fma3_prog ++ ret`). This gives `scalarproduct_fma3_prog` a single exit label for structured WP verification while `scalarproduct_fma3_funspec` still verifies the full function with `ret`.

3. **Explicit preconditions in Lean exposing undocumented/implicit assembly assumptions**:
   The Lean specs (`scalarproduct_fma3_spec` / `scalarproduct_fma3_funspec`) make the exact safety requirements of the assembly explicit:
   - **`isAligned 16 rdi` (only `v1`, not `v2`)**: `.loop128`, `.loop64`, and `.loop32` use unaligned `vmovups` for `v1` and memory-operand `vfmadd231ps` for `v2`, **but `.loop16` uses `vmovaps (%rdi,%r8,1), %xmm1`** (requiring 16-byte alignment on `v1`, while `vmulps (%rsi,%r8,1)` does not require alignment on `v2`).
   - **`len % 4 = 0` and `0 < len`**: `.loop16` checks its loop condition at the **bottom** (`cmp %rcx, %r8; jl .loop16`). If `len < 4` (even `len = 0`), it jumps to `.l16` and still unconditionally reads 16 bytes from both `v1` and `v2`. And if `len % 4 ≠ 0`, trailing elements `< 4` are ignored.
   - **`len * 4 < 2^32`**: Ensures `shl $0x2, %edx` does not overflow 32 bits (and clears the upper 32 bits of `%rdx`).

4. **Scope of verification (safety & framing, not floating-point arithmetic correctness)**:
   - `float_dsp.asm` is meant to compute $\sum_{i=0}^{\text{len}-1} v_1[i] \cdot v_2[i]$ in `xmm0`.
   - The Lean theorems verify **termination, memory safety (no out-of-bounds reads or alignment faults within the mapped `v1`/`v2`/stack-return-address blocks), memory preservation (`s'.dmem = s.dmem`), and SysV ABI register/stack framing (`ensures s' => True` with `autoframes`)**—they do not currently specify or prove the IEEE-754 floating-point value returned in `xmm0`.

```lean
/-
  Formal verification (Weakest Precondition / WP) of FFmpeg's `ff_scalarproduct_float_fma3`
  (from `libavutil/x86/float_dsp.asm`) using the Kraken x86-64 verification library.

  Big picture (ELI5):
  This file takes the compiled x86-64 machine instructions of FFmpeg's FMA3 dot-product
  function and proves mathematically that:
    1. It always finishes (never gets stuck in an infinite loop).
    2. It never reads outside the two input arrays or crashes on bad alignment.
    3. It never secretly modifies memory (the arrays stay read-only).
    4. It obeys the Linux/System V x86-64 calling convention (doesn't clobber caller's
       callee-saved registers or corrupt the stack / return address).
  (Note: this example verifies safety, termination, and ABI framing; it does NOT yet
   prove the floating-point arithmetic value returned in `%xmm0`.)
-/
module

public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.FunSpec
import Kraken.X64.Parser

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

-- Enable Kraken's experimental Verification Condition Generator (`vcgen`)
set_option experimental.vcgen true

namespace State.FfScalarproductFloatFma3

/-
  How this assembly differs from FFmpeg's NASM source (`libavutil/x86/float_dsp.asm`):

  1. `x86inc.asm` macros are already expanded for Linux/SysV x86-64:
     - `INIT_YMM fma3` + `cglobal scalarproduct_float, 3,5,8, v1, v2, size, len, offset`
       became the concrete label `ff_scalarproduct_float_fma3:` with concrete registers:
         `v1q` -> `%rdi` (arg 1: pointer to float array v1)
         `v2q` -> `%rsi` (arg 2: pointer to float array v2)
         `sized`/`sizeq` -> `%edx`/`%rdx` (arg 3: number of floats `len`)
         `lenq` -> `%rcx` (scratch: byte limit / remaining bytes)
         `offsetq` -> `%r8` (scratch: current byte cursor)
         `m0..m7` -> `%ymm0..%ymm7`
     - `%if ARCH_X86_64 == 0` (the 32-bit x87 FPU `fld` fallback) is compiled out.
     - `x86inc.asm` `AVX_INSTR` wrappers (`xorps`, `movups`, `addps`, `movaps`, `mulps`,
       `movhlps`, `movss`, `shufps`, `addss`) expanded to VEX-prefixed AVX mnemonics
       (`vxorps`, `vmovups`, `vaddps`, `vmovaps`, `vmulps`, `vmovhlps`, `vmovss`, ...).
       Notice 2-arg `movhlps xmm1, xmm0` became 3-arg `vmovhlps %xmm0,%xmm1,%xmm1`.
     - `fmaddps m0, m4, [v2q+offsetq], m0` expanded to `vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0`.

  2. Intel syntax (NASM) -> AT&T / GAS disassembly syntax:
     - Operand order is REVERSED (`src, dst` instead of `dst, src`).
       e.g. `shl sized, 2` -> `shl $0x2,%edx`; `vextractf128 xmm2, m0, 1` -> `vextractf128 $0x1,%ymm0,%xmm2`.
     - Registers use `%`, immediates use `$` in hex (`$0x20` = 32, `$0x7f` = 127).
     - `~127`, `~63`, `~31`, `~15` appear as 64-bit two's-complement masks
       (`$0xffffffffffffff80`, `$0xffffffffffffffc0`, `$0xffffffffffffffe0`, `$0xfffffffffffffff0`).
     - Memory `[base + offset + disp]` becomes `disp(base, offset, 1)`.
     - Assembler size-optimization quirk in `.loop128`:
       NASM `add offsetq, 128` became `sub $0xffffffffffffff80,%r8` (`r8 - (-128) = r8 + 128`),
       because `-128` fits in a compact 1-byte signed immediate (`imm8`), while `+128` does not!

  3. Single-exit refactoring for formal verification:
     - In NASM, each of the 4 branches ends with `RET` (`vzeroupper` + `ret`).
     - Here, the 3 upper branches replace `ret` with `jmp done`, `.l16` falls through
       to `done: nop`, and the final `ret` is appended separately in `scalarproduct_fma3`.
       This gives `vcgen` a single `"done"` exit point and lets us separate the body
       proof (`scalarproduct_fma3_spec`) from the full `call`/`ret` ABI proof (`scalarproduct_fma3_funspec`).
-/
/-- Function body of `ff_scalarproduct_float_fma3` without the final `ret` instruction. -/
def scalarproduct_fma3_prog : Program := ⸨prog|
ff_scalarproduct_float_fma3:                         # before: `INIT_YMM fma3` + `cglobal scalarproduct_float, 3,5,8, v1, v2, size, len, offset`
                                                     # SysV x64 register map (all caller-saved -> zero push/pop needed!):
                                                     #   v1=%rdi (arg1), v2=%rsi (arg2), size=%edx/%rdx (arg3), len=%rcx (r3), offset=%r8 (r4), m0..m7=%ymm0..%ymm7
    xor %r8,%r8                                      # before: `xor offsetq, offsetq` | offset=0 (byte cursor); %r8 is 5th SysV reg (r4)
    vxorps %ymm0,%ymm0,%ymm0                         # before: `xorps m0, m0, m0` | AVX_INSTR -> VEX; m0=%ymm0 (Bucket #0 = 8 zero floats)
    shl $0x2,%edx                                    # before: `shl sized, 2` (AT&T flips src,dst) | size *= 4 (floats->bytes); writing %edx zero-extends %rdx!
    mov %rdx,%rcx                                    # before: `mov lenq, sizeq` (AT&T flips src,dst) | %rcx = total bytes (%rcx is 4th SysV reg r3)
    cmp $0x20,%rcx                                   # before: `cmp lenq, 32` | fewer than 32B (< 8 floats)?
    jl .l16                                          # before: `jl .l16` | jump straight to 16B SSE tail (skips zeroing %ymm1..%ymm3)
    cmp $0x40,%rcx                                   # before: `cmp lenq, 64` | fewer than 64B (< 16 floats)?
    jl .l32                                          # before: `jl .l32` | jump straight to 32B AVX tail
    vxorps %ymm1,%ymm1,%ymm1                         # before: `xorps m1, m1, m1` | Bucket #1 (%ymm1) = 0 (only cleared if >= 64B)
    cmp $0x80,%rcx                                   # before: `cmp lenq, 128` | fewer than 128B (< 32 floats)?
    jl .l64                                          # before: `jl .l64` | jump straight to 64B tail
    and $0xffffffffffffff80,%rcx                     # before: `and lenq, ~127` | round total down to multiple of 128B (end offset for .loop128)
    vxorps %ymm2,%ymm2,%ymm2                         # before: `xorps m2, m2, m2` | Bucket #2 (%ymm2) = 0
    vxorps %ymm3,%ymm3,%ymm3                         # before: `xorps m3, m3, m3` | Bucket #3 (%ymm3) = 0
.loop128:                                            # ── Main loop: 128 bytes (32 floats) / iter using 4 buckets to hide FMA latency ──
    vmovups (%rdi,%r8,1),%ymm4                       # before: `movups m4, [v1q+offsetq]` | unaligned 32B load v1[0..7] (%rdi=%r0=v1); safe for 16B-aligned ptrs
    vmovups 0x20(%rdi,%r8,1),%ymm5                   # before: `movups m5, [v1q+offsetq + 32]` | load v1[8..15] into %ymm5
    vmovups 0x40(%rdi,%r8,1),%ymm6                   # before: `movups m6, [v1q+offsetq + 64]` | load v1[16..23] into %ymm6
    vmovups 0x60(%rdi,%r8,1),%ymm7                   # before: `movups m7, [v1q+offsetq + 96]` | load v1[24..31] into %ymm7
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0             # before: `fmaddps m0, m4, [v2q+offsetq], m0` | FMA4_INSTR -> vfmadd231ps (AT&T flips); %ymm0 += %ymm4 * v2[0..7]
    vfmadd231ps 0x20(%rsi,%r8,1),%ymm5,%ymm1         # before: `fmaddps m1, m5, [v2q+offsetq + 32], m1` | %ymm1 += %ymm5 * v2[8..15]
    vfmadd231ps 0x40(%rsi,%r8,1),%ymm6,%ymm2         # before: `fmaddps m2, m6, [v2q+offsetq + 64], m2` | %ymm2 += %ymm6 * v2[16..23]
    vfmadd231ps 0x60(%rsi,%r8,1),%ymm7,%ymm3         # before: `fmaddps m3, m7, [v2q+offsetq + 96], m3` | %ymm3 += %ymm7 * v2[24..31]
    sub $0xffffffffffffff80,%r8                      # before: `add offsetq, 128` | assembler trick: `sub -128` uses 1-byte imm8 (-128 fits, +128 doesn't!) -> %r8 += 128
    cmp %rcx,%r8                                     # before: `cmp offsetq, lenq` (AT&T flips!) | compare cursor %r8 vs loop limit %rcx
    jl .loop128                                      # before: `jl .loop128` | repeat while %r8 < %rcx
    vaddps %ymm2,%ymm0,%ymm0                         # before: `addps m0, m0, m2` | merge Bucket #2 into Bucket #0
    vaddps %ymm3,%ymm1,%ymm1                         # before: `addps m1, m1, m3` | merge Bucket #3 into Bucket #1 (keep 2 buckets alive in case .l64 runs)
    mov %rdx,%rcx                                    # before: `mov lenq, sizeq` | restore total byte count from %rdx
    and $0x7f,%rcx                                   # before: `and lenq, 127` | %rcx = remaining bytes (size % 128)
    cmp $0x40,%rcx                                   # before: `cmp lenq, 64` | >= 64B left?
    jge .l64                                         # before: `jge .l64` | handle 64B chunk using both %ymm0 and %ymm1
    vaddps %ymm1,%ymm0,%ymm0                         # before: `addps m0, m0, m1` | < 64B left: merge Bucket #1 into Bucket #0 (now only %ymm0)
    cmp $0x20,%rcx                                   # before: `cmp lenq, 32` | >= 32B left?
    jge .l32                                         # before: `jge .l32` | handle 32B chunk
    vextractf128 $0x1,%ymm0,%xmm2                    # before: `vextractf128 xmm2, m0, 1` (AT&T flips!) | extract upper 4 floats [4..7] of %ymm0 into %xmm2
    vaddps %xmm2,%xmm0,%xmm0                         # before: `addps xmm0, xmm2` | fold 8 floats -> 4 floats in %xmm0 ([0+4, 1+5, 2+6, 3+7])
    cmp $0x10,%rcx                                   # before: `cmp lenq, 16` | >= 16B left?
    jge .l16                                         # before: `jge .l16` | handle 16B chunk
    vmovhlps %xmm0,%xmm1,%xmm1                       # before: `movhlps xmm1, xmm0` | AVX_INSTR 3-op VEX form; copy top 2 floats [c,d] of %xmm0 to low half of %xmm1
    vaddps %xmm1,%xmm0,%xmm0                         # before: `addps xmm0, xmm1` | fold 4 floats -> 2 floats in %xmm0[0..1] = [a+c, b+d]
    vmovss %xmm0,%xmm1,%xmm1                         # before: `movss xmm1, xmm0` | AVX_INSTR 3-op VEX form; copy lane 0 (a+c) into %xmm1[0]
    vshufps $0x1,%xmm0,%xmm0,%xmm0                   # before: `shufps xmm0, xmm0, 1` (AT&T flips!) | slide lane 1 (b+d) into %xmm0[0]
    vaddss %xmm1,%xmm0,%xmm0                         # before: `addss xmm0, xmm1` | %xmm0[0] = (a+c)+(b+d) = scalar float result (SysV float return reg!)
    vzeroupper                                       # before: part of `RET` (when `vzeroupper_required=1`) | clear upper YMM bits to avoid AVX->SSE stall
    jmp done                                         # before: `ret` part of `RET` (`ARCH_X86_64==0` x87 `fld` stripped) | jump to unified `done` exit for Kraken WP
.l64:                                                # ── Tier 1 tail: 64 bytes (16 floats) ──
    and $0xffffffffffffffc0,%rcx                     # before: `and lenq, ~63` | round remaining bytes down to multiple of 64 (here 64)
    add %r8,%rcx                                     # before: `add lenq, offsetq` | %rcx = target end byte offset
.loop64:
    vmovups (%rdi,%r8,1),%ymm4                       # before: `movups m4, [v1q+offsetq]` | load v1[0..7]
    vmovups 0x20(%rdi,%r8,1),%ymm5                   # before: `movups m5, [v1q+offsetq + 32]` | load v1[8..15]
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0             # before: `fmaddps m0, m4, [v2q+offsetq], m0` | %ymm0 += %ymm4 * v2[0..7]
    vfmadd231ps 0x20(%rsi,%r8,1),%ymm5,%ymm1         # before: `fmaddps m1, m5, [v2q+offsetq + 32], m1` | %ymm1 += %ymm5 * v2[8..15]
    add $0x40,%r8                                    # before: `add offsetq, 64` | advance cursor by 64B (fits in imm8!)
    cmp %rcx,%r8                                     # before: `cmp offsetq, lenq` | done with 64B chunk?
    jl .loop64                                       # before: `jl .loop64` | runs at most 1 iteration (because remaining < 128B)
    vaddps %ymm1,%ymm0,%ymm0                         # before: `addps m0, m0, m1` | merge Bucket #1 into Bucket #0
    mov %rdx,%rcx                                    # before: `mov lenq, sizeq` | restore total bytes
    and $0x3f,%rcx                                   # before: `and lenq, 63` | %rcx = remaining bytes (size % 64)
    cmp $0x20,%rcx                                   # before: `cmp lenq, 32` | >= 32B left?
    jge .l32                                         # before: `jge .l32` | handle 32B chunk
    vextractf128 $0x1,%ymm0,%xmm2                    # before: `vextractf128 xmm2, m0, 1` | fold 8 floats (%ymm0) -> 4 floats (%xmm0)
    vaddps %xmm2,%xmm0,%xmm0                         # before: `addps xmm0, xmm2`
    cmp $0x10,%rcx                                   # before: `cmp lenq, 16` | >= 16B left?
    jge .l16                                         # before: `jge .l16` | handle 16B chunk
    vmovhlps %xmm0,%xmm1,%xmm1                       # before: `movhlps xmm1, xmm0` | final horizontal squeeze: 4 floats -> 1 float in %xmm0[0]
    vaddps %xmm1,%xmm0,%xmm0                         # before: `addps xmm0, xmm1`
    vmovss %xmm0,%xmm1,%xmm1                         # before: `movss xmm1, xmm0`
    vshufps $0x1,%xmm0,%xmm0,%xmm0                   # before: `shufps xmm0, xmm0, 1`
    vaddss %xmm1,%xmm0,%xmm0                         # before: `addss xmm0, xmm1`
    vzeroupper                                       # before: `RET` (`vzeroupper` + `ret`) | clear upper YMM bits
    jmp done                                         # before: `ret` | jump to unified `done` exit
.l32:                                                # ── Tier 2 tail: 32 bytes (8 floats) ──
    and $0xffffffffffffffe0,%rcx                     # before: `and lenq, ~31` | round remaining bytes down to multiple of 32 (here 32)
    add %r8,%rcx                                     # before: `add lenq, offsetq` | %rcx = target end byte offset
.loop32:
    vmovups (%rdi,%r8,1),%ymm4                       # before: `movups m4, [v1q+offsetq]` | load 8 floats from v1
    vfmadd231ps (%rsi,%r8,1),%ymm4,%ymm0             # before: `fmaddps m0, m4, [v2q+offsetq], m0` | %ymm0 += %ymm4 * v2[0..7]
    add $0x20,%r8                                    # before: `add offsetq, 32` | advance cursor by 32B
    cmp %rcx,%r8                                     # before: `cmp offsetq, lenq`
    jl .loop32                                       # before: `jl .loop32` | runs at most 1 iteration (remaining < 64B)
    vextractf128 $0x1,%ymm0,%xmm2                    # before: `vextractf128 xmm2, m0, 1` | fold 8 floats (%ymm0) -> 4 floats (%xmm0)
    vaddps %xmm2,%xmm0,%xmm0                         # before: `addps xmm0, xmm2`
    mov %rdx,%rcx                                    # before: `mov lenq, sizeq` | restore total bytes
    and $0x1f,%rcx                                   # before: `and lenq, 31` | %rcx = remaining bytes (size % 32)
    cmp $0x10,%rcx                                   # before: `cmp lenq, 16` | >= 16B left?
    jge .l16                                         # before: `jge .l16` | handle 16B chunk
    vmovhlps %xmm0,%xmm1,%xmm1                       # before: `movhlps xmm1, xmm0` | final horizontal squeeze: 4 floats -> 1 float in %xmm0[0]
    vaddps %xmm1,%xmm0,%xmm0                         # before: `addps xmm0, xmm1`
    vmovss %xmm0,%xmm1,%xmm1                         # before: `movss xmm1, xmm0`
    vshufps $0x1,%xmm0,%xmm0,%xmm0                   # before: `shufps xmm0, xmm0, 1`
    vaddss %xmm1,%xmm0,%xmm0                         # before: `addss xmm0, xmm1`
    vzeroupper                                       # before: `RET` (`vzeroupper` + `ret`) | clear upper YMM bits
    jmp done                                         # before: `ret` | jump to unified `done` exit
.l16:                                                # ── Tier 3 tail: 16 bytes (4 floats, SSE-width) ──
    and $0xfffffffffffffff0,%rcx                     # before: `and lenq, ~15` | round remaining bytes down to multiple of 16 (here 16)
    add %r8,%rcx                                     # before: `add lenq, offsetq` | %rcx = target end byte offset
.loop16:                                             # do-while loop: assumes len > 0 and len % 4 == 0 (`h_len_pos`, `h_len_mod`)
    vmovaps (%rdi,%r8,1),%xmm1                       # before: `movaps xmm1, [v1q+offsetq]` | ALIGNED 16B load -> why `h_v1_aligned` is required on %rdi!
    vmulps (%rsi,%r8,1),%xmm1,%xmm1                  # before: `mulps xmm1, [v2q+offsetq]` | AVX mem operand needs no alignment -> no alignment needed on %rsi!
    vaddps %xmm1,%xmm0,%xmm0                         # before: `addps xmm0, xmm1` | %xmm0 += %xmm1
    add $0x10,%r8                                    # before: `add offsetq, 16` | advance cursor by 16B
    cmp %rcx,%r8                                     # before: `cmp offsetq, lenq`
    jl .loop16                                       # before: `jl .loop16` | runs at most 1 iteration (remaining < 32B)
    vmovhlps %xmm0,%xmm1,%xmm1                       # before: `movhlps xmm1, xmm0` | [a,b,c,d] -> %xmm1 = [c,d,?,?]
    vaddps %xmm1,%xmm0,%xmm0                         # before: `addps xmm0, xmm1` | %xmm0 = [a+c, b+d, ?, ?]
    vmovss %xmm0,%xmm1,%xmm1                         # before: `movss xmm1, xmm0` | %xmm1[0] = a+c
    vshufps $0x1,%xmm0,%xmm0,%xmm0                   # before: `shufps xmm0, xmm0, 1` | %xmm0[0] = b+d
    vaddss %xmm1,%xmm0,%xmm0                         # before: `addss xmm0, xmm1` | %xmm0[0] = a+b+c+d
    vzeroupper                                       # before: `RET` (`vzeroupper` + `ret`) | clear upper YMM bits
done:                                                # added for Kraken: single unified exit point (`ret` is appended in `scalarproduct_fma3`)
    nop                                              # added for Kraken: anchor instruction for the `"done"` WP invariant
⸩

/-- Complete `ff_scalarproduct_float_fma3` function including the final `ret`. -/
def scalarproduct_fma3 : Program := scalarproduct_fma3_prog ++ ⸨prog|
    ret
⸩

/--
  Body-level specification (without `call`/`ret`):
  Proves that `scalarproduct_fma3_prog` terminates cleanly (`fun _ _ => False` on errors)
  and leaves all of memory completely unchanged (`s'.dmem = s.dmem`).

  Why each hypothesis (precondition) is needed (ELI5):
  - `h_len_reg`: the low 32 bits of `%rdx` (`%edx`) hold the C `int order` (`len`).
  - `h_len_mod` & `h_len_pos`: `len` must be a positive multiple of 4 floats (`len * 4` is a
    positive multiple of 16 bytes), because `.l16` is a do-while loop that always reads 16 bytes!
  - `h_len_bound`: `len * 4 < 2^32` ensures `shl $0x2, %edx` (multiplying by 4) doesn't overflow 32 bits.
  - `h_v1_aligned`: `v1` (`%rdi`) must be 16-byte aligned because `.loop16` uses `vmovaps` (aligned load)
    on `%rdi`. Notice `%rsi` (`v2`) does NOT need alignment here because `vmulps`'s memory operand
    doesn't require 16-byte alignment under AVX, and `.loop128`/`.loop64`/`.loop32` use `vmovups`!
  - `h_v1`, `h_v2`: separation-logic assertions saying `[rdi, rdi + len*4)` and `[rsi, rsi + len*4)`
    are valid mapped blocks in memory `s.dmem`.
-/
theorem scalarproduct_fma3_spec [Host] [FunDecls] (s : MachineData) (len : Nat)
    (h_len_reg : (s.regs.get64 .rdx).take 32 = BitVec.ofNat 32 len)
    (h_len_mod : len % 4 = 0) (h_len_pos : 0 < len) (h_len_bound : len * 4 < 2 ^ 32)
    (h_v1_aligned : isAligned 16 (s.regs.get64 .rdi) = true)
    (R₁ R₂ : DataMem → Prop)
    (h_v1 : s.dmem =⋆ Mem.Blocks [(s.regs.get64 .rdi, len * 4)] ⋆ R₁)
    (h_v2 : s.dmem =⋆ Mem.Blocks [(s.regs.get64 .rsi, len * 4)] ⋆ R₂) :
    WP.wp scalarproduct_fma3_prog (fun _ s' => s'.dmem = s.dmem) (fun _ _ => False) s := by
  vcgen [scalarproduct_fma3_prog]
    invariants
    -- Loop/label invariants: exact truths that hold every time execution hits each label `l`
    · fun l s' =>
        match l with
        -- Entry: nothing has changed yet
        | "ff_scalarproduct_float_fma3" => s' = s
        -- Main 128B loop: `rdx = len*4`, `rcx` = total rounded down to 128B, `r8` = cursor (< rcx, multiple of 128)
        | ".loop128" => s'.regs.get64 .rdi = s.regs.get64 .rdi ∧ s'.regs.get64 .rsi = s.regs.get64 .rsi
            ∧ (s'.regs.get64 .rdx).toNat = len * 4 ∧ s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
            ∧ (s'.regs.get64 .rcx).toNat % 128 = 0 ∧ (s'.regs.get64 .rcx).toNat ≤ len * 4 ∧ len * 4 < (s'.regs.get64 .rcx).toNat + 128 ∧ (s'.regs.get64 .r8).toNat % 128 = 0 ∧ (s'.regs.get64 .r8).toNat < (s'.regs.get64 .rcx).toNat
        -- Entry to 64B tail: `rcx` = remaining bytes (`64 ≤ rcx < 128`), `r8 + rcx = total bytes`, `r8` is 128B-aligned
        | ".l64" => s'.regs.get64 .rdi = s.regs.get64 .rdi ∧ s'.regs.get64 .rsi = s.regs.get64 .rsi
            ∧ (s'.regs.get64 .rdx).toNat = len * 4 ∧ s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
            ∧ (s'.regs.get64 .rcx).toNat + (s'.regs.get64 .r8).toNat = len * 4 ∧ 64 ≤ (s'.regs.get64 .rcx).toNat ∧ (s'.regs.get64 .rcx).toNat < 128 ∧ (s'.regs.get64 .r8).toNat % 128 = 0
        -- 64B loop body: `rcx = r8 + 64`, and since `len*4 < r8 + 128`, it executes at most ONCE (no backedge!)
        | ".loop64" => s'.regs.get64 .rdi = s.regs.get64 .rdi ∧ s'.regs.get64 .rsi = s.regs.get64 .rsi
            ∧ (s'.regs.get64 .rdx).toNat = len * 4 ∧ s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
            ∧ (s'.regs.get64 .rcx).toNat = (s'.regs.get64 .r8).toNat + 64 ∧ (s'.regs.get64 .r8).toNat + 64 ≤ len * 4 ∧ len * 4 < (s'.regs.get64 .r8).toNat + 128 ∧ (s'.regs.get64 .r8).toNat % 64 = 0
        -- Entry to 32B tail: `rcx` = remaining bytes (`32 ≤ rcx < 64`), `r8` is 64B-aligned
        | ".l32" => s'.regs.get64 .rdi = s.regs.get64 .rdi ∧ s'.regs.get64 .rsi = s.regs.get64 .rsi
            ∧ (s'.regs.get64 .rdx).toNat = len * 4 ∧ s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
            ∧ (s'.regs.get64 .rcx).toNat + (s'.regs.get64 .r8).toNat = len * 4 ∧ 32 ≤ (s'.regs.get64 .rcx).toNat ∧ (s'.regs.get64 .rcx).toNat < 64 ∧ (s'.regs.get64 .r8).toNat % 64 = 0
        -- 32B loop body: `rcx = r8 + 32`, executes at most ONCE
        | ".loop32" => s'.regs.get64 .rdi = s.regs.get64 .rdi ∧ s'.regs.get64 .rsi = s.regs.get64 .rsi
            ∧ (s'.regs.get64 .rdx).toNat = len * 4 ∧ s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
            ∧ (s'.regs.get64 .rcx).toNat = (s'.regs.get64 .r8).toNat + 32 ∧ (s'.regs.get64 .r8).toNat + 32 ≤ len * 4 ∧ len * 4 < (s'.regs.get64 .r8).toNat + 64 ∧ (s'.regs.get64 .r8).toNat % 32 = 0
        -- Entry to 16B tail: `rcx` = remaining bytes (`16 ≤ rcx < 32`), `r8` is 32B-aligned
        | ".l16" => s'.regs.get64 .rdi = s.regs.get64 .rdi ∧ s'.regs.get64 .rsi = s.regs.get64 .rsi
            ∧ (s'.regs.get64 .rdx).toNat = len * 4 ∧ s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
            ∧ (s'.regs.get64 .rcx).toNat + (s'.regs.get64 .r8).toNat = len * 4 ∧ 16 ≤ (s'.regs.get64 .rcx).toNat ∧ (s'.regs.get64 .rcx).toNat < 32 ∧ (s'.regs.get64 .r8).toNat % 32 = 0
        -- 16B loop body: `rcx = r8 + 16`, executes at most ONCE
        | ".loop16" => s'.regs.get64 .rdi = s.regs.get64 .rdi ∧ s'.regs.get64 .rsi = s.regs.get64 .rsi
            ∧ (s'.regs.get64 .rdx).toNat = len * 4 ∧ s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
            ∧ (s'.regs.get64 .rcx).toNat = (s'.regs.get64 .r8).toNat + 16 ∧ (s'.regs.get64 .r8).toNat + 16 ≤ len * 4 ∧ len * 4 < (s'.regs.get64 .r8).toNat + 32 ∧ (s'.regs.get64 .r8).toNat % 16 = 0
        -- Exit: memory and stack pointer are intact
        | "done" => s'.dmem = s.dmem ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp
        | _ => False
    -- Termination measure (variant): must strictly decrease on every loop backedge!
    -- Only `.loop128` can actually jump back to itself (`rcx - r8` shrinks by 128 each round).
    -- `.loop64`, `.loop32`, and `.loop16` run at most 1 iteration, so `0` suffices for them.
    · fun l s' => match l with
        | "ff_scalarproduct_float_fma3" => 2 ^ 64
        | ".loop128" => (s'.regs.get64 .rcx).toNat - (s'.regs.get64 .r8).toNat
        | _ => 0
    with kfinish

/--
  Full C-callable function specification (`funspec`) for `ff_scalarproduct_float_fma3`:
  Wraps `scalarproduct_fma3` (including `ret`) with the Linux System V ABI contract.

  ELI5 differences vs `scalarproduct_fma3_spec`:
  - `s` is the caller's state right BEFORE `call`, while `s₀` inside the invariants is the
    callee's state right AFTER `call` (so the 8-byte return address sits at `s.regs.rsp - 8#64`).
  - `Mem.Mapped` additionally requires that 8-byte return-address stack slot `(rsp - 8, 8)`.
  - `autoframes calling_conv SysV preserves rax rsi rdi r9 r10 r11` automatically proves that
    all callee-saved registers, caller-owned memory, and the return address/stack frame are
    preserved when `ret` returns to the caller.
  - `ensures s' => True` means this spec proves ABI safety and termination (not the float result).
-/
funspec scalarproduct_fma3_funspec "ff_scalarproduct_float_fma3" [Host] [FunDecls]
    [Embeds scalarproduct_fma3]
    (hf : FunDecls.at (label "ff_scalarproduct_float_fma3") = some ⟨scalarproduct_fma3⟩)
    (len : Nat) at s
    requires s.regs.rdx.toBitVec.take 32 = BitVec.ofNat 32 len
      ∧ len % 4 = 0 ∧ 0 < len ∧ len * 4 < 2 ^ 32 ∧ isAligned 16 s.regs.rdi.toBitVec = true
      ∧ Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8), (s.regs.rdi.toBitVec, len * 4),
          (s.regs.rsi.toBitVec, len * 4)] s.dmem
    ensures s' => True
    autoframes calling_conv SysV preserves rax rsi rdi r9 r10 r11 := by
  vcgen [scalarproduct_fma3]
    invariants
    -- Same loop invariants as above, plus `Frame.Regs s s'` (tracks caller-frame register preservation)
    -- and `s'.regs.rsp = s.regs.rsp - 8#64` (the return address pushed by `call` stays untouched on stack).
    · fun {s₀} l s' => match l with
        | "ff_scalarproduct_float_fma3" => s' = s₀
        | ".loop128" => s'.regs.rdx.toNat = len * 4 ∧ s'.dmem = s₀.dmem ∧ Frame.Regs s s'
            ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
            ∧ s'.regs.rcx.toNat % 128 = 0 ∧ s'.regs.rcx.toNat ≤ len * 4 ∧ len * 4 < s'.regs.rcx.toNat + 128 ∧ s'.regs.r8.toNat % 128 = 0 ∧ s'.regs.r8.toNat < s'.regs.rcx.toNat
        | ".l64" => s'.regs.rdx.toNat = len * 4 ∧ s'.dmem = s₀.dmem ∧ Frame.Regs s s'
            ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
            ∧ s'.regs.rcx.toNat + s'.regs.r8.toNat = len * 4 ∧ 64 ≤ s'.regs.rcx.toNat ∧ s'.regs.rcx.toNat < 128 ∧ s'.regs.r8.toNat % 128 = 0
        | ".loop64" => s'.regs.rdx.toNat = len * 4 ∧ s'.dmem = s₀.dmem ∧ Frame.Regs s s'
            ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
            ∧ s'.regs.rcx.toNat = s'.regs.r8.toNat + 64 ∧ s'.regs.r8.toNat + 64 ≤ len * 4 ∧ len * 4 < s'.regs.r8.toNat + 128 ∧ s'.regs.r8.toNat % 64 = 0
        | ".l32" => s'.regs.rdx.toNat = len * 4 ∧ s'.dmem = s₀.dmem ∧ Frame.Regs s s'
            ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
            ∧ s'.regs.rcx.toNat + s'.regs.r8.toNat = len * 4 ∧ 32 ≤ s'.regs.rcx.toNat ∧ s'.regs.rcx.toNat < 64 ∧ s'.regs.r8.toNat % 64 = 0
        | ".loop32" => s'.regs.rdx.toNat = len * 4 ∧ s'.dmem = s₀.dmem ∧ Frame.Regs s s'
            ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
            ∧ s'.regs.rcx.toNat = s'.regs.r8.toNat + 32 ∧ s'.regs.r8.toNat + 32 ≤ len * 4 ∧ len * 4 < s'.regs.r8.toNat + 64 ∧ s'.regs.r8.toNat % 32 = 0
        | ".l16" => s'.regs.rdx.toNat = len * 4 ∧ s'.dmem = s₀.dmem ∧ Frame.Regs s s'
            ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
            ∧ s'.regs.rcx.toNat + s'.regs.r8.toNat = len * 4 ∧ 16 ≤ s'.regs.rcx.toNat ∧ s'.regs.rcx.toNat < 32 ∧ s'.regs.r8.toNat % 32 = 0
        | ".loop16" => s'.regs.rdx.toNat = len * 4 ∧ s'.dmem = s₀.dmem ∧ Frame.Regs s s'
            ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
            ∧ s'.regs.rcx.toNat = s'.regs.r8.toNat + 16 ∧ s'.regs.r8.toNat + 16 ≤ len * 4 ∧ len * 4 < s'.regs.r8.toNat + 32 ∧ s'.regs.r8.toNat % 16 = 0
        | "done" => s'.dmem = s₀.dmem ∧ Frame.Regs s s' ∧ s'.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64
        | _ => False
    -- Same termination measure as `scalarproduct_fma3_spec`
    · fun l s' => match l with
        | "ff_scalarproduct_float_fma3" => 2 ^ 64
        | ".loop128" => s'.regs.rcx.toNat - s'.regs.r8.toNat
        | _ => 0
    simp [scalarproduct_fma3_prog] with kfinish

end State.FfScalarproductFloatFma3
```
