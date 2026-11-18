> where ff_scalarproduct_float_fma3 is defined?
>
> I look for https://github.com/search?q=repo%3AFFmpeg%2FFFmpeg+ff_scalarproduct_float_fma3&type=code
>
> and see only
>
> float ff_scalarproduct_float_fma3(const float *v1, const float *v2, int order);
> in
>
> https://github.com/FFmpeg/FFmpeg/blob/0883d9a2945fe068beb821c6b714c55858d1df46/libavutil/x86/float_dsp_init.c#L74
>
> https://github.com/FFmpeg/FFmpeg/blob/master/libavutil/x86/float_dsp.asm
>
> https://github.com/FFmpeg/FFmpeg/blob/master/libavutil/x86/x86inc.asm
>
> so how it works?

-----------

### 📍 Where `ff_scalarproduct_float_fma3` is defined

It is defined in **`libavutil/x86/float_dsp.asm`** right here:

```nasm
INIT_YMM fma3
cglobal scalarproduct_float, 3,5,8, v1, v2, size, len, offset
```

GitHub code search for `ff_scalarproduct_float_fma3` only finds the C declaration/assignment in `libavutil/x86/float_dsp_init.c` because the assembly symbol name is **synthesized at assemble time** by NASM preprocessor macros in `libavutil/x86/x86util.asm` and `libavutil/x86/x86inc.asm`.

---

### ⚙️ How the symbol name is constructed (Step-by-Step)

1. **Prefix setup (`libavutil/x86/x86util.asm`)** 🏷️
   `float_dsp.asm` starts with `%include "libavutil/x86/x86util.asm"`, which defines FFmpeg's internal prefix before including `x86inc.asm`:
   ```nasm
   %define private_prefix ff
   %define public_prefix avpriv
   %include "libavutil/x86/x86inc.asm"
   ```

2. **Target ISA & register width setup (`INIT_YMM fma3` in `x86inc.asm`)** 🧠
   `INIT_YMM fma3` configures the assembler state for 256-bit AVX/FMA3 code:
   - Sets `avx_enabled` → `1` (so instructions auto-emit VEX encoding and `RET` emits `vzeroupper`) and `mmsize` → `32`
   - Calls `INIT_CPUFLAGS fma3`, which sets:
     - `cpuname` → `fma3`
     - `SUFFIX` → `_fma3`
     - `cpuflags` → `cpuflags_fma3` (`(1<<18) | cpuflags_avx`, transitively enabling `avx`, `sse42`, …, `mmx`)
   - Calls `DEFINE_MMREGS ymm`, which maps `m0`–`m15` (on x86-64; `m0`–`m7` on x86-32) to `ymm0`–`ymm15` and sets `mmtype` → `ymm`.
     *(Note: `xm0`–`xm15` separately target the 128-bit `xmm0`–`xmm15` sub-registers when `mmsize >= 16`, which is why the tail code can write `movss r0m, xm0` even inside a `YMM` function.)*

3. **Symbol mangling & export (`cglobal` → `cglobal_internal` in `x86inc.asm`)** 🔗
   ```nasm
   cglobal scalarproduct_float, 3,5,8, v1, v2, size, len, offset
   ```
   - `cglobal` appends `SUFFIX` and delegates to `cglobal_internal`:
     ```nasm
     cglobal_internal 1, %1 %+ SUFFIX, %2   ; -> scalarproduct_float_fma3
     ```
   - Because the first arg is `1` (unlike `cvisible`, which passes `0` for `avpriv_*` public symbols), `cglobal_internal` prepends `private_prefix %+ _` and runs `mangle(...)`:
     ```nasm
     %xdefine %2 mangle(private_prefix %+ _ %+ %2)
     ```
     - On **Linux / ELF x86-64** (`PREFIX` undefined), `mangle(x)` is `x`, so it emits:
       ```nasm
       global ff_scalarproduct_float_fma3:function hidden
       align function_align
       ff_scalarproduct_float_fma3:
       ```
       (`hidden` avoids PLT/GOT indirection inside `libavutil.so`.)
     - On **Win32 / macOS** (`PREFIX` defined as `_`), `mangle(x)` prepends `_` (`_ff_scalarproduct_float_fma3`) so the C linker resolves `ff_scalarproduct_float_fma3`.

---

### 🧩 What `3,5,8, v1, v2, size, len, offset` & the body do

- **Cross-ABI prologue/epilogue (`3,5,8`)** 🛡️
  - `3`: 3 C arguments (`v1`, `v2`, `size`).
  - `5`: 5 GPRs used (`v1`, `v2`, `size`, `len`, `offset`), automatically mapped across SysV AMD64 (`rdi, rsi, rdx, rcx, r8`), Win64 (`rcx, rdx, r8, r9`, saving/restoring extra callee-saved regs), or x86-32 stack args, with automatic `d`/`q` width suffixes (`sized`, `sizeq`, `lenq`, `offsetq`).
  - `8`: 8 SIMD registers used (`m0`–`m7` = `ymm0`–`ymm7`), so Win64 automatically saves/restores `xmm6`–`xmm7`.
- **Multi-tier FMA3 loop & alignment strategy** 🚀
  - `shl sized, 2` converts element count to byte count (`order * 4`).
  - **`.loop128` (32 floats / iter)**: uses **4 independent accumulators (`m0`–`m3`)** with `fmaddps` (`vfmadd231ps`) to hide FMA pipeline latency. Uses `movups` because buffers guaranteed to be 16-byte aligned for SSE aren't necessarily 32-byte aligned for AVX/FMA3.
  - **`.l64` → `.l32` → `.l16` cascade**: drains remaining 64-byte, 32-byte, and 16-byte chunks cleanly (switching to SSE `xmm` + `movaps` for the 16-byte tail).
  - **Horizontal reduction & return** 🎯: `vextractf128 xmm2, m0, 1` + `addps` folds `ymm0` → `xmm0`, followed by `movhlps` + `shufps`/`addss` down to scalar `float` in `xmm0` (or on 32-bit x86, stores `xm0` to `r0m` and pushes it onto the x87 FPU stack via `fld dword r0m`).
  - `RET` restores any saved registers and emits `vzeroupper` to avoid AVX→SSE transition stalls.

---

### 🔌 How C connects to it (`libavutil/x86/float_dsp_init.c`)

At runtime, `ff_float_dsp_init_x86(AVFloatDSPContext *fdsp)` checks `av_get_cpu_flags()` and overrides `fdsp->scalarproduct_float`:
- SSE baseline → `ff_scalarproduct_float_sse`
- FMA3 (when fast/external) → `ff_scalarproduct_float_fma3`

Here is the upgraded breakdown covering **(1) Standard NASM/x86 vs. User-Defined (`x86inc.asm` / `x86util.asm`)** and **(2) the full assembly code with an ELI5 walkthrough** 🧠✨

===========================
---------------------------

## 1️⃣ Standard NASM / x86 vs. User-Defined (`x86util.asm` / `x86inc.asm`)

Because `x86inc.asm` cleverly overrides some SSE instruction names with macros, it helps to separate what **NASM/CPU hardware provides out of the box** from **FFmpeg/x264's macro layer**:

### 🏛️ Standard Built-in NASM & Native x86/AVX
* **NASM Preprocessor & Directives:**
  * `%include`, `%define`, `%xdefine`, `%assign`, `%undef`, `%macro ... %endmacro`, `%if ... %else ... %endif`, `%ifndef`, `%+` (token pasting)
  * `SECTION .text`, `global ...`, `dword`, `~127`
  * Local labels starting with `.` (`.loop128`, `.l64`, `.l32`, `.l16`, `.loop64`, etc. — NASM automatically scopes them under the nearest parent label `ff_scalarproduct_float_fma3:`)
* **Standard Scalar / Control-Flow x86 Instructions:**
  * `xor`, `shl`, `mov`, `cmp`, `and`, `add`, `jl`, `jge`
  * `fld` (legacy x87 FPU load, used only in the 32-bit `ARCH_X86_64 == 0` return block)
* **Native AVX Instruction & Registers:**
  * `vextractf128` (note the explicit `v` prefix — native AVX instruction)
  * `xmm0`, `xmm1`, `xmm2` (standard 128-bit x86 register names)

---

### 🛠️ User-Defined (`x86util.asm`, `x86inc.asm`, `config.asm`)
* **Prefix & Function Scaffolding:**
  * `private_prefix` (`ff`), `public_prefix` (`avpriv`) — defined in `x86util.asm`
  * `INIT_YMM fma3` — `x86inc.asm` macro (`avx_enabled=1`, `mmsize=32`, `SUFFIX=_fma3`, maps `m0..m15` → `ymm0..ymm15`)
  * `cglobal scalarproduct_float, 3,5,8, ...` — `x86inc.asm` macro (synthesizes `ff_scalarproduct_float_fma3`, marks `global ...:function hidden` on ELF, emits ABI prologue)
  * `RET` (**uppercase!**) — `x86inc.asm` macro (unlike lowercase CPU `ret`, `RET` automatically emits `vzeroupper` when `avx_enabled && mmsize == 32`, restores callee-saved registers, then emits `ret`)
  * `ARCH_X86_64` — FFmpeg build macro (`1` on 64-bit, `0` on 32-bit)
* **Portable Register & Memory Aliases (`x86inc.asm`):**
  * **Vector aliases:** `m0`–`m7` → `ymm0`–`ymm7`; `xm0` → `xmm0`
  * **Named GPRs + width suffixes:** `v1q`, `v2q`, `sized`, `sizeq`, `lenq`, `offsetq`
    * `d` = 32-bit (`dword`, e.g. `sized` → `edx`)
    * `q` = pointer-sized (64-bit on x86-64, 32-bit on x86-32, e.g. `v1q` → `rdi`, `v2q` → `rsi`, `lenq` → `rcx`, `offsetq` → `r8`)
  * **Stack scratch alias:** `r0m` (stack memory slot for arg 0, used on 32-bit x86 to bounce the result from `xmm0` to x87 `st(0)`)
* **Overridden / Virtual SIMD Instructions (`x86inc.asm`):**
  * `xorps`, `movups`, `movaps`, `addps`, `mulps`, `movhlps`, `movss`, `shufps`, `addss`
    * ⚠️ **Plot twist:** Even though these *look* like standard SSE names, `x86inc.asm` wraps them with `AVX_INSTR`. Because `INIT_YMM fma3` set `avx_enabled = 1`, NASM automatically compiles them into **VEX-encoded AVX instructions** (`vxorps`, `vmovups`, `vaddps`, etc.) — which is why 3-operand `xorps m0, m0, m0` and `addps m0, m0, m2` are valid here!
  * `fmaddps`
    * Not a raw CPU mnemonic (x86 hardware uses `vfmadd132ps` / `vfmadd213ps` / `vfmadd231ps`). `fmaddps` is an `x86inc.asm` FMA abstraction macro that picks the right hardware `vfmadd...ps` opcode for the operands (here computing `dst += a * b`).

---

## 2️⃣ Full Assembly Code & ELI5 Analysis 🧸

### 📄 The Function (`libavutil/x86/float_dsp.asm`)

```nasm
; ── ⚙️ Setup & ABI Wrapper ───────────────────────────────────────────────────
INIT_YMM fma3                               ; [x86inc] 256-bit mode: m0..m15=ymm0..ymm15, VEX encoding, SUFFIX=_fma3
cglobal scalarproduct_float, 3,5,8, v1, v2, size, len, offset
                                            ; [x86inc] Emits `ff_scalarproduct_float_fma3` (global hidden on ELF)
                                            ;          3 C args (v1, v2, size), 5 GPRs (+len, offset), 8 YMM regs (m0..m7)

; ── 🚦 Entry & Fast Size Dispatch ─────────────────────────────────────────────
    xor   offsetq, offsetq                  ; [x86]    offset = 0 (byte cursor into v1 & v2)
    xorps      m0, m0, m0                   ; [x86inc] -> vxorps ymm0, ymm0, ymm0 (Bucket #0 = [0,0,0,0,0,0,0,0])
    shl     sized, 2                        ; [x86]    size *= 4 (convert float count -> byte count; zero-extends to sizeq)
    mov      lenq, sizeq                    ; [x86]    len = total bytes
    cmp      lenq, 32                       ; [x86]    Fewer than 32 bytes (< 8 floats)?
    jl   .l16                               ; [x86]      -> Jump straight to 16-byte (4-float) SSE loop
    cmp      lenq, 64                       ; [x86]    Fewer than 64 bytes (< 16 floats)?
    jl   .l32                               ; [x86]      -> Jump straight to 32-byte (8-float) AVX/FMA loop
    xorps    m1, m1, m1                   ; [x86inc] Bucket #1 = 0 (lazy-cleared only when >= 64 bytes)
    cmp      lenq, 128                      ; [x86]    Fewer than 128 bytes (< 32 floats)?
    jl   .l64                               ; [x86]      -> Jump straight to 64-byte (16-float) loop
    and    lenq, ~127                       ; [x86]    Round len down to multiple of 128B (end offset for .loop128)
    xorps    m2, m2, m2                   ; [x86inc] Bucket #2 = 0
    xorps    m3, m3, m3                   ; [x86inc] Bucket #3 = 0

; ── 🚜 Main Loop: 128 bytes (32 floats) per iteration using 4 parallel buckets
.loop128:                                   ; [NASM]   Local label scoped to ff_scalarproduct_float_fma3
    movups   m4, [v1q+offsetq]              ; [x86inc] -> vmovups: load floats 0..7   from v1 (unaligned-safe for 16B ptrs)
    movups   m5, [v1q+offsetq + 32]         ; [x86inc] Load floats  8..15 from v1
    movups   m6, [v1q+offsetq + 64]         ; [x86inc] Load floats 16..23 from v1
    movups   m7, [v1q+offsetq + 96]         ; [x86inc] Load floats 24..31 from v1
    fmaddps  m0, m4, [v2q+offsetq     ], m0 ; [x86inc] FMA4_INSTR -> vfmadd231ps: m0 += m4 * v2[0..7]   (independent pipeline!)
    fmaddps  m1, m5, [v2q+offsetq + 32], m1 ; [x86inc] m1 += m5 * v2[8..15]
    fmaddps  m2, m6, [v2q+offsetq + 64], m2 ; [x86inc] m2 += m6 * v2[16..23]
    fmaddps  m3, m7, [v2q+offsetq + 96], m3 ; [x86inc] m3 += m7 * v2[24..31]
    add   offsetq, 128                      ; [x86]    Advance cursor by 128 bytes (32 floats)
    cmp   offsetq, lenq                     ; [x86]    Reached end of 128-byte blocks?
    jl .loop128                             ; [x86]      -> Repeat if offset < len

; ── 🧺 Merge 4 buckets -> 2 buckets & cascade into leftovers ──────────────────
    addps    m0, m0, m2                     ; [x86inc] -> vaddps: merge Bucket #2 into Bucket #0
    addps    m1, m1, m3                     ; [x86inc] Merge Bucket #3 into Bucket #1 (keep 2 buckets alive in case .l64 runs)
    mov      lenq, sizeq                    ; [x86]    Restore total byte count
    and      lenq, 127                      ; [x86]    len = remaining bytes (size % 128)
    cmp      lenq, 64                       ; [x86]    At least 64 bytes left?
    jge .l64                                ; [x86]      -> Handle 64B tail (still using both m0 & m1)
    addps    m0, m0, m1                     ; [x86inc] < 64B left: merge Bucket #1 into Bucket #0 (now 1 bucket: ymm0)
    cmp      lenq, 32                       ; [x86]    At least 32 bytes left?
    jge .l32                                ; [x86]      -> Handle 32B tail
    vextractf128 xmm2, m0, 1                ; [AVX]    Extract upper 128 bits [4..7] of ymm0 into xmm2
    addps    xmm0, xmm2                     ; [x86inc] -> vaddps: fold 8 floats -> 4 floats in xmm0 ([0+4, 1+5, 2+6, 3+7])
    cmp      lenq, 16                       ; [x86]    At least 16 bytes left?
    jge .l16                                ; [x86]      -> Handle 16B tail
    movhlps  xmm1, xmm0                     ; [x86inc] -> vmovhlps: copy top 2 floats [c, d] of xmm0 into low half of xmm1
    addps    xmm0, xmm1                     ; [x86inc] Fold 4 floats -> 2 floats in xmm0[0..1] = [a+c, b+d]
    movss    xmm1, xmm0                     ; [x86inc] -> vmovss: copy lane 0 (a+c) into xmm1[0]
    shufps   xmm0, xmm0, 1                  ; [x86inc] -> vshufps: slide lane 1 (b+d) into xmm0[0]
    addss    xmm0, xmm1                     ; [x86inc] -> vaddss: xmm0[0] = (a+c) + (b+d) = final scalar float!
%if ARCH_X86_64 == 0                        ; [NASM+cfg] 32-bit x86 C ABI returns floats on the x87 FPU stack, not xmm0
    movss r0m, xm0                          ; [x86inc] Spill xmm0[0] to stack scratch slot r0m
    fld dword r0m                           ; [x86]    Push float onto x87 FPU stack st(0)
%endif                                      ; [NASM]
    RET                                     ; [x86inc] Emits `vzeroupper` (avoid AVX->SSE stall) + pops regs + `ret`

; ── 🧹 Leftover Tier 1: 64 bytes (16 floats) ─────────────────────────────────
.l64:
    and    lenq, ~63                        ; [x86]    Round remaining len down to multiple of 64B (64)
    add    lenq, offsetq                    ; [x86]    len = target end byte offset
.loop64:
    movups   m4, [v1q+offsetq]              ; [x86inc] Load floats 0..7  from v1
    movups   m5, [v1q+offsetq + 32]         ; [x86inc] Load floats 8..15 from v1
    fmaddps  m0, m4, [v2q+offsetq], m0      ; [x86inc] m0 += m4 * v2[0..7]
    fmaddps  m1, m5, [v2q+offsetq + 32], m1 ; [x86inc] m1 += m5 * v2[8..15]
    add   offsetq, 64                       ; [x86]    Advance cursor by 64 bytes
    cmp   offsetq, lenq                     ; [x86]    Done with 64B chunk?
    jl .loop64
    addps    m0, m0, m1                     ; [x86inc] Merge Bucket #1 into Bucket #0
    mov      lenq, sizeq                    ; [x86]    Restore total bytes
    and      lenq, 63                       ; [x86]    len = remaining bytes (size % 64)
    cmp      lenq, 32                       ; [x86]    At least 32 bytes left?
    jge .l32                                ; [x86]      -> Handle 32B tail
    vextractf128 xmm2, m0, 1                ; [AVX]    Fold 8 floats (ymm0) -> 4 floats (xmm0)
    addps    xmm0, xmm2
    cmp      lenq, 16                       ; [x86]    At least 16 bytes left?
    jge .l16                                ; [x86]      -> Handle 16B tail
    movhlps  xmm1, xmm0                     ; [x86inc] Final squeeze: 4 floats -> 1 float in xmm0[0]
    addps    xmm0, xmm1
    movss    xmm1, xmm0
    shufps   xmm0, xmm0, 1
    addss    xmm0, xmm1
%if ARCH_X86_64 == 0
    movss r0m, xm0
    fld dword r0m
%endif
    RET                                     ; [x86inc] `vzeroupper` + `ret`

; ── 🧹 Leftover Tier 2: 32 bytes (8 floats) ──────────────────────────────────
.l32:
    and    lenq, ~31                        ; [x86]    Round remaining len down to multiple of 32B (32)
    add    lenq, offsetq                    ; [x86]    len = target end byte offset
.loop32:
    movups   m4, [v1q+offsetq]              ; [x86inc] Load 8 floats from v1
    fmaddps  m0, m4, [v2q+offsetq], m0      ; [x86inc] m0 += m4 * v2[0..7]
    add   offsetq, 32                       ; [x86]    Advance cursor by 32 bytes
    cmp   offsetq, lenq
    jl .loop32
    vextractf128 xmm2, m0, 1                ; [AVX]    Fold 8 floats (ymm0) -> 4 floats (xmm0)
    addps    xmm0, xmm2
    mov      lenq, sizeq                    ; [x86]    Restore total bytes
    and      lenq, 31                       ; [x86]    len = remaining bytes (size % 32)
    cmp      lenq, 16                       ; [x86]    At least 16 bytes left?
    jge .l16                                ; [x86]      -> Handle 16B tail
    movhlps  xmm1, xmm0                     ; [x86inc] Final squeeze: 4 floats -> 1 float in xmm0[0]
    addps    xmm0, xmm1
    movss    xmm1, xmm0
    shufps   xmm0, xmm0, 1
    addss    xmm0, xmm1
%if ARCH_X86_64 == 0
    movss r0m, xm0
    fld dword r0m
%endif
    RET                                     ; [x86inc] `vzeroupper` + `ret`

; ── 🧹 Leftover Tier 3: 16 bytes (4 floats, SSE-width) ───────────────────────
.l16:
    and    lenq, ~15                        ; [x86]    Round remaining len down to multiple of 16B
    add    lenq, offsetq                    ; [x86]    len = target end byte offset
.loop16:                                    ;          (do-while loop: assumes order >= 4 and multiple of 4 floats)
    movaps   xmm1, [v1q+offsetq]            ; [x86inc] -> vmovaps: aligned 16B load of 4 floats from v1
    mulps    xmm1, [v2q+offsetq]            ; [x86inc] -> vmulps:  xmm1 *= v2[0..3]
    addps    xmm0, xmm1                     ; [x86inc] -> vaddps:  xmm0 += xmm1
    add   offsetq, 16                       ; [x86]    Advance cursor by 16 bytes
    cmp   offsetq, lenq
    jl .loop16
    movhlps  xmm1, xmm0                     ; [x86inc] Final squeeze: [a,b,c,d] -> [a+c, b+d]
    addps    xmm0, xmm1
    movss    xmm1, xmm0                     ; [x86inc] Save (a+c)
    shufps   xmm0, xmm0, 1                  ; [x86inc] Move (b+d) to lane 0
    addss    xmm0, xmm1                     ; [x86inc] xmm0[0] = a+b+c+d
%if ARCH_X86_64 == 0
    movss r0m, xm0
    fld dword r0m
%endif
    RET                                     ; [x86inc] `vzeroupper` + `ret`
```

---

### 🧸 ELI5 Walkthrough: "Multiplying Two Lists & Adding Everything Up"

Imagine you have two long lists of numbers, **`v1`** and **`v2`**, and you want the dot product:
$$\text{total} = (v1[0] \times v2[0]) + (v1[1] \times v2[1]) + \dots$$

#### 1️⃣ Prep the tape measure & first bucket
* `xor offsetq, offsetq`: Start our bookmark `offset` at byte `0`.
* `xorps m0, m0, m0`: Grab an empty 8-slot bucket (`ymm0 = [0,0,0,0,0,0,0,0]`).
* `shl sized, 2`: Each `float` takes **4 bytes**, so multiply `size` by 4 (`<< 2`) to measure in bytes instead of elements.
* **Lazy-check shortcut:** If there are `< 32` bytes (`< 8` floats), skip straight to `.l16`. If `< 64` bytes, skip to `.l32`. Only zero extra buckets (`m1`, `m2`, `m3`) if the list is actually big enough to use them!

#### 2️⃣ `.loop128`: Why 4 buckets (`m0..m3`) instead of 1? 🛒🛒🛒🛒
* `and lenq, ~127`: Round down to chunks of **128 bytes (32 floats)** at a time.
* Instead of tossing everything into 1 bucket `m0`, the CPU uses **4 separate 8-float buckets (`m0`, `m1`, `m2`, `m3`)**:
  * Why? Multiply-add (`fmaddps`) takes ~4–5 clock cycles to finish writing to a bucket. If we used 1 bucket every line, the CPU would sit around waiting for `m0` to finish. With 4 independent buckets, all 4 FMA operations run in parallel in the CPU pipeline! 🚀
* Notice `movups` (**unaligned** load) is used for 32-byte AVX loads: FFmpeg only promises 16-byte alignment on float buffers, not 32-byte alignment, so `movups` safely prevents crashes.
* Once `.loop128` finishes, we combine the 4 buckets down to 2 (`m0 += m2`, `m1 += m3`), mask `sizeq & 127` to see what leftovers remain, and cascade down.

#### 3️⃣ `.l64` → `.l32` → `.l16`: Sweeping up the crumbs 🧹
Any remaining bytes that didn't fit in a 128-byte chunk fall through smaller and smaller sieves:
* **`.l64`** (64 bytes = 16 floats): Uses 2 buckets (`m0`, `m1`), then merges `m0 += m1`.
* **`.l32`** (32 bytes = 8 floats): Uses 1 bucket (`m0`), then folds the 8-float `ymm0` into a 4-float `xmm0` (`vextractf128` + `addps`).
* **`.l16`** (16 bytes = 4 floats): Uses plain 4-float `xmm0`/`xmm1` (`movaps` + `mulps` + `addps`), assuming `order` is a positive multiple of 4 floats (typical FFmpeg DSP contract).

#### 4️⃣ The Final Squeeze: 4 floats → 1 number 🍋
At the end of every branch, `xmm0` holds 4 partial sums `[a, b, c, d]`. We fold it in half twice:
```text
xmm0            = [ a,   b,   c,   d ]
movhlps xmm1    = [ c,   d,   ?,   ? ]   (grab top half)
addps xmm0,xmm1 = [a+c, b+d,  ?,   ? ]   (4 -> 2 numbers!)

movss xmm1,xmm0 = [a+c,  ?,   ?,   ? ]   (save left number)
shufps xmm0,0,1 = [b+d,  ?,   ?,   ? ]   (slide right number into slot 0)
addss xmm0,xmm1 = [a+c+b+d, ?, ?,  ? ]   (2 -> 1 final scalar!)
```
* **64-bit return:** `xmm0` *is* the float return register, so we just run `RET` (`vzeroupper` + `ret`).
* **32-bit return (`ARCH_X86_64 == 0`):** Old 32-bit C ABI expects floats on the x87 FPU stack (`st(0)`), so it bounces `xm0` through memory (`movss r0m, xm0` → `fld dword r0m`) right before `RET`.
