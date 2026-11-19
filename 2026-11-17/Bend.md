> Hvm1 2 3 4 - what is the difference?

The generations are alternate/evolving runtime designs, not small incremental version releases.

| Generation | Implementation | Core model | Main direction | Status |
|---|---|---|---|---|
| **HVM1** | Rust/CUDA-era prototype | Interaction nets | First massively parallel HVM prototype | 2022 prototype; largely historical |
| **HVM2** | Rust interpreter plus C/CUDA backends | Interaction combinators | Stable, low-level parallel runtime | Production-oriented; successor to HVM1 |
| **HVM3** | Haskell | Interaction Calculus | Experimental successor combining HVM1/2 ideas | Work in progress |
| **HVM4** | C | Interaction Calculus | Fast, simplified runtime and superposition support | Pre-launch / experimental |

### HVM1

- Rust implementation.
- Introduced the project’s massively parallel interaction-net runtime.
- The official description calls it a 2022 prototype.
- It is the predecessor of HVM2 and should not be confused with HVM2’s low-level IR.

Repository: [HigherOrderCO/HVM1](https://github.com/HigherOrderCO/HVM1)

### HVM2

- Rust, C and CUDA implementations.
- Uses **interaction combinators**, a specific interaction-net system.
- Has CPU and NVIDIA CUDA execution modes.
- Exposes a low-level IR rather than a friendly source language.
- Its README states it is simpler, faster and more correct than HVM1 and provides long-term support for features described in the paper.
- NVIDIA/CUDA support is documented, although CUDA is described as less stable than C.

Repository: [HigherOrderCO/HVM2](https://github.com/HigherOrderCO/HVM2)

Primary documentation:

- [HVM2 README](https://github.com/HigherOrderCO/HVM2#readme)
- [HVM2 paper](https://github.com/HigherOrderCO/HVM2/blob/main/paper/HVM2.pdf)

### HVM3

- Written in Haskell.
- Implements the **Interaction Calculus** rather than the HVM2 interaction-combinator IR.
- Adds or emphasizes affine/linear lambdas, global substitutions, first-class duplications and superpositions.
- Official README calls it a successor combining HVM1 and HVM2 strengths and a work in progress.
- Intended to compile to standalone C, but the README documents no NVIDIA/CUDA backend.

Repository: [HigherOrderCO/HVM3](https://github.com/HigherOrderCO/HVM3)

### HVM4

- Written in C.
- Is also built around the Interaction Calculus.
- Implements a smaller, direct runtime with features such as:
  - superpositions
  - duplications
  - reduction tracing
  - a collapse operation
- Its README explicitly says: **“you're here before launch. Use at your own risk.”**
- No comparable GPU/CUDA backend is documented in its README.

Repository: [HigherOrderCO/HVM4](https://github.com/HigherOrderCO/HVM4)

In short:

- **HVM1:** original Rust/CUDA prototype
- **HVM2:** optimized Rust/C/CUDA interaction-combinator runtime
- **HVM3:** Haskell research compiler/runtime based on Interaction Calculus
- **HVM4:** newest C-based pre-launch Interaction Calculus runtime

The current **Bend 2 repository does not use any of these HVM runtimes**; it directly emits C, CUDA/Metal, or JavaScript.


> Hvm1 2 3 4 - in main branch - last commit done when ?
> Hvm1 2 3 4 - across all branches inside of them, which branch has most recent commit ?


| Repository | Default branch | Latest commit on `main` | Newest branch head I found |
|---|---|---|---|
| [HVM1](https://github.com/HigherOrderCO/HVM1) | `master` | **Aug 21, 2024** | `main` — Aug 21, 2024 |
| [HVM2](https://github.com/HigherOrderCO/HVM2) | `main` | **Aug 21, 2024** | `main` — Aug 21, 2024 |
| [HVM3](https://github.com/HigherOrderCO/HVM3) | `main` | **Jan 29, 2026** | `main` — Jan 29, 2026 |
| [HVM4](https://github.com/HigherOrderCO/HVM4) | `main` | **May 30, 2026** | `main` — May 30, 2026 |

