**No, they do not use inaccessible cardinals.**

Instead, MetaCoq circumvents Gödel's Incompleteness Theorem by making **Strong Normalization an explicit hypothesis** in the theorem statement:

```coq
{normalization_in : NormalizationIn Σ}
```

---

### How this theorem works

Look at the premises of `pcuic_consistent`:

1. `{normalization_in : NormalizationIn Σ}`  
   This is an **unproved hypothesis/parameter** asserting that every term in the environment $\Sigma$ strongly normalizes (terminates).
2. `axiom_free Σ`  
   Asserts that the environment contains no unproved axioms (like `sorry` or arbitrary postulates).
3. `declared_inductive Σ False_pcuic False_mib False_oib`  
   States that `False` is defined as an inductive type with **zero constructors** (`ind_ctors := []`).

#### The Proof Logic inside the snippet:
1. `destruct (pcuic_canonicity ...) as [...]`  
   Because of the `normalization_in` hypothesis, MetaCoq can invoke the **Canonicity Theorem** (`pcuic_canonicity`). Canonicity states: *"If a closed term $t$ has an inductive type, $t$ must evaluate to a constructor or cofixpoint."*
2. `destruct t0; try discriminate ctor.`  
   It checks what constructor $t$ evaluated to.
3. `cbn in H1. rewrite nth_error_nil in H1. discriminate.`  
   Since `False_oib` was defined with `ind_ctors := []` (0 constructors), no constructor exists for $t$ to evaluate to! This creates a contradiction and completes the proof that $t : \text{False}$ is impossible.

---

### Comparison with `Lean4LeanModel`

| Project | Hypothesis Used | Logical Meaning |
| :--- | :--- | :--- |
| **`Lean4LeanModel`** (Lean 4) | `OmegaInaccessibles` | *"Assuming set theory has $\omega$ inaccessible cardinals, Lean is consistent."* (Builds a Set-Theoretic Model) |
| **MetaCoq / MetaRocq** (Coq) | `NormalizationIn Σ` | *"Assuming PCUIC terms strongly normalize, PCUIC is consistent."* (Syntactic Canonicity Proof) |

Neither project violates Gödel's Incompleteness Theorem. Both require an unproved assumption to state consistency: Lean uses a **set-theoretic large cardinal hypothesis**, while MetaCoq uses a **proof-theoretic normalization hypothesis**.
