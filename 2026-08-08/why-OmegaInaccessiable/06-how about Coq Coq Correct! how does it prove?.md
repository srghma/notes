In the paper ***"Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq"*** (Sozeau et al., POPL 2020), the authors take a completely different approach to the consistency problem. 

Instead of trying to prove that Coq's type system is consistent (which Gödel's Second Incompleteness Theorem prevents Coq from doing internally without extra axioms), they prove that **Coq's actual type-checking software implementation is 100% bug-free relative to its formal specification**.

---

### 1. The Problem They Solved: TCB vs. TTB

Traditionally, using Coq required trusting two separate things:
1. **The Theory (Metatheory):** The logical rules of the Calculus of Inductive Constructions (CIC).
2. **The Code Base (TCB - Trusted Code Base):** The ~18,000 lines of OCaml code that implement Coq's kernel (the type checker, conversion checker, guard checker, etc.).

Even if the *theory* of CIC is consistent, the *OCaml implementation* can have bugs. In fact, historically, **about one critical bug was found in Coq's OCaml kernel every year**.

The paper moves Coq from a **Trusted Code Base (TCB)** to a **Trusted Theory Base (TTB)**.

---

### 2. How Does the Proof Work?

The project (part of **MetaCoq**) breaks the proof into four main layers:

```
[ Abstract PCUIC Specification (Inductive Rules: Γ ⊢ e : T) ]
                         ▲
                         │ Proven Sound & Complete in Coq
                         ▼
   [ Executable Type Checker in Coq (check_type env ctx e) ]
                         │
                         │ Proven Semantic-Preserving
                         ▼
        [ Certified Erasure (Stripping Proofs/Types) ]
                         │
                         ▼
              [ Executable OCaml Kernel ]
```

#### Step 1: Formalize Coq's Specification (PCUIC)
They define the mathematical rules of Coq inside Coq as an inductive relation called **PCUIC** (*Polymorphic, Cumulative Calculus of Inductive Constructions*).
* $1.1.1
This defines what it means declaratively for a context $\Gamma$, term $e$, and type $T$ to satisfy $\Gamma \vdash e : T$.

#### Step 2: Write an Executable Type Checker
They write an actual Coq program:
$$\text{check\_type} : \text{Environment} \to \text{Context} \to \text{Term} \to \text{Option Type}$$
This program handles weak head normal form (WHNF) reduction, conversion, universe constraint checking, and inductive guard checking.

#### Step 3: Prove Soundness and Completeness
They prove two main theorems inside Coq about `check_type`:

1. **Soundness (No False Positives):** 
   If `check_type env ctx e` returns `Some T`, then there is a valid formal derivation $\Gamma \vdash e : T$ in the PCUIC specification. *(The type checker will never accept an invalid proof or broken term).*
2. **Completeness (No False Negatives):** 
   If a valid derivation $\Gamma \vdash e : T$ exists according to the PCUIC specification, then `check_type env ctx e` will succeed and return `Some T'` (where $T'$ is convertible to $T$).

#### Step 4: Certified Erasure
To run the type checker efficiently, Coq definitions must be extracted to executable OCaml code. They write and formally prove a **proof erasure step** that strips away pure types and proof terms while guaranteeing that the program's runtime execution behavior is strictly preserved.

---

### 3. How does this handle Gödel's Incompleteness Theorem?

The authors explicitly address Gödel's theorem in the paper:

> *"Note that because of Gödel's second incompleteness theorem, there is no hope to prove completely the soundness of the specification of Coq inside Coq (in particular strong normalization)... but it is possible to prove the correctness of the implementation assuming the soundness of the specification."*

Instead of proving **Absolute Consistency** ($\vdash \text{Consistent}(\text{Coq})$), the paper proves **Conditional Correctness**:

$$\text{Soundness of Specification} \implies \text{Executable Type Checker is 100\% Correct}$$

---

### Summary

* **`Lean4LeanModel` (from your previous question):** Uses set-theoretic axioms ($\omega$ inaccessibles) to prove **Semantic Soundness** (that Lean's theory cannot prove `False`).
* **`Coq Coq Correct!` (MetaCoq):** Uses inductive specification matching to prove **Implementation Soundness** (that the executable kernel program perfectly matches the paper specification, eliminating C++/OCaml programming bugs).
