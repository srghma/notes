```
metarocq/
│
├── template-coq/       # Quoting/unquoting library (reifies Coq terms into Coq ASTs)
│
├── pcuic/              # THE SPECIFICATION & METATHEORY
│   └── theories/
│       ├── PCUICTyping.v            # <--- Declarative typing specification (Σ ;;; Γ |- t : T)
│       ├── PCUICCumulativitySpec.v  # <--- Conversion & cumulativity specification
│       └── PCUICSR.v                # <--- Proof of Subject Reduction
│
├── safechecker/        # THE VERIFIED TYPE-CHECKER IMPLEMENTATION
│   └── theories/
│       ├── PCUICTypeChecker.v       # <--- Executable type checking algorithm
│       └── PCUICSafeChecker.v       # <--- Soundness & completeness proofs
│
└── erasure/            # CERTIFIED ERASURE PIPELINE
    └── theories/                    # <--- Proof stripping / extraction to Untyped Lambda Calculus
```

### **1. Weakening**
- **Files:** 
  - `pcuic/theories/Typing/PCUICWeakeningTyp.v` (local context weakening)
  - `pcuic/theories/Conversion/PCUICWeakeningConv.v` (conversion/reduction weakening)
  - `pcuic/theories/Typing/PCUICWeakeningEnvTyp.v` (global environment weakening)
  - `pcuic/theories/Conversion/PCUICWeakeningEnvConv.v` (environment weakening for conversion)
- **Main theorems:**
  - `weakening_typing` - Typing preserved by extending local context
  - `weakening_red` - Reduction preserved by context extension
  - `weakening_cumul` - Cumulativity preserved by weakening
  - `weakening_env_*` - Various weakening lemmas for global environment extension

### **2. Confluence**
- **File:** `pcuic/theories/PCUICConfluence.v`
- **Key results:**
  - Confluence via parallel reduction diamond property (`PCUICParallelReductionConfluence`)
  - Transitivity of conversion/cumulativity on well-typed terms

### **3. Subject Reduction**
- **File:** `pcuic/theories/PCUICSR.v` (line 840)
- **Main definition:**
  ```rocq prover
  Definition SR_red1 {cf} Σ Γ t T :=
    forall u (Hu : closed_red1 Σ Γ t u), Σ ;;; Γ |- u : T.
  ```

### **4. Principality**
- **File:** `pcuic/theories/PCUICPrincipality.v` (line 74)
- **Main theorem:**
  ```rocq prover
  Theorem principal_type {Γ u A} : Σ ;;; Γ |- u : A ->
    ∑ C, (forall B, Σ ;;; Γ |- u : B -> Σ ;;; Γ ⊢ C ≤ B × Σ ;;; Γ |- u : C).
  ```
- Every typable term has a smallest (principal) type

### **5. Bidirectional Typing**
- **Files:**
  - `pcuic/theories/Bidirectional/BDTyping.v` - Core bidirectional rules
  - `pcuic/theories/Bidirectional/BDToPCUIC.v` (line 105) - Bidirectional → undirected typing
  - `pcuic/theories/Bidirectional/BDFromPCUIC.v` (line 382) - Undirected → bidirectional typing
  - `pcuic/theories/Bidirectional/BDUnique.v` - Inferred types are unique
  - `pcuic/theories/Bidirectional/BDStrengthening.v` (line 475) - Weakening from contexts
- **Key theorems:**
  - `typing_infering` - Every typing derives an infering judgment
  - `typing_checking` - Every typing derives a checking judgment
  - Strengthening: unused variables can be removed from context

### **6. Elimination Restrictions**
- **File:** `pcuic/theories/PCUICElimination.v` (line 1)
- **Definitions:**
  - `SingletonProp` - Singleton elimination from Prop to Type restrictions
  - `Computational` - Computational inductives forbid proof arguments
  - `Subsingleton` - Subsingleton properties of inductives
- These ensure singleton elimination criterion for propositional types

### **7. Canonicity**
- **File:** `pcuic/theories/PCUICCanonicity.v` (line 1)
- **Main theorem:**
  ```rocq prover
  Lemma pcuic_canonicity {cf:checker_flags} {nor : normalizing_flags} Σ 
    {normalization_in: NormalizationIn Σ} t i u args :
    axiom_free Σ -> wf Σ ->
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    { t':term & (Σ ;;; [] |- t' : mkApps (tInd i u) args) * 
                (Σ ;;; [] |- t =s t') * construct_cofix_discr (head t')}.
  ```
- Weak head normal form of term of inductive type is a constructor application

### **8. Consistency**
- **File:** `pcuic/theories/PCUICConsistency.v` (line 1)
- **Main theorem:**
  ```rocq prover
  Theorem pcuic_consistent {cf:checker_flags} {nor : normalizing_flags} Σ
    {normalization_in: NormalizationIn Σ} t False_pcuic :
    declared_inductive Σ False_pcuic False_mib False_oib ->
    wf_ext Σ -> axiom_free Σ ->
    Σ ;;; [] |- t : tInd False_pcuic []  -> False.
  ```
- **Depends on:** `pcuic_canonicity` + `NormalizationIn` (strong normalization postulate)
- Proves PCUIC cannot derive `False` assuming strong normalization
