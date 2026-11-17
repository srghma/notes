2010  [Sets in Coq, Coq in Sets](https://www.lix.polytechnique.fr/page/index.php?username=barras&path=proofs/sets-old/sets.pdf)

2020 [Coq Coq Correct!](https://sozeau.gitlabpages.inria.fr/www/research/publications/Coq_Coq_Correct-POPL20.pdf)

`coq-in-coq` (Benjamin Werner, 1997)
Coq in Sets (Bruno Barras, 2010)

1. https://www.lix.polytechnique.fr/page/index.php?username=barras&path=proofs/sets/
2. https://github.com/barras/cic-model/

MetaCoq / Coq Coq Correct! (Sozeau et al., 2020)

* **What it formalizes:** Full modern Coq (pC(u)IC. **Predicative Calculus of Cumulative Inductive Constructions**).
* **What it proves:** **executable type-checking algorithm** correctly implements Coq's formal typing specification (`check_type t = Some T ↔ Γ ⊢ t : T`).

consistency of HoTT (relative to Kan complex [1](https://github.com/HoTT/book/blob/578b85cc8d586b1677ec4335148adeb443057d24/introduction.tex#L360) [2](https://github.com/HoTT/book/blob/578b85cc8d586b1677ec4335148adeb443057d24/formal.tex#L1185)

consistency vs soundness
