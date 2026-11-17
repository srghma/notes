**Yes, it is the standard, canonical approach in mathematical logic and computer-checked mathematics.** 

It was not invented for this pull request; rather, using $\omega$ (countably many) inaccessible cardinals to model a type theory with an infinite hierarchy of universes is a textbook method with a history spanning several decades.

---

### Key Milestones in the History of this Idea

1. **Alexander Grothendieck (1960s) – Grothendieck Universes**
   In category theory and algebraic geometry, Grothendieck introduced the concept of a *Grothendieck Universe* so mathematicians could talk about "the set of all small groups" without running into Russell's Paradox. In ZFC set theory, a Grothendieck universe is mathematically identical to a **strongly inaccessible cardinal** $\kappa$.

2. **Benjamin Werner (1997) – *Sets in Types, Types in Sets***
   - **Publication:** Benjamin Werner, "Sets in Types, Types in Sets", *Theoretical Aspects of Computer Software* (TACS 1997), LNCS 1281, pp. 530–546.
   - **URL:** https://doi.org/10.1007/BFb0014566
   Werner constructed set-theoretic models of the **Calculus of Inductive Constructions (CIC)**—the formal foundation underlying proof assistants like Coq and Lean. He established that to model a type theory with universe levels ($U_0, U_1, U_2, \dots$), set theory needs inaccessible cardinals to act as those universe levels.

3. **Bruno Barras (2010) – *Sets in Coq, Coq in Sets***
   - **Publication:** Bruno Barras, "Sets in Coq, Coq in Sets", *Journal of Formalized Reasoning*, Vol. 3, No. 1 (2010), pp. 29–48.
   - **URL:** https://doi.org/10.6092/issn.1972-5787/1695
   Barras extended this work by formalizing set-theoretic models of Coq inside Coq. He explicitly proved that modeling the Calculus of Constructions with an infinite universe hierarchy ($\text{CC}_\omega$) requires **an infinite sequence ($\omega$) of inaccessible cardinals**.

4. **Mario Carneiro (2019) – *The Type Theory of Lean***
   - **Publication:** Mario Carneiro, "The Type Theory of Lean", MS Thesis, Carnegie Mellon University (2019).
   - **URL:** https://github.com/digama0/lean-type-theory/releases/tag/v1.0
   In his CMU Master's thesis, Mario Carneiro (the primary author of Lean's `mathlib` and the `Lean4Lean` project in your PR) formalized the exact type theory of Lean 3 and proved its **equiconsistency** with ZFC set theory plus $\omega$ inaccessible cardinals (often denoted $\text{ZFC}_\omega$).

---

### Why is this the "Standard Approach"?

In dependent type theories like Lean, Coq, and Agda, universes are stratified:
* `Sort 0` ($\text{Prop}$)
* `Sort 1` ($\text{Type}_0$)
* `Sort 2` ($\text{Type}_1$)
* $\dots$
* `Sort n` ($\text{Type}_{n-1}$)

To build a set-theoretic model (semantics) that proves the type checker is sound:
1. $\text{Sort } 0$ is mapped to a set universe bounded by cardinal $\kappa_0$.
2. $\text{Sort } 1$ is mapped to a larger set universe bounded by cardinal $\kappa_1 > \kappa_0$.
3. $\text{Sort } n$ is mapped to $\kappa_n > \kappa_{n-1} > \dots > \kappa_0$.

Because Lean allows universe terms to mention arbitrary natural numbers $n$, giving a set-theoretic interpretation for the *entire* type system requires a sequence of cardinals $\kappa_0 < \kappa_1 < \kappa_2 < \dots$, which is precisely $\omega$ inaccessible cardinals.

### Summary

The theorem in that PR is proving **semantic soundness** for Lean 4 using the exact logical framework established over the last ~30 years:

$$\text{ZFC} + \omega \text{ Inaccessible Cardinals} \implies \text{Consistency of Lean}$$

By framing the theorem with `OmegaInaccessibles`, the project connects Lean's internal typechecker to the standard, well-studied consistency benchmark used across mathematical logic.
