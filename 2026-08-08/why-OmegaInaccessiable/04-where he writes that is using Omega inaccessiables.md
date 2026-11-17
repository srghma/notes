In Bruno Barras' paper *"Sets in Coq, Coq in Sets"*, he explicitly mentions using an infinite sequence / infinite number of inaccessible cardinals in two main places:

---

### 1. In the Introduction (Page 1, Paragraph 4)

In the introduction, Barras cites Benjamin Werner's earlier work and notes that building a set-theoretic model for the Calculus of Inductive Constructions (CIC) in ZF set theory requires infinitely many inaccessibles:

```markdown
"The Calculus of Constructions with universes (CCω) does not admit a finite model 
(as shown for instance by Miquel in [5] : a model of intuitionistic Zermelo can 
be built in a subtheory of CCω). This theory can be proven consistent in ZF [4], 
but Werner showed there is little hope that we can have a model of CIC in ZF 
without resorting to an infinite number of inaccessible cardinals."
```

---

### 2. In Section 4: "Model of the Calculus of Constructions with Universes (CCω)" (Page 5)

When formally describing the model construction for $\text{CC}_\omega$ (Calculus of Constructions with an infinite universe hierarchy $u_0, u_1, u_2, \dots$), Barras explicitly states the requirement:

```markdown
"An abstract model of CCω is an abstract model of CC, extended with a sequence 
(ui)_{i∈N} that satisfy the following properties :
∗ ∈ u0    un ∈ un+1    un ⊂ un+1
A ∈ un ∧ (∀x ∈ A, B(x) ∈ un) → Π(A, B) ∈ un
A ∈ ∗ ∧ (∀x ∈ A, B(x) ∈ un) → Π(A, B) ∈ un

As already mentioned, our long term goal is to build models for the Calculus of 
Inductive Constructions, so here we are not going to build a model of CCω under 
minimal assumptions. We require the existence of an infinite sequence of 
inaccessible cardinals."
```

---

### Summary of why he uses it here
In Section 4, each universe $u_n$ in the sequence $(u_i)_{i \in \mathbb{N}}$ corresponds to a Grothendieck universe, which in set theory is formed using an **inaccessible cardinal** $\kappa_n$. To model the entire unbounded sequence $u_0, u_1, u_2, \dots$ of universes simultaneously, he assumes an infinite sequence $(\kappa_n)_{n \in \mathbb{N}}$ of inaccessible cardinals ($\omega$ inaccessibles).
