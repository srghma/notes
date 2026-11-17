Based on the 2026 paper (*"Same Coeffect, Different Base: Connecting Two Dominant Approaches to Graded Types"*) and the Granule codebase, here is a detailed breakdown answering your questions:

---

### 1. Is the idea to show that Linear Push Core is isomorphic to Graded Modal Core?

**Partially, but with an important distinction:**

* **The broader goal of the paper**: To establish a comprehensive bridge between the **two dominant lineages of graded type systems**:
  1. **Linear-base lineage** ($\text{LB} \subseteq \text{LC} \subseteq \text{LPC}$): Functions are linear by default ($A \multimap B$), and coeffects/grades are packaged into a modality ($\Box_r A$).
  2. **Graded-base lineage** ($\text{GB} \subseteq \text{GMB} \subseteq \text{GMC}$, and $\text{GPB}$): Arrows are pervasively graded ($A \xrightarrow{r} B$).

* **Why Linear *Push* Core (LPC)?**
  * At the base level, **Linear Base ($\text{LB}$)** and **Graded Modal Base ($\text{GMB}$)** enjoy an **observational isomorphism** ($\text{LB} \cong \text{GMB}$, [ObservationalIso.lean](file:///home/srghma/projects/lean-melearning-Same%20Coeffect,%20Different%20Base-Connecting%20Two%20Dominant%20Approaches%20to%20Graded%20Types-2026/RequestProject/Sec3/Translations/ObservationalIso.lean#L7-L52)).
  * However, when moving to core calculi with products ($\otimes, \times$) and sums ($\oplus, +$), the naive translation $\text{GMC} \to \text{LC}$ is **unsound** (the $\times$ arrow in [diagram.mermaid](file:///home/srghma/projects/lean-melearning-Same%20Coeffect,%20Different%20Base-Connecting%20Two%20Dominant%20Approaches%20to%20Graded%20Types-2026/diagram.mermaid#L47) and [arrow_GMC_LC_unsound](file:///home/srghma/projects/lean-melearning-Same%20Coeffect,%20Different%20Base-Connecting%20Two%20Dominant%20Approaches%20to%20Graded%20Types-2026/RequestProject/Diagram.lean#L137-L144)). This is because pattern matching in $\text{GMC}$ automatically distributes modalities over pairs, which Linear Logic/$\text{LC}$ forbids.
  * Adding explicit distributivity constructs ($\text{push}_\otimes, \text{push}_\oplus, \text{push}_{\mathrm{unit}}$) yields **Linear Push Core ($\text{LPC}$)** ([products-sums-ottput.tex](file:///home/srghma/projects/lean-melearning-Same%20Coeffect,%20Different%20Base-Connecting%20Two%20Dominant%20Approaches%20to%20Graded%20Types-2026/products-sums-ottput.tex#L345-L365)).
  * $\text{LPC}$ and $\text{GMC}$ have **mutual sound embeddings/translations** ($\text{LPC} \leftrightarrow \text{GMC}$) that preserve typing and simulate reduction steps ([arrow_GMC_LPC](file:///home/srghma/projects/lean-melearning-Same%20Coeffect,%20Different%20Base-Connecting%20Two%20Dominant%20Approaches%20to%20Graded%20Types-2026/RequestProject/Diagram.lean#L145-L151)).

---

### 2. Does Granule use Linear Push Core by default, and switch to Graded Modal Core via `language GradedBase`?

* **By default: YES, Granule is Linear Push Core ($\text{LPC}$)**.
  * In default Granule, unadorned arrows `a -> b` are linear, and coeffects live in the modality `a [r]`.
  * Moreover, Granule's pattern matching implicitly distributes box modalities over constructors and tuples (e.g. `let [(x, y)] = p in ...`). As noted in §5.4 and §6.1 of the paper ([discussion-ottput.tex:L72-L78](file:///home/srghma/projects/lean-melearning-Same%20Coeffect,%20Different%20Base-Connecting%20Two%20Dominant%20Approaches%20to%20Graded%20Types-2026/discussion-ottput.tex#L72-L78) and [products-sums-ottput.tex:L360-L362](file:///home/srghma/projects/lean-melearning-Same%20Coeffect,%20Different%20Base-Connecting%20Two%20Dominant%20Approaches%20to%20Graded%20Types-2026/products-sums-ottput.tex#L360-L362)):
    > *"Granule is a linear-base system by default... Granule achieves the same expressivity [as push] implicitly via pattern matching."*

* **With `language GradedBase`: It switches to Graded Base / Graded Poly Base, NOT Graded Modal Core**.
  * When you enable `language GradedBase` in Granule ([examples/graded-base.gr](file:///home/srghma/projects/granule/examples/graded-base.gr#L1-L10)), the arrow itself becomes graded (`a % r -> b`), matching the syntax and semantics of **Graded Base ($\text{GB}$)** ([discussion-ottput.tex:L86-L95](file:///home/srghma/projects/lean-melearning-Same%20Coeffect,%20Different%20Base-Connecting%20Two%20Dominant%20Approaches%20to%20Graded%20Types-2026/discussion-ottput.tex#L86-L95)).
  * In the formal calculi, **Graded Modal Core ($\text{GMC}$)** has an explicit primitive box modality ($\Box_r A$) alongside graded arrows. But in Granule with `GradedBase`, coeffects are placed directly on function arrows or encoded into data types, rather than using primitive modal boxes.
  * Because Granule supports polymorphism (`forall {a : Type}`), Granule under `language GradedBase` corresponds formally to **Graded Poly Base ($\text{GPB}$)** combined with data types ([introduction-ottput.tex:L130-L135](file:///home/srghma/projects/lean-melearning-Same%20Coeffect,%20Different%20Base-Connecting%20Two%20Dominant%20Approaches%20to%20Graded%20Types-2026/introduction-ottput.tex#L130-L135)).

---

### 3. Did only Graded Poly Base (GPB) have type polymorphism / System F / term-on-type dependence?

**YES, exactly correct within the formal calculi of the paper.**

* Among the **7 formal calculi** studied in the paper:
  * **Linear lineage**: Linear Base ($\text{LB}$), Linear Core ($\text{LC}$), Linear Push Core ($\text{LPC}$) — *all simply-typed / monomorphic*.
  * **Graded lineage**: Graded Base ($\text{GB}$), Graded Modal Base ($\text{GMB}$), Graded Modal Core ($\text{GMC}$) — *all simply-typed / monomorphic*.
  * **Graded Poly Base ($\text{GPB}$)**: The **only calculus** in the paper with System F type polymorphism ([Syntax.lean](file:///home/srghma/projects/lean-melearning-Same%20Coeffect,%20Different%20Base-Connecting%20Two%20Dominant%20Approaches%20to%20Graded%20Types-2026/RequestProject/Sec4/Poly/Syntax.lean#L8-L20)):
    $$\text{Terms: } t ::= \dots \mid \Lambda \alpha.\, t \mid t\ @\ A \qquad \text{Types: } A ::= \dots \mid \alpha \mid \forall \alpha.\, B$$

* **Why GPB was introduced**:
  Translating $\text{LB} \to \text{GB}$ in direct style (without a global CPS transformation) requires Church-encoding the graded modality $\Box_r A$:
  $$\Box_r A \triangleq \forall \beta.\ (A \xrightarrow{r} \beta) \xrightarrow{1} \beta$$
  which requires System F type abstraction ($\forall \beta$).

* **Consequence in the diagram**:
  In `linear-calculi-diagram.pdf` (and [diagram.mermaid:L48-L49](file:///home/srghma/projects/lean-melearning-Same%20Coeffect,%20Different%20Base-Connecting%20Two%20Dominant%20Approaches%20to%20Graded%20Types-2026/diagram.mermaid#L48-L49)), translations from $\text{GPB}$ back to $\text{LC}$ or $\text{LPC}$ are marked:
  $$\text{GPB} \dashrightarrow \text{LC / LPC} \quad \text{\textbf{❌ Impossible: Target lacks }} \forall$$
  precisely because none of the other formal core or base calculi support type quantification.
