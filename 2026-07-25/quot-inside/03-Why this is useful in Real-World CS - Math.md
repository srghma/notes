1. **Term Rewriting / Lambda Calculus**:
   A single-step $\beta$-reduction $M \to_\beta N$ is **not** symmetric or reflexive. But if you take `Quot (· →_β ·)`, you instantly get the type of **Lambda Terms modulo $\beta$-convertibility**!
2. **Free Groups**:
   You define single-step word reduction $w_1 \cdot x \cdot x^{-1} \cdot w_2 \sim w_1 \cdot w_2$ (not symmetric or transitive). `Quot` on this rule gives you the **Free Group**.
3. **Graph Algorithms**:
   Converting single-step directed transitions into connected components or state equivalences without manually defining paths or transitive closures first.
