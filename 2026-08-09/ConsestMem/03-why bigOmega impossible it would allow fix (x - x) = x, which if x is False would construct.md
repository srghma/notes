Your diagnosis is exactly right, and it's worth seeing *why* it's right — it's not an accident of how you happened to write `T`, it's a theorem.

**The type mismatch is forced by consistency, not by bad luck.**

Lean's core calculus (the Calculus of Inductive Constructions) is strongly normalizing: every closed, well-typed term built in the trusted kernel — no `sorry`, no unsound axioms — reduces to a normal form in finitely many steps. This has been proven for the underlying calculus (Coquand–Werner and later refinements). So it's not that *this particular* `T` fails to give you a loop — nothing in safe Lean can loop. If Big Omega were constructible, strong normalization would be false, and the whole system would be broken.

**Why it would actually be catastrophic if it worked.**

Suppose you *could* get something of type `T → T` applied to itself to type-check — equivalently, suppose you had a genuine fixed-point operator `fix : (P → P) → P` for arbitrary `P : Prop`. Instantiate `P := False`:

```
fix (fun h => h) : False
```

`False → False` is trivially provable (`id`), so you'd derive `False` directly, with zero other assumptions. That's Curry's paradox. So the reason `omega₁ : T → T` can never be fed to itself isn't a syntactic accident — allowing it would let you prove anything at all. The type discipline you noticed *is* the thing standing between Lean and inconsistency.

**This is literally Girard's paradox, tamed.**

Martin-Löf's original 1971 type theory had `Type : Type`, and Girard showed it's inconsistent via essentially this self-application trick. Hurkens later compressed the argument to about 60 lines. The one ingredient those paradoxes need is a universe of propositions that contains *itself* as a member — `Prop : Prop`, or `Type : Type`. Lean/Coq deliberately avoid this: `Prop` is impredicative (you can quantify over all of `Prop` and land back in `Prop`, which is what makes your `T` even expressible), but `Prop` itself lives in `Type`, and `Type u` lives in `Type (u+1)` — the hierarchy never folds back on itself. That asymmetry between "`Prop` quantifies over `Prop`" and "`Prop` *is* `Prop`" is exactly what blocks Big Omega.

**So: is there another way, inside real Lean? No — provably not**, as long as you stay in the trusted, consistent core. This isn't "no one's found the trick yet"; the trick's existence is equivalent to Lean being unsound.

**What if you step outside the trusted core?** There are escape hatches, but none of them actually build Big Omega — they just opt out of the guarantee:

- `partial def bigOmega : T := littleOmega bigOmega` will elaborate (`T` is inhabited, e.g. by `idT`), but the kernel treats `partial` definitions as opaque constants — it never unfolds or reduces them; the only requirement for soundness is that the declared type is inhabited. So you get a black-box constant, not an actual self-reducing loop inside Lean's logic. `#reduce` on it won't show you an infinite regress; it'll just refuse to unfold.
- `sorry` invokes the explicit "admit" axiom and Lean will flag every downstream result as depending on an unproven assumption.
- An axiom that collapses the universe hierarchy (recreating `Type : Type`) reopens Girard/Hurkens' paradox and gets you straight to `False` — at which point "Big Omega" is moot, since `False` already proves everything, including a term of any type you like, trivially and uninterestingly.

So the honest summary: your `littleOmega : T → T` not being self-applicable is one of the load-bearing walls of the type theory. If you ever find a way around it in unmodified, axiom-clean Lean, you haven't found a clever encoding — you've found an inconsistency bug worth reporting.
