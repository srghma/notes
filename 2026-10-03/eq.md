```lean
theorem test_work (α : Type) (P : α → Prop) (a b : α) (h : Eq a b) (hP : P a) : P b :=
  match b, h with
  | _, Eq.refl a => hP

#print test_work
```

prints

```lean
theorem test_work : ∀ (α : Type) (P : α → Prop) (a b : α), a = b → P a → P b :=
fun α P a b h hP =>
  match b, h with
  | .(a), Eq.refl a => hP
```

which is

```lean
set_option pp.all true in
#print test_work
#print test_work.match_1_1

theorem test_work : ∀ (α : Type) (P : α → Prop) (a b : α) (h : @Eq.{1} α a b) (hP : P a), P b :=
fun (α : Type) (P : α → Prop) (a b : α) (h : @Eq.{1} α a b) (hP : P a) =>
  test_work.match_1_1 α a (fun (b : α) (h : @Eq.{1} α a b) => P b) b h fun (_ : Unit) => hP

@[instance_reducible] def test_work.match_1_1 : ∀ (α : Type) (a : α) (motive : (b : α) → a = b → Prop) (b : α)
  (h : a = b), (∀ (_ : Unit), motive a ⋯) → motive b h :=
fun α a motive b h h_1 =>
  Eq.casesOn (motive := fun a_1 x => b = a_1 → h ≍ x → motive b h) h
    (fun h_2 =>
      Eq.ndrec (motive := fun b => ∀ (h : a = b), h ≍ Eq.refl a → motive b h)
        (fun h h_3 => Eq.symm (eq_of_heq h_3) ▸ h_1 ()) (Eq.symm h_2) h)
    (Eq.refl b) (HEq.refl h)
```

explain to what the `.(a)` is being converted

---

Answer:

```lean
(b, h) - arguments
.(a) turns into the substitution of b with a inside the motive

fun (b : α) (h : @Eq.{1} α a b) => P b
```
