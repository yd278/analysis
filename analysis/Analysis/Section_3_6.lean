import Mathlib.Tactic
import Analysis.Section_3_5

/-!
# Analysis I, Section 3.6: Cardinality of sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.


Main constructions and results of this section:

- Cardinality of a set
- Finite and infinite sets
- Connections with Mathlib equivalents

After this section, these notions will be deprecated in favor of their Mathlib equivalents.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.6.1 (Equal cardinality) -/
abbrev SetTheory.Set.EqualCard (X Y:Set) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Example 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0,1,2} {3,4,5} := by
  use open Classical in fun x ↦
    ⟨if x.val = 0 then 3 else if x.val = 1 then 4 else 5, by aesop⟩
  constructor
  · intro; aesop
  intro y
  have : y = (3: Object) ∨ y = (4: Object) ∨ y = (5: Object) := by
    have := y.property
    aesop
  rcases this with (_ | _ | _)
  · use ⟨0, by simp⟩; aesop
  · use ⟨1, by simp⟩; aesop
  · use ⟨2, by simp⟩; aesop

/-- Example 3.6.3 -/
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x:ℕ))) := by
  use fun x ↦  ⟨(((x:ℕ) + (x:ℕ )): nat),
    by
      rw[specification_axiom'']
      use (((x:ℕ) + (x:ℕ )): nat).property
      simp
  ⟩ 
  constructor
  . 
    intro a1 a2 heq
    simp at heq
    have : (a1 : ℕ ) = (a2 : ℕ ) := by
      linarith
    simpa using this
  .
    intro ⟨b,hb⟩ 
    rw[specification_axiom''] at hb
    obtain ⟨hb, hev⟩ := hb 
    obtain ⟨r,hr⟩ := hev 
    use r
    simp
    simp[← hr]

@[refl]
theorem SetTheory.Set.EqualCard.refl (X:Set) : EqualCard X X := by
  use fun x ↦ x
  constructor
  . 
    intro x1 x2 heq
    simpa using heq
  .
    intro b
    use b

@[symm]
theorem SetTheory.Set.EqualCard.symm {X Y:Set} (h: EqualCard X Y) : EqualCard Y X := by
  obtain ⟨f,hf⟩ := h 
  let e : X ≃ Y := Equiv.ofBijective f hf
  use e.invFun
  exact e.symm.bijective

@[trans]
theorem SetTheory.Set.EqualCard.trans {X Y Z:Set} (h1: EqualCard X Y) (h2: EqualCard Y Z) : EqualCard X Z := by
  obtain ⟨f1,hf1⟩ := h1
  obtain ⟨f2,hf2⟩ := h2 
  use f2 ∘ f1
  apply Function.Bijective.comp hf2 hf1

/-- Proposition 3.6.4 / Exercise 3.6.1 -/
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := ⟨ EqualCard, {refl, symm, trans} ⟩

/-- Definition 3.6.5 -/
abbrev SetTheory.Set.has_card (X:Set) (n:ℕ) : Prop := X ≈ Fin n

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) :
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, Setoid.r, EqualCard]

/-- Remark 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n:ℕ) :
    (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)).has_card n := by
      set X := nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n) with hx
      apply (has_card_iff _ _).mpr
      set f : X → Fin n := fun x ↦ by
        /- obtain ⟨xo, hxX⟩ := x -/
        have hxN := specification_axiom x.property
        set xn : nat := ⟨x.val, hxN⟩ 
        have hxX : ↑xn ∈ X := by simp[xn]; exact x.property
        rw[specification_axiom'] at hxX
        set x':ℕ := nat_equiv.symm xn
        set y' := x'-1
        have: y' < n := by omega
        exact Fin_mk n y' this
      use f
      constructor
      . 
        intro x1 x2 heq
        simp only [Subtype.mk.injEq, Object.natCast_inj, f] at heq
        have hx1 := x1.property
        rw[specification_axiom''] at hx1
        obtain ⟨hx1,⟨hl1, hu1⟩ ⟩ := hx1
        set x1n : nat := ⟨x1.val,hx1⟩ 
        have hx2 := x2.property
        rw[specification_axiom''] at hx2
        obtain ⟨hx2,⟨hl2, hu2⟩ ⟩ := hx2
        set x2n : nat := ⟨x2.val,hx2⟩ 
        set x1N := nat_equiv.symm x1n
        set x2N := nat_equiv.symm x2n
        replace hl1 : 0 < x1N := by omega
        replace hl2 : 0 < x2N := by omega
        have tgt := Nat.pred_inj hl1 hl2 heq
        aesop
      .
        intro y
        set y': ℕ := ↑y
        have y'lt := Fin.toNat_lt y
        set x' := y' + 1
        set x :nat := nat_equiv x' with hxx'
        have hxX : (x:Object) ∈ X := by
          rw[specification_axiom']
          simp[x]
          omega
        use ⟨↑x, hxX⟩ 
        simp only[f,Subtype.coe_eta]
        simp only [hxx', Equiv.symm_apply_apply, Fin.coe_inj]
        have: x'-1 = ↑y := by omega
        simp[this]




/-- Example 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a:Object) : ({a}:Set).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by simp)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  use ⟨a, by simp⟩
  have := Fin.toNat_lt y
  simp_all

theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
    (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (
    if x.val = a then 0 else if x.val = b then 1 else if x.val = c then 2 else 3
  ) (by aesop)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  have : y = (0:ℕ) ∨ y = (1:ℕ) ∨ y = (2:ℕ) ∨ y = (3:ℕ) := by
    have := Fin.toNat_lt y
    omega
  rcases this with (_ | _ | _ | _)
  · use ⟨a, by aesop⟩; aesop
  · use ⟨b, by aesop⟩; aesop
  · use ⟨c, by aesop⟩; aesop
  · use ⟨d, by aesop⟩; aesop

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) : X ≠ ∅ := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0); rw [mem_Fin]; use 0, (by omega); rfl
  rw [has_card_iff] at hX
  choose f hf using hX
  have hsurj := hf.2
  -- obtain a contradiction from the fact that `f` is a bijection from the empty set to a
  -- non-empty set.
  specialize hsurj (Fin_mk n 0 (by omega))
  obtain ⟨⟨a,hax⟩ ,ha⟩:= hsurj 
  rw[eq_empty_iff_forall_notMem] at this
  specialize this a
  contradiction

/-- Exercise 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X:Set} : X.has_card 0 ↔ X = ∅ := by
  have hempf: (Fin 0) = ∅ := by aesop
  constructor
  . 
    intro hX
    obtain ⟨f, hf⟩ := hX 
    have e : X ≃ (Fin 0) := Equiv.ofBijective f hf
    have hsurjG : Function.Surjective e.invFun := e.symm.surjective
    set g := e.invFun
    by_contra! hX
    have hx := nonempty_def hX
    obtain ⟨x,hx⟩ := hx 
    specialize hsurjG ⟨x,hx⟩ 
    obtain ⟨ a, hga⟩ := hsurjG
    obtain⟨a, ha⟩ := a 
    rw[eq_empty_iff_forall_notMem] at hempf
    specialize hempf a
    contradiction
  . 
    intro hemp
    rw[has_card_iff]
    set f : X → Fin 0 := fun x ↦ by
      obtain ⟨x, hx⟩ := x 
      rw[eq_empty_iff_forall_notMem] at hemp
      specialize hemp x
      contradiction
    use f
    constructor
    . 
      intro x1 x2
      obtain ⟨x1, hx1⟩ := x1 
      rw[eq_empty_iff_forall_notMem] at hemp
      specialize hemp x1
      contradiction
    rintro ⟨i,hi⟩ 
    rw[eq_empty_iff_forall_notMem] at hempf
    specialize hempf i
    contradiction

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.card_erase {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) (x:X) :
    (X \ {x.val}).has_card (n-1) := by
  -- This proof has been rewritten from the original text to try to make it friendlier to
  -- formalize in Lean.
  have  := pos_card_nonempty h hX
  have ne : Nonempty X := by aesop
  rw [has_card_iff] at hX; choose f hf using hX
  set X' : Set := X \ {x.val}
  set ι : X' → X := fun ⟨y, hy⟩ ↦ ⟨ y, by aesop ⟩
  observe hι : ∀ x:X', (ι x:Object) = x
  choose m₀ hm₀ hm₀f using (mem_Fin _ _).mp (f x).property
  set g : X' → Fin (n-1) := fun x' ↦
    let := Fin.toNat_lt (f (ι x'))
    let : (f (ι x'):ℕ) ≠ m₀ := by
      by_contra!; simp [←this, Subtype.val_inj, hf.1.eq_iff, ι] at hm₀f
      have := x'.property; aesop
    if h' : f (ι x') < m₀ then Fin_mk _ (f (ι x')) (by omega)
    else Fin_mk _ (f (ι x') - 1) (by omega)
  have hg_def (x':X') : if (f (ι x'):ℕ) < m₀ then (g x':ℕ) = f (ι x') else (g x':ℕ) = f (ι x') - 1 := by
    split_ifs with h' <;> simp [g,h']
  have hg : Function.Bijective g := by
    constructor
    . 
      intro x1 x2 heq
      simp only[g] at heq
      by_cases h1 : ↑(f (ι x1)) < m₀ <;>
      by_cases h2 : ↑(f (ι x2)) < m₀ <;>
      simp only [h1, ↓reduceDIte, h2, Subtype.mk.injEq, Object.natCast_inj] at heq
      . 
        rw[← Fin.coe_inj ] at heq
        replace heq := hf.1 heq
        simp only [ι ,Subtype.mk.injEq] at heq
        ext
        exact heq
      . 
        push_neg at h2
        have : (f (ι x2)) = m₀ := by omega
        simp [←this, Subtype.val_inj, hf.1.eq_iff, ι] at hm₀f
        have := x2.property
        aesop
      . 
        push_neg at h1
        have : (f (ι x1)) = m₀ := by omega
        simp [←this, Subtype.val_inj, hf.1.eq_iff, ι] at hm₀f
        have := x1.property
        aesop
      .

        have fne1 : (f (ι x1)) ≠ m₀ := by
          by_contra hcon
          simp [←hcon, Subtype.val_inj, hf.1.eq_iff, ι] at hm₀f
          have := x1.property; aesop
        have fne2 : (f (ι x2)) ≠ m₀ := by
          by_contra hcon
          simp [←hcon, Subtype.val_inj, hf.1.eq_iff, ι] at hm₀f
          have := x2.property; aesop
        have hm0 : 0 ≤ m₀ := by simp
        have hl1 : 0 < (f (ι x1): ℕ ) := by omega
        have hl2 : 0 < (f (ι x2): ℕ ) := by omega
        replace heq := Nat.pred_inj hl1 hl2 heq
        rw[← Fin.coe_inj ] at heq
        replace heq := hf.1 heq
        simp only [ι ,Subtype.mk.injEq] at heq
        ext
        exact heq
    intro y
    set ff := Function.invFun f
    by_cases hy : (y:ℕ) < m₀ 
    .
      set y' := Fin_mk n y (by omega) 
      set x' := ff y'
      have: x' ≠ x := by
        by_contra hcon
        simp[← hcon ,x',ff] at hm₀f
        rw[Function.rightInverse_invFun hf.2] at hm₀f
        aesop
      set x : X' := ⟨x'.val, 
        by
          rw[mem_sdiff]
          refine ⟨x'.property,?_⟩ 
          simp
          push_neg
          contrapose! this
          ext
          exact this
      ⟩ 
      have hιx : ι x = x' := by
        simp[ι, x]
      use x
      simp[g, hιx, x']
      have rightInv :  (f (ff y')) = (y':ℕ ) := by
        rw[Function.rightInverse_invFun hf.2]
      have cond : (f (ff y')) < m₀ := by
        rw[rightInv]
        simp[y']
        exact hy
      simp[cond]
      rw[rightInv]
      simp[y']
    push_neg at hy
    have hyn := Fin.toNat_lt y
    set y' := Fin_mk n (y+1) (by omega)
    set x' := ff y'
    have: x' ≠ x := by
      by_contra hcon
      simp[← hcon ,x',ff] at hm₀f
      rw[Function.rightInverse_invFun hf.2] at hm₀f
      aesop
    set x : X' := ⟨x'.val, 
      by
        rw[mem_sdiff]
        refine ⟨x'.property,?_⟩ 
        simp
        push_neg
        contrapose! this
        ext
        exact this
    ⟩ 
    have hιx : ι x = x' := by
      simp[ι, x]
    use x
    simp[g, hιx, x']
    have rightInv :  (f (ff y')) = (y':ℕ ) := by
      rw[Function.rightInverse_invFun hf.2]
    have cond : ¬ (f (ff y')) <  m₀ := by
      rw[rightInv]
      simp[y']
      omega
    simp[cond]
    rw[rightInv]
    simp[y']
  use g

/-- Proposition 3.6.8 (Uniqueness of cardinality) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- This proof is written to follow the structure of the original text.
  revert X m; induction' n with n hn
  . intro _ _ h1 h2; rw [has_card_zero] at h1; contrapose! h1
    apply pos_card_nonempty _ h2; omega
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  choose x hx using nonempty_def this
  have : m ≠ 0 := by contrapose! this; simpa [has_card_zero, this] using h2
  specialize hn (card_erase ?_ h1 ⟨ _, hx ⟩) (card_erase ?_ h2 ⟨ _, hx ⟩) <;> omega

lemma SetTheory.Set.Example_3_6_8_a: ({0,1,2}:Set).has_card 3 := by
  rw [has_card_iff]
  have : ({0, 1, 2}: Set) = SetTheory.Set.Fin 3 := by
    ext x
    simp only [mem_insert, mem_singleton, mem_Fin]
    constructor
    · aesop
    rintro ⟨x, ⟨_, rfl⟩⟩
    simp only [nat_coe_eq_iff]
    omega
  rw [this]
  use id
  exact Function.bijective_id

lemma SetTheory.Set.Example_3_6_8_b: ({3,4}:Set).has_card 2 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (if x = (3:Object) then 0 else 1) (by aesop)
  constructor
  · intro x1 x2
    aesop
  intro y
  have := Fin.toNat_lt y
  have : y = (0:ℕ) ∨ y = (1:ℕ) := by omega
  aesop

lemma SetTheory.Set.Example_3_6_8_c : ¬({0,1,2}:Set) ≈ ({3,4}:Set) := by
  by_contra h
  have h1 : Fin 3 ≈ Fin 2 := (Example_3_6_8_a.symm.trans h).trans Example_3_6_8_b
  have h2 : Fin 3 ≈ Fin 3 := by rfl
  have := card_uniq h1 h2
  contradiction

abbrev SetTheory.Set.finite (X:Set) : Prop := ∃ n:ℕ, X.has_card n

abbrev SetTheory.Set.infinite (X:Set) : Prop := ¬ finite X

/-- Exercise 3.6.3, phrased using Mathlib natural numbers -/
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M := by
  induction' n with k hk
  . 
    use 0
    intro i
    obtain ⟨i, hi⟩ := i 
    rw[specification_axiom'']at hi
    obtain ⟨hin,hilt⟩ :=hi
    aesop
  set f' : Fin k → nat := fun x ↦ 
    f (Fin_mk (k+1) (x: ℕ) (by have := Fin.toNat_lt x;omega))
  specialize hk f'
  obtain ⟨M,hkm⟩ := hk 
  set new := f (Fin_mk (k+1) k (by omega)) with dnew
  have equiv : ∀ i : Fin (k+1), (hik: i < k) → f i = f' (Fin_mk (k) (Fin.toNat i) (hik))  := by
    intro i hik
    simp[f']
    have:  Fin_mk (k+1) (i :ℕ ) (Fin.toNat_lt i) = i := by
      simp
    rw[this]
  by_cases hnew : (new:ℕ ) ≤ M
  . 
    use M
    intro i
    by_cases hik: (i:ℕ) < k
    . rw[equiv i hik]
      set i' := Fin_mk k (i:ℕ) hik
      exact hkm i'
    push_neg at hik
    have lt := Fin.toNat_lt i
    have :(i:ℕ) = k := by omega
    have : i = Fin_mk (k+1) (k) (by omega) := by
      simp[this]
    rw[this]
    simp[← dnew]
    exact hnew
  push_neg at hnew
  use new
  intro i
  by_cases hik : (i : ℕ) < k
  . rw[equiv i hik]
    set i' := Fin_mk k (i: ℕ ) hik
    specialize hkm i'
    omega
  push_neg at hik
  have lt := Fin.toNat_lt i
  have :(i:ℕ) = k := by omega
  have : i = Fin_mk (k+1) (k) (by omega) := by
    simp[this]
  rw[this]

/-- Theorem 3.6.12 -/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  -- This proof is written to follow the structure of the original text.
  by_contra this; choose n hn using this
  simp [has_card] at hn; symm at hn; simp [HasEquiv.Equiv, Setoid.r, EqualCard] at hn
  choose f hf using hn; choose M hM using bounded_on_finite f
  replace hf := hf.surjective ↑(M+1); contrapose! hf
  peel hM with hi; contrapose! hi
  apply_fun nat_equiv.symm at hi; simp_all

open Classical in
/-- It is convenient for Lean purposes to give infinite sets the ``junk`` cardinality of zero. -/
noncomputable def SetTheory.Set.card (X:Set) : ℕ := if h:X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X:Set} (hX: X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

theorem SetTheory.Set.has_card_to_card {X:Set} {n: ℕ}: X.has_card n → X.card = n := by
  intro h; simp [card, card_uniq (⟨ n, h ⟩:X.finite).choose_spec h]; aesop

theorem SetTheory.Set.card_to_has_card {X:Set} {n: ℕ} (hn: n ≠ 0): X.card = n → X.has_card n
  := by grind [card, has_card_card]

theorem SetTheory.Set.card_fin_eq (n:ℕ): (Fin n).has_card n := (has_card_iff _ _).mp ⟨ id, Function.bijective_id ⟩

theorem SetTheory.Set.Fin_card (n:ℕ): (Fin n).card = n := has_card_to_card (card_fin_eq n)

theorem SetTheory.Set.Fin_finite (n:ℕ): (Fin n).finite := ⟨n, card_fin_eq n⟩

theorem SetTheory.Set.EquivCard_to_has_card_eq {X Y:Set} {n: ℕ} (h: X ≈ Y): X.has_card n ↔ Y.has_card n := by
  choose f hf using h; let e := Equiv.ofBijective f hf
  constructor <;> (intro h'; rw [has_card_iff] at *; choose g hg using h')
  . use e.symm.trans (.ofBijective _ hg); apply Equiv.bijective
  . use e.trans (.ofBijective _ hg); apply Equiv.bijective

theorem SetTheory.Set.EquivCard_to_card_eq {X Y:Set} (h: X ≈ Y): X.card = Y.card := by
  by_cases hX: X.finite <;> by_cases hY: Y.finite <;> try rw [finite] at hX hY
  . choose nX hXn using hX; choose nY hYn using hY
    simp [has_card_to_card hXn, has_card_to_card hYn, EquivCard_to_has_card_eq h] at *
    solve_by_elim [card_uniq]
  . choose nX hXn using hX; rw [EquivCard_to_has_card_eq h] at hXn; tauto
  . choose nY hYn using hY; rw [←EquivCard_to_has_card_eq h] at hYn; tauto
  simp [card, hX, hY]

/-- Exercise 3.6.2 -/
theorem SetTheory.Set.empty_iff_card_eq_zero {X:Set} : X = ∅ ↔ X.finite ∧ X.card = 0 := by
  constructor
  . intro empty
    rw[← has_card_zero] at empty
    split_ands
    . use 0
    apply has_card_to_card empty
  intro ⟨hfin,hcard⟩ 
  obtain ⟨n,hhc⟩ := hfin 
  have: n = 0:= by
    by_contra! hne
    apply has_card_to_card at hhc
    rw[← hhc] at hne
    contradiction
  rwa[this, has_card_zero] at hhc

lemma SetTheory.Set.empty_of_card_eq_zero {X:Set} (hX : X.finite) : X.card = 0 → X = ∅ := by
  intro h
  rw [empty_iff_card_eq_zero]
  exact ⟨hX, h⟩

lemma SetTheory.Set.finite_of_empty {X:Set} : X = ∅ → X.finite := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.1

lemma SetTheory.Set.card_eq_zero_of_empty {X:Set} : X = ∅ → X.card = 0 := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.2

@[simp]
lemma SetTheory.Set.empty_finite : (∅: Set).finite := finite_of_empty rfl

@[simp]
lemma SetTheory.Set.empty_card_eq_zero : (∅: Set).card = 0 := card_eq_zero_of_empty rfl

/-- Proposition 3.6.14 (a) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_insert {X:Set} (hX: X.finite) {x:Object} (hx: x ∉ X) :
    (X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by
      split_ands
      map_tacs[use X.card + 1; apply has_card_to_card]
      all_goals
        obtain ⟨n, hnC⟩ := hX 
        have : X.card = n := by
          apply has_card_to_card hnC
        rw[has_card_iff] at hnC
        obtain ⟨f, hbf⟩ := hnC 
        set f' : (X ∪ {x} : Set) → Fin (X.card + 1) := fun x' ↦ by
          by_cases hx : x' = x
          . 
            exact Fin_mk (X.card + 1) n (by omega) 
          push_neg at hx
          have hx'X : x'.val ∈ X := by aesop
          set i  :=f ⟨x'.val, hx'X⟩
          have hi := Fin.toNat_lt i
          exact Fin_mk (X.card + 1) (i:ℕ ) (by omega)
        use f'
        have frange : ∀ x , (f x :ℕ ) <  n:= by 
          intro x;exact Fin.toNat_lt (f x)
        constructor
        . 
          intro x1 x2 heq
          by_cases hx1 : x1 = x <;>
          by_cases hx2 : x2 = x
          . 
            ext
            rw[hx1,hx2]
          .
            simp only [hx1, ↓reduceDIte, hx2, Fin.coe_inj, f' , Fin.toNat_mk] at heq
            generalize_proofs pf at heq
            specialize frange ⟨x2, pf⟩ 
            linarith
          .
            simp only [hx1, ↓reduceDIte, hx2, Fin.coe_inj, f' , Fin.toNat_mk] at heq
            generalize_proofs pf at heq
            specialize frange ⟨x1, pf⟩ 
            linarith
          . 
            push_neg at hx1 hx2
            have hx1X' := x1.property
            have hx2X' := x2.property
            have hx1X : x1.val ∈ X := by aesop
            have hx2X : x2.val ∈ X := by aesop
            have equ1 : (f' x1 : ℕ ) = (f ⟨x1, hx1X⟩ ) := by
              simp only [hx1, ↓reduceDIte, Fin.toNat_mk, f']
            have equ2 : (f' x2 : ℕ ) = (f ⟨x2, hx2X⟩ ) := by
              simp only [hx2, ↓reduceDIte, Fin.toNat_mk, f']
            rw[Fin.coe_inj,equ1,equ2,← Fin.coe_inj] at heq
            replace heq := hbf.1 heq
            ext
            rwa[Subtype.mk.injEq] at heq
        intro i
        by_cases hi : (i:ℕ ) = n
        . 
          use ⟨x, by aesop⟩ 
          simp [f']
          exact hi.symm
        push_neg at hi
        have lt := Fin.toNat_lt i
        have fin : (i:ℕ) < n := by omega
        have surj := hbf.2
        specialize surj (Fin_mk n (i:ℕ) (fin)  )
        obtain ⟨j , hj⟩ := surj 
        use ⟨j, by aesop⟩ 
        have njX : j ≠ x := by aesop
        simp only [njX, ↓reduceDIte, Subtype.coe_eta, hj, Fin.toNat_mk, Fin.coe_inj, f']


/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by
      choose cY hcY using hY
      induction' cY with y hind generalizing Y
      . 
        rw[has_card_zero] at hcY
        rw[hcY]
        simp[hX]
      . 
        have nonempty_y : Y ≠ ∅ := by
          apply pos_card_nonempty (by omega)  hcY
        apply nonempty_def at nonempty_y
        obtain ⟨yc ,hyc⟩ := nonempty_y 
        set y' : Y := ⟨yc, hyc⟩ 
        set Y' := Y \ {y'.val}
        have hera := card_erase (by omega) hcY y'
        simp at hera
        obtain ⟨hfin,hle⟩  := hind hera
        by_cases hyvalue : y'.val ∈ X
        . 
          have : (X ∪ Y \ {y'.val} ) = X ∪ Y := by
            ext x; simp; constructor
            . rintro (h1|⟨h2,h3⟩ ) <;> tauto
            rintro (h1|h2)
            . tauto
            by_cases x = y' <;> aesop
          rw[← this]
          constructor
          . tauto
          apply has_card_to_card at hera 
          apply has_card_to_card at hcY
          omega
        . 
          have : (X ∪ Y \ {y'.val} ) ∪ {y'.val } = (X ∪ Y)  := by
            ext x; simp; constructor
            . rintro ((h1|⟨h21,h22⟩)|h2) <;> aesop
            rintro (h1|h2) <;> tauto
          rw[← this]
          have : y'.val ∉ (X ∪ Y \ {y'.val}) := by aesop
          obtain ⟨insfin, ins_card⟩  := card_insert hfin this
          split_ands
          . assumption
          rw[ins_card]
          apply has_card_to_card at hera 
          apply has_card_to_card at hcY
          omega
/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
  (hdisj: Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by
    have ufin : (X ∪ Y).finite := (card_union hX hY).1
    choose cY hcY using hY
    induction' cY with y hind generalizing Y
    . 
      rw[has_card_zero] at hcY
      rw[hcY]
      simp
    have nonempty_y : Y ≠ ∅ := by
      apply pos_card_nonempty (by omega)  hcY
    apply nonempty_def at nonempty_y
    obtain ⟨yc ,hyc⟩ := nonempty_y 
    set y' : Y := ⟨yc, hyc⟩ 
    have hy' := y'.property
    have hY'C := card_erase (by omega) hcY y'
    simp at hY'C
    set Y' := Y \ {y'.val} with hY'Y
    have hY' : Y'.finite := by use y
    have hdisj' : Disjoint X Y' := by
      rw[disjoint_iff,eq_empty_iff_forall_notMem] at hdisj ⊢ ;aesop
    have hufin' : (X ∪ Y').finite := (card_union hX hY').1
    have hsum := hind hdisj' hufin' hY'C
    have ins_back : (X ∪ Y) = (X ∪ Y') ∪ {y'.val} := by
      ext x
      simp
      constructor
      . rintro (h1|h2);
        . tauto
        by_cases hx :x=y'.val <;> aesop
      rintro ((h11|h12)|h2) <;> aesop
    have y'niX : y'.val ∉ X := by
      by_contra hin
      have : y'.val ∈ X ∩ Y := by aesop
      rw[disjoint_iff] at hdisj
      aesop
    have y'niu : y'.val ∉ (X ∪ Y') := by aesop

    have hindC : (X ∪ Y).card = (X ∪ Y').card + 1 := by
      rw[ins_back]
      exact (card_insert hufin' y'niu).2
    apply has_card_to_card at hcY
    apply has_card_to_card at hY'C
    omega

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by
      choose Xc hXc using hX
      induction' Xc with k hind generalizing X Y
      . 
        rw[has_card_zero] at hXc
        rw[hXc] at hY
        have : Y = ∅ := by 
          rw[subset_def] at hY
          rw[eq_empty_iff_forall_notMem] at *
          aesop
        rw[this]
        split_ands
        . exact empty_finite
        rw[hXc]
      have nonempty_x : X ≠ ∅ := by
        apply pos_card_nonempty (by omega)  hXc
      apply nonempty_def at nonempty_x
      obtain ⟨xc ,hxc⟩ := nonempty_x 
      set x' : X := ⟨xc, hxc⟩ with hxx'
      have erase := card_erase (by omega) hXc x'
      simp at erase
      set X' := X \ {↑x'}
      -- discuss if xc is in Y
      by_cases hxcY : x'.val ∈ Y
      . 
        set Y' := Y \ { x'.val} with hY'Y
        have : Y' ⊆ X' := by
          simp[X',Y',subset_def]
          rw[subset_def] at hY
          aesop
        obtain ⟨ind1, ind2⟩ := hind this erase 

        have ins_back : Y = Y' ∪ {x'.val} := by
          ext x
          simp[hY'Y]
          constructor
          . intro hxY; tauto
          rintro (hxY1|hxY2) <;> aesop
        have x'niY' : x'.val ∉ Y' := by
          simp[Y']
        obtain ⟨hinsf, hinssum⟩ := card_insert ind1 x'niY'
        rw[ins_back]
        split_ands
        . tauto
        apply has_card_to_card at erase 
        apply has_card_to_card at hXc
        omega
      have : Y ⊆ X' := by
        rw[subset_def] at hY ⊢ 
        aesop
      have ind := hind this erase
      constructor
      . tauto
      apply has_card_to_card at erase 
      apply has_card_to_card at hXc
      omega

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY: Y ⊂ X) :
    Y.card < X.card := by
      obtain ⟨hYf, hYcXc⟩  := card_subset hX hY.1
      rw[lt_iff_le_and_ne]
      refine ⟨hYcXc, ?_⟩ 
      have extra : ∃ xₑ , xₑ ∈ X ∧ xₑ ∉ Y := by
        by_contra! h
        rw[ssubset_def] at hY
        obtain ⟨hsub,hne⟩ := hY 
        rw[← subset_def] at h
        have eq := subset_antisymm Y X hsub h
        contradiction
      choose Xc hXc using hX
      choose xe hxeX hxeY using extra
      have : Xc ≥ 1 := by
        by_contra!
        have :Xc = 0 := by omega
        rw[this,has_card_zero] at hXc
        aesop
      have erase := card_erase this hXc ⟨xe,hxeX⟩ 
      simp at erase
      set X' := (X \ {xe})
      have sub : Y ⊆ X' := by
        rw[subset_def]
        intro x hxy
        have : x ≠ xe := by aesop
        simp[X']
        rw[ssubset_def] at hY
        aesop
      have hX' : X'.finite := by
        use Xc - 1
      obtain ⟨hYf', hYcX'c⟩  := card_subset hX' sub
      apply has_card_to_card at erase
      apply has_card_to_card at hXc
      omega

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) (f: X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by
      choose Xc hXc using hX 
      induction' Xc with k hind generalizing X
      . 
        rw[has_card_zero] at hXc
        set I := image f X with hI
        have : I = ∅ := by aesop
        rw[this]
        simp
      have nonempty_x : X ≠ ∅ := by
        apply pos_card_nonempty (by omega)  hXc
      apply nonempty_def at nonempty_x
      obtain ⟨xc ,hxc⟩ := nonempty_x 
      set x' : X := ⟨xc, hxc⟩ with hxx'
      have erase := card_erase (by omega) hXc x'
      simp at erase
      set X' := X \ {↑x'}
      have hX'X : ∀ x ∈  X' , x ∈  X := by aesop
      set f' : X' → Y := fun x ↦  f ⟨x.val, hX'X x.val x.property⟩ 
      obtain ⟨hifin,hile⟩ := hind f' erase
      set I' := image f' X'
      set I := image f X
      by_cases hin : (f x').val ∈ I'
      . 
        have : I = I' := by
          ext y
          simp only [mem_image f, Subtype.exists, exists_and_left, and_exists_self, mem_image f', I,
            I']
          constructor
          . 
            rintro ⟨a,⟨haX,hfa⟩ ⟩ 
            rw[mem_image f'] at hin
            choose xrep hxrep hfxrep using hin
            by_cases extra : a = x'
            .
              use xrep.val, hxrep
              simp
              rw[hfxrep]
              simpa [extra] using hfa
            push_neg at extra
            use a
            use by aesop
          rintro ⟨a,⟨haX', hfa⟩ ⟩ 
          use a
          use by aesop
        rw[this]
        apply has_card_to_card at hXc
        apply has_card_to_card at erase
        simp[hifin]
        omega
      have : I = I' ∪ {(f x').val} := by
        ext y
        simp only [mem_image f, Subtype.exists, exists_and_left, and_exists_self, mem_union,
          mem_image f', mem_singleton, I, I']
        constructor
        . rintro ⟨a,⟨hax, hfay⟩ ⟩ 
          by_cases extra: a = x'
          . 
            right
            aesop
          left
          aesop
        rintro (⟨a, ⟨haX',hf'ax⟩ ⟩ |h2) 
        . use a ,(hX'X a haX')
        use x', x'.property
        simp[h2.symm]
      rw[this]
      split_ands
      . 
        exact (card_insert hifin hin).1
      have card:= (card_insert hifin hin).2
      apply has_card_to_card at hXc
      apply has_card_to_card at erase
      omega

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (hX: X.finite) {f: X → Y}
  (hf: Function.Injective f) : (image f X).card = X.card := by
    have fin := (card_image hX f).1
    have le := (card_image hX f).2
    set I := image f X
    set g : I → X := fun i ↦ ((mem_image _ _ _).mp i.property).choose
    set g_spec := fun (i:I)↦ ((mem_image f X i).mp i.property).choose_spec
    have: image g I = X := by
      ext x
      rw[mem_image]
      constructor
      . 
        rintro ⟨i,hi,hgi⟩ 
        obtain⟨hgci,hfci⟩  := g_spec i
        aesop
      intro hx
      set y := f ⟨x,hx⟩ 
      have : y.val ∈ I := by aesop
      use ⟨y.val,this⟩ 
      split_ands
      . simp[this]
      obtain ⟨h1,h2⟩ := g_spec ⟨y.val,this⟩ 
      rw[coe_inj] at h2 
      apply hf at h2
      simp[g,h2]
    have ge := (card_image fin g).2
    rw[this] at ge
    omega


/-- Proposition 3.6.14 (e) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by
      choose Xc hXc using hX 
      induction' Xc with k hind generalizing X
      . 
        rw[has_card_zero] at hXc
        rw[hXc]
        have : ((∅ : Set) ×ˢ Y) = ∅ :=by aesop
        rw[this];simp
      have nonempty_x : X ≠ ∅ := by
        apply pos_card_nonempty (by omega)  hXc
      apply nonempty_def at nonempty_x
      obtain ⟨xc ,hxc⟩ := nonempty_x 
      set x' : X := ⟨xc, hxc⟩ with hxx'
      have erase := card_erase (by omega) hXc x'
      simp at erase
      set X' := X \ {↑x'}
      obtain ⟨hfinind, hmulind⟩  := hind erase
      have hdiff : (X ×ˢ Y) = (X' ×ˢ Y) ∪ (({x'.val}:Set) ×ˢ Y) := by
        ext pair
        simp
        constructor
        .
          rintro⟨x,hx,y,hy,hpair⟩ 
          by_cases hextra : x = x'
          . 
            right; aesop
          left;aesop
        rintro (h1|h2) <;> aesop
      rw[hdiff]
      have hdisj : Disjoint (X' ×ˢ Y) (({x'.val}:Set) ×ˢ Y) := by
        rw[disjoint_iff,eq_empty_iff_forall_notMem]
        aesop
      have fstp : ∀ p : (({x'.val}:Set) ×ˢ Y), fst p =⟨ x'.val, by simp⟩ := by
        rintro p 
        have hp :=(fst p).property
        rw[mem_singleton] at hp
        ext;simpa

      choose Yc hYc using hY
      have hextCard: (({x'.val}:Set) ×ˢ Y).has_card Yc  := by
        choose fy hfy using hYc
        use fun p ↦ fy (snd p)
        constructor
        . 
          intro p1 p2 heq
          simp at heq
          rw[← Fin.coe_inj] at heq
          apply hfy.1 at heq
          have : fst p1 = fst p2 := by
            have hp1 := fstp p1
            have hp2 := fstp p2
            rw[hp1,hp2]
          ext
          simp[pair_eq_fst_snd]
          aesop
        intro i
        set a := (hfy.2 i).choose with ha
        have spec := (hfy.2 i).choose_spec
        use mk_cartesian ⟨x',by aesop⟩ a
        simpa only [ha, snd_of_mk_cartesian]
      have hfin : (({x'.val}:Set) ×ˢ Y).finite := by use Yc
      split_ands
      . exact (card_union hfinind hfin).1
      have huni := card_union_disjoint hfinind hfin hdisj
      apply has_card_to_card at hXc
      apply has_card_to_card at erase
      apply has_card_to_card at hextCard
      apply has_card_to_card at hYc
      rw[huni,hextCard,hmulind,hXc,erase,hYc]
      ring

noncomputable def SetTheory.Set.pow_fun_equiv {A B : Set} : ↑(A ^ B) ≃ (B → A) where
  toFun f := ((powerset_axiom f).mp f.property).choose
  invFun f := ⟨(f:Object), by simp[powerset_axiom] ⟩ 
  left_inv f := by
    have spec := ((powerset_axiom f).mp f.property).choose_spec
    simp[spec]
  right_inv f := by simp

lemma SetTheory.Set.pow_fun_eq_iff {A B : Set} (x y : ↑(A ^ B)) : x = y ↔ pow_fun_equiv x = pow_fun_equiv y := by
  rw [←pow_fun_equiv.apply_eq_iff_eq]

lemma SetTheory.Set.unique_empty_power {A : Set} (hA : A.finite ) (f₁ f₂ : ↑(A ^ (∅ :Set))) : f₁ = f₂ := by
  rw[pow_fun_eq_iff f₁ f₂]
  ext ⟨x,hx⟩ 
  by_contra; simp at hx
lemma SetTheory.Set.zero_pow_card_one {A : Set} (hA : A.finite ) : (A ^ (∅:Set)).has_card 1 := by
  use fun x ↦ Fin_mk 1 0 (by simp)
  constructor
  . 
    intro x1 x2 heq
    exact unique_empty_power hA x1 x2
  intro zero
  have f : (∅ :Set) → A := by
    intro ⟨x,hx⟩ ; simp at hx
  use pow_fun_equiv.symm f
  simp 
  have := Fin.toNat_lt zero
  omega
lemma SetTheory.Set.EquivCard_to_finite {A B :Set} (hAB : A ≈ B) : A.finite ↔ B.finite := by
  constructor <;> intro h
  <;> choose n hn using h
  <;> use n
  . apply (EquivCard_to_has_card_eq hAB).mp hn
  apply (EquivCard_to_has_card_eq hAB).mpr hn

lemma SetTheory.Set.singleton_pow_card_eq {A : Set} (hA : A.finite ) {x:Object} : (A ^ ({x}:Set)).has_card A.card := by
  choose Ac hAc using hA
  have : A.card = Ac := by 
    apply has_card_to_card hAc
  rw[this]
  obtain ⟨fA, hfA⟩:= hAc 
  use fun pair ↦ fA (pow_fun_equiv pair ⟨x,by simp⟩)
  constructor
  . intro f1 f2 heq
    simp only at heq
    apply hfA.1 at heq
    apply_fun pow_fun_equiv
    funext x'
    have :x' = ⟨x,by simp⟩  := by aesop
    rwa[this]
  intro num
  have hsurj := hfA.2
  specialize hsurj num
  obtain ⟨a,ha⟩ := hsurj 
  set f : ({x} : Set) → A := fun x ↦ a
  use pow_fun_equiv.symm f
  aesop

noncomputable def SetTheory.Set.fun_extend_equiv {X Y : Set} {x' :Object} (hx: x' ∉ X): ↑(Y ^ (X ∪ ({x'}:Set))) ≃ (Y ^ X) ×ˢ (Y ^ ({x'}:Set)) where
  toFun F := by
    set f := pow_fun_equiv F
    set f1 : X → Y := fun x ↦ f ⟨x.val, by aesop⟩ 
    set f2 : ({x'}:Set) → Y := fun x ↦ f ⟨x.val , by aesop⟩ 
    exact mk_cartesian (pow_fun_equiv.symm f1) (pow_fun_equiv.symm f2)
  invFun pair := by
    set f1 := pow_fun_equiv (fst pair)
    set f2 := pow_fun_equiv (snd pair)
    exact pow_fun_equiv.symm (open Classical in fun x ↦ 
      if hxx' : x = x' then f2 ⟨x,by aesop⟩ 
      else f1 ⟨x, by aesop ⟩ 
    )
  left_inv F := by simp
  right_inv pair := by
    simp only [Equiv.apply_symm_apply, Subtype.coe_eta]
    have heq :=  mk_cartesian_fst_snd_eq pair
    rw[← heq]
    congr
    . 
      apply_fun pow_fun_equiv
      ext x; aesop
    apply_fun pow_fun_equiv
    ext x; obtain ⟨x, hx⟩ := x; 
    simp at hx
    simp[hx]

/-- Proposition 3.6.14 (f) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hY: Y.finite) (hX: X.finite) :
    (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card := by
      choose Xc hXc using hX 
      induction' Xc with k hind generalizing X
      . 
        rw[has_card_zero] at hXc
        rw[hXc]
        have base := zero_pow_card_one hY
        split_ands
        . use 1
        apply has_card_to_card at base
        simp[base]
      have nonempty_x : X ≠ ∅ := by
        apply pos_card_nonempty (by omega)  hXc
      apply nonempty_def at nonempty_x
      obtain ⟨xc ,hxc⟩ := nonempty_x 
      set x' : X := ⟨xc, hxc⟩ with hxx'
      have erase := card_erase (by omega) hXc x'
      simp at erase
      set X' := X \ {↑x'}
      obtain ⟨hfinind, hmulind⟩  := hind erase
      have hx'niX' : x'.val ∉ X' := by aesop
      have hXX' : X = X' ∪ {x'.val} := by
        ext y
        simp[X',hxx']
        constructor
        . 
          intro hy;simp[hy]
          have p := Classical.em ¬y=xc;tauto
        rintro (⟨h11,h12⟩ |h2) 
        . tauto
        aesop

      rw[hXX']
      set Nxt := (Y ^ (X' ∪ {x'.val}))
      set Prv := (Y ^ X')
      set Inc := (Y ^ ({x'.val}:Set))
      have ind : Nxt ≈ (Prv ×ˢ Inc) := by
        use (fun_extend_equiv hx'niX').toFun
        exact (fun_extend_equiv hx'niX').bijective
      have eqcard_inc_y : Inc.has_card Y.card := by
        apply singleton_pow_card_eq hY
      have inc_fin : Inc.finite := by use Y.card
      apply has_card_to_card at erase
      apply has_card_to_card at hXc
      obtain ⟨NxtFin, NxtEq⟩ := card_prod (hfinind) (inc_fin)
      refine ⟨ (EquivCard_to_finite ind).mpr NxtFin, ?_⟩ 
      apply EquivCard_to_card_eq at ind
      apply has_card_to_card at eqcard_inc_y
      rw[ind,NxtEq,← hXX',eqcard_inc_y,hmulind,erase,hXc]
      ring

/-- Exercise 3.6.5. You might find `SetTheory.Set.prod_commutator` useful. -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) := by
      have comm := prod_commutator A B
      use comm
      exact comm.bijective

noncomputable abbrev SetTheory.Set.pow_fun_equiv' (A B : Set) : ↑(A ^ B) ≃ (B → A) :=
  pow_fun_equiv (A:=A) (B:=B)



/-- Exercise 3.6.6. You may find `SetTheory.Set.curry_equiv` useful. -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by
      have curry := curry_equiv (X:=C) (Y:=B) (Z:=A)
      have BCtA :=( pow_fun_equiv' A (B ×ˢ C) ).symm
      have BtA := pow_fun_equiv' A B
      have CtBtA := pow_fun_equiv' ((A ^ B):Set) C
      have commu := prod_commutator B C
      use fun cur ↦ BCtA (curry (BtA.toFun ∘ CtBtA cur) ∘ commu.toFun )
      constructor
      . 
        intro cur1 cur2 heq
        simp at heq
        rw[Function.Surjective.right_cancellable commu.surjective] at heq
        apply curry.injective at heq
        have : CtBtA cur1 = CtBtA cur2 := by
          ext c
          apply congrArg fun f↦ f c at heq
          simp at heq
          simp[heq]
        apply CtBtA.injective this
      intro bcta
      obtain ⟨fbcta, rfl⟩ := BCtA.surjective bcta
      have decomp : ∃ cur, (curry (BtA.toFun ∘ CtBtA cur) ∘ commu.toFun) = fbcta := by
        set fcbta := fbcta ∘ commu.symm 
        have reverted : ∃ cur, curry (BtA.toFun ∘ CtBtA cur) = fcbta:= by
          set fctbta := curry.symm fcbta 
          have uncurried : ∃ cur, BtA.toFun ∘ CtBtA cur = fctbta := by
            set ctfab := BtA.symm ∘ fctbta 
            have : ∃ cur, CtBtA cur = ctfab:=by
              exact CtBtA.surjective ctfab
            obtain ⟨cur, hcur⟩ := this
            use cur
            aesop
          obtain ⟨cur,hcur⟩ := uncurried 
          use cur
          aesop
        obtain ⟨cur, hcur⟩ := reverted 
        use cur
        aesop
      obtain ⟨cur,decomp⟩ := decomp 
      use cur
      aesop



theorem SetTheory.Set.pow_pow_eq_pow_mul (a b c:ℕ): (a^b)^c = a^(b*c) := by ring


theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C:Set) (hd: Disjoint B C) :
    EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by 
    rw[disjoint_iff] at hd
    use fun abac ↦ by
      set f := fst abac
      set s := snd abac
      set ff := pow_fun_equiv f
      set fs := pow_fun_equiv s
      set final : ((B ∪ C):Set)→ A := open Classical in fun x ↦ 
        if hxb: (x.val ∈ B) then ff ⟨x.val, by simp_all only⟩ 
        else fs ⟨x.val, by have hx := x.property; simp_all only[mem_union, false_or]⟩  
      exact pow_fun_equiv.symm final
    constructor
    . intro abac1 abac2 heq
      simp only [EmbeddingLike.apply_eq_iff_eq] at heq
      set f1 := pow_fun_equiv (fst abac1)
      set w1 := pow_fun_equiv (snd abac1)
      set f2 := pow_fun_equiv (fst abac2)
      set w2 := pow_fun_equiv (snd abac2)
      have eqf : f1 = f2 := by
        funext x
        set x' : (B ∪ C :Set) := ⟨x.val ,by aesop⟩ 
        have : x'.val ∈ B := by aesop
        apply congrArg fun f ↦ f x' at heq
        simpa[this,x'] using heq
      have eqw : w1 = w2 := by 
        funext x
        set x' : (B ∪ C :Set) := ⟨x.val ,by aesop⟩ 

        have : x'.val ∉ B := by 
          by_contra this
          have hxC : x'.val ∈ C :=by aesop
          rw[eq_empty_iff_forall_notMem] at hd
          aesop
        apply congrArg fun f ↦ f x' at heq
        simpa[this,x'] using heq
      set fp1 := pow_fun_equiv.symm f1
      have hf1 : fp1 = fst abac1 := by aesop
      set wp1 := pow_fun_equiv.symm w1
      have hw1 : wp1 = snd abac1 := by aesop
      set fp2 := pow_fun_equiv.symm f2
      have hf2 : fp2 = fst abac2 := by aesop
      set wp2 := pow_fun_equiv.symm w2
      have hw2 : wp2 = snd abac2 := by aesop
      have : mk_cartesian fp1 wp1 = mk_cartesian fp2 wp2 := by
        aesop
      have : mk_cartesian fp1 wp1 = abac1 := by
        rw[hf1,hw1]
        simp
      have : mk_cartesian fp2 wp2 = abac2 := by
        rw[hf2,hw2]
        simp
      aesop
    intro F
    simp only [ mem_cartesian, powerset_axiom, exists_prop, exists_exists_eq_and]
    set f := pow_fun_equiv F
    set ff : B → A := fun x ↦ f ⟨x, by aesop⟩ 
    set fs : C → A := fun x ↦ f ⟨x, by aesop⟩ 
    use mk_cartesian (pow_fun_equiv.symm ff) (pow_fun_equiv.symm fs)
    simp only [fst_of_mk_cartesian, Equiv.apply_symm_apply, snd_of_mk_cartesian]
    apply_fun pow_fun_equiv
    simp
    funext x
    by_cases hb : x.val ∈ B
    . aesop
    have hc : x.val ∈ C := by aesop
    simp[hb]
    aesop

theorem SetTheory.Set.pow_mul_pow_eq_pow_add (a b c:ℕ): (a^b) * a^c = a^(b+c) := by ring

/-- Exercise 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
    (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card :=by
    constructor
    .
      rintro ⟨f,hf⟩ 
      have imageC := card_image_inj hA  hf
      have sub : (image f A) ⊆ B := by
        rw[subset_def]
        intro b
        rw[mem_image]
        rintro⟨a,⟨haa,hfa⟩ ⟩ 
        rw[← hfa]
        exact (f a).property
      have subC := card_subset hB sub
      aesop
    intro hle
    choose Ac hAc using hA
    have hAc' := has_card_to_card hAc
    choose fA hfA using hAc
    choose Bc hBc using hB
    have hBc' := has_card_to_card hBc
    choose fB hfB using hBc
    set eA := Equiv.ofBijective fA hfA
    set eB := Equiv.ofBijective fB hfB
    use fun x ↦ by
      exact eB.symm  (Fin_mk Bc (eA x) (by have := Fin.toNat_lt (eA x);omega))
    intro a1 a2 heq
    simp at heq
    rw[coe_inj] at heq
    apply eA.injective heq

/-- Exercise 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
  (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by
    have hA' : Nonempty A := by
      apply nonempty_def at hA;simp[hA]
    set g := Function.invFun f
    use g
    exact Function.invFun_surjective hf

/-- Exercise 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by
      choose Bc hBc using hB
      induction' Bc with k hind generalizing B
      . 
        rw[has_card_zero] at hBc
        rw[hBc]
        have : A ∩ (∅ :Set) = ∅ := by
          ext a
          simp
        simp[this]
      have nonempty_B := pos_card_nonempty (by omega) hBc
      apply nonempty_def at nonempty_B
      choose b hb using nonempty_B
      set b' : B := ⟨b,hb⟩ 
      have erase := card_erase (by omega) hBc b'
      simp at erase
      set B' := B \ {b'.val}
      specialize hind erase
      by_cases hbA : b ∈ A
      . 
        have huniind : (A ∪ B') = (A ∪ B) := by
          ext x
          by_cases x = b <;> aesop
        have hintind : (A ∩ B')  ∪ {b} = (A ∩ B) := by
          ext x
          simp[B']
          constructor
          . aesop
          tauto
        have hinsert : b ∉ A ∩ B' := by aesop
        have hintFin : (A ∩ B').finite := by
          have : (A ∩ B') ⊆ A := by rw[subset_def] ;aesop
          exact (card_subset hA this).1
        have hCinsert := (card_insert hintFin hinsert).2
        apply has_card_to_card at erase
        apply has_card_to_card at hBc
        simp [← huniind,← hintind,hCinsert]
        omega
      have huniind : (A ∪ B') ∪ {b} = (A ∪ B) := by
        ext x
        by_cases x = b <;> aesop
      have hintind : (A ∩ B')  = (A ∩ B) := by
        ext x
        aesop
      have huniFin : (A ∪ B').finite  := by
        have : B'.finite := by use k
        exact (card_union hA this).1
      have hinsert : b ∉ (A ∪ B') := by aesop
      have hCinsert := (card_insert huniFin hinsert).2
      apply has_card_to_card at erase
      apply has_card_to_card at hBc
      rw[← huniind,← hintind]
      omega

/-- Exercise 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
  (hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by
    contrapose! hAcard with hone
    have fact : (iUnion _ A).finite ∧ (iUnion _ A).card ≤ n := by
      induction' n with k hind
      . -- case zero
        have : (Fin 0).iUnion A = ∅ := by
          by_contra! ne
          obtain ⟨x, hx⟩ := nonempty_def ne 
          rw[mem_iUnion] at hx
          obtain ⟨⟨a,ap⟩,_ ⟩:= hx
          simp at ap
        simp[this]
      -- induction steps
      set A': (Fin k) → Set := fun i ↦ A (Fin_embed k (k+1) (by omega) i)
      have hA' : ∀ i' , (A' i').finite := by
        intro i'
        set i := Fin_embed k (k+1) (by omega) i'
        specialize hA i
        aesop
      have hone' : ∀ i', (A' i').card < 2 := by
        intro i'
        set i := Fin_embed k (k+1) (by omega) i'
        specialize hone i
        aesop
      obtain ⟨hPrvFin, hPrvLt⟩:= hind hA' hone'
      set Prv := (Fin k).iUnion A'
      set Nxt := (Fin (k+1)).iUnion A
      have hInc : Nxt = Prv ∪ A (Fin_mk (k+1) k (by omega)) := by
        ext x
        simp[Nxt,Prv,mem_iUnion]
        constructor
        . -- mp
          rintro ⟨i ,⟨hinat, hilt⟩,hxA ⟩ 
          by_cases hcase : nat_equiv.symm ⟨i,hinat⟩ = k 
          . right
            have : Fin_mk (k + 1) k (by simp) = ⟨i,by simp; use hinat, hilt⟩ := by simp[← hcase]
            simpa [this]
          replace hcase : nat_equiv.symm ⟨i,hinat⟩ < k := by omega
          left
          use i, by use hinat
        -- mpr
        rintro (⟨i, ⟨hinat,hilt⟩,hxA ⟩ | h)  
        . 
          use i, by use hinat; omega
        use (k:nat), by use (k:nat).property; simp
        simp[h]
      have hIncFin := hA (Fin_mk (k+1) k (by omega))
      obtain ⟨hIndFin, hIndLt⟩ := card_union hPrvFin hIncFin 
      simp[hInc,hIndFin]
      have hIncLt := hone (Fin_mk (k+1) k (by omega)) 
      set Inc := A (Fin_mk (k+1) k (by omega))
      omega
    exact fact.2


lemma SetTheory.Set.pair_card_two {x1 x2 : Object} : x1 ≠ x2 ↔ ({x1, x2} : Set).has_card 2 := by
  constructor
  .
    intro hne
    use open Classical in fun x ↦ if x = x1 then Fin_mk 2 0 (by simp) else Fin_mk 2 1 (by simp)
    constructor
    . 
      intro s1 s2 heq
      have hs1 := s1.property
      have hs2 := s2.property
      by_cases h1:  s1.val = x1 <;>
      by_cases h2:  s2.val = x1 <;>
      aesop
    intro num 
    by_cases h : 0 = Fin.toNat num
    . use ⟨x1, by simp⟩ 
      simpa
    use ⟨x2,by simp⟩ 
    simp[hne.symm]
    have hlt := Fin.toNat_lt num          
    omega
  rintro ⟨f,hf⟩ 
  by_contra! heq
  have eq := Equiv.ofBijective f hf
  set s1 := eq.symm (Fin_mk 2 0 (by simp))
  set s2 := eq.symm (Fin_mk 2 1 (by simp))
  have : s1 ≠ s2 := by aesop
  have hs1 := s1.property
  have hs2 := s2.property
  simp[heq] at hs1 hs2
  have heq : s1.val = s2.val := by
    simp[hs1,hs2]
  rw[coe_inj] at heq
  contradiction

/-- Exercise 3.6.11 -/
theorem SetTheory.Set.two_to_two_iff {X Y:Set} (f: X → Y): Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by
      constructor
      . --  mp Inj → 2 to 2
        intro hinj S hSX hSC
        apply has_card_to_card
        apply card_to_has_card (by simp) at hSC
        choose fSC hfSC using hSC
        have eSC := Equiv.ofBijective  fSC hfSC
        set fI2 : (image f S) → (Fin 2) := fun i ↦ by
          obtain⟨i,hi⟩:= i 
          rw[mem_image] at hi
          set x := hi.choose
          have hxS := hi.choose_spec.1
          exact eSC ⟨x, hxS⟩ 
        have hbij : Function.Bijective fI2:= by
          constructor
          . -- injective
            intro i1 i2 heq
            simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, fI2] at heq
            rw[coe_inj] at heq
            have hi1 := i1.property
            have hi2 := i2.property
            rw[mem_image] at hi1 hi2
            have spec1 := hi1.choose_spec.2
            have spec2 := hi2.choose_spec.2
            ext
            rw[← spec1,← spec2,coe_inj]
            simp[heq]
          -- surjective
          intro num
          simp only [fI2]
          set s := eSC.symm num with hs
          have snum : eSC s = num := by aesop
          rw[← snum]
          set sx : X := ⟨s, hSX s.val s.property⟩ with hsx
          set y := f sx
          have  hyi : y.val ∈ image f S := by
            rw[mem_image]
            use sx
            split_ands
            . simp[sx]; exact s.property
            simp[y]
          obtain ⟨sp1,sp2⟩ := ((mem_image _ _ _).mp hyi).choose_spec
          rw[coe_inj] at sp2
          simp[y] at sp2
          apply hinj at sp2
          use ⟨y,hyi⟩ 
          simp [sp2]
          rfl
        use fI2
      intro hS
      intro x1 x2 heq
      contrapose! heq with hne
      have hone : x1.val ≠ x2.val := by aesop
      rw[pair_card_two] at hone
      set S : Set := {x1.val,x2.val} with heS
      specialize hS S (by
        rw[subset_def]
        aesop
      )
      apply has_card_to_card at hone
      specialize hS hone
      apply card_to_has_card (by simp) at hS
      set I := image f S
      have : I = {(f x1).val, (f x2).val} := by aesop
      rw[this] at hS
      rw[← pair_card_two] at hS
      contrapose! hS
      simp[hS]

/-- Exercise 3.6.12 -/
def SetTheory.Set.Permutations (n: ℕ): Set := (Fin n ^ Fin n).specify (fun F ↦
    Function.Bijective (pow_fun_equiv F))

/-- Exercise 3.6.12 (i), first part -/
theorem SetTheory.Set.Permutations_finite (n: ℕ): (Permutations n).finite := by
  have lemma1 : Permutations n ⊆  (Fin n ^ Fin n) := specify_subset _
  have lemma2 : (Fin n ^ Fin n).finite  := (card_pow (by aesop) (by aesop)).1
  exact (card_subset lemma2 lemma1).1
/- To continue Exercise 3.6.12 (i), we'll first develop some theory about `Permutations` and `Fin`. -/

noncomputable def SetTheory.Set.Permutations_toFun {n: ℕ} (p: Permutations n) : (Fin n) → (Fin n) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  exact this.choose.choose

theorem SetTheory.Set.Permutations_bijective {n: ℕ} (p: Permutations n) :
    Function.Bijective (Permutations_toFun p) := by
      set f := Permutations_toFun p with df
      simp only[Permutations_toFun] at df
      have := p.property
      simp only [Permutations, specification_axiom'', powerset_axiom] at this
      have spec := this.choose_spec
      have spec_spec := this.choose.choose_spec
      aesop

theorem SetTheory.Set.Permutations_inj {n: ℕ} (p1 p2: Permutations n) :
    Permutations_toFun p1 = Permutations_toFun p2 ↔ p1 = p2 := by
      refine ⟨?_, by aesop⟩ 
      intro heq
      have dp1 := p1.property
      have dp2 := p2.property
      simp only [Permutations, specification_axiom'', powerset_axiom] at dp1 dp2
      ext
      have ss1 := dp1.choose.choose_spec
      have ss2 := dp2.choose.choose_spec
      rw[← ss1,← ss2]
      simp only[Permutations_toFun] at heq
      simpa

/-- This connects our concept of a permutation with Mathlib's `Equiv` between `Fin n` and `Fin n`. -/
noncomputable def SetTheory.Set.perm_equiv_equiv {n : ℕ} : Permutations n ≃ (Fin n ≃ Fin n) := {
  toFun := fun p => Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)
  invFun := fun e => ⟨pow_fun_equiv.symm e, by simp only[Permutations, specification_axiom',Equiv.apply_symm_apply, Equiv.bijective] ⟩ 
  left_inv p := by 
    -- prepare the choose_spec
    have property := by
      have := p.property
      simp only [Permutations, specification_axiom'', powerset_axiom] at this
      exact this
    have spec := property.choose.choose_spec

    -- body of the proof
    simp only
    have fbij := Permutations_bijective p
    -- This is the function corresponding to p
    set f := Permutations_toFun p with df
    symm at df
    -- This is the equivalents generated by f, as well as toFun p
    set e := Equiv.ofBijective f fbij with de
    symm at de
    have rfl_e_f : e = f:= by rfl
    -- now we want to prove invFun e = p
    -- get the powerset element pow_e
    set pow_e :=  pow_fun_equiv.symm e with d_pow_e
    symm at d_pow_e
    -- finally show that pow_e is equivalent to p
    aesop
  right_inv equiv := by
    simp only
    -- Obtain the powerset form of equiv
    have hbij := equiv.bijective
    set pow := pow_fun_equiv.symm equiv with dpow
    have ppow : pow_fun_equiv pow = equiv := by aesop
    have pow_is_per : pow.val ∈ Permutations n := by
      simp only[Permutations, specification_axiom'',ppow]
      use pow.property
    have per_to_fun_rfl : Permutations_toFun ⟨pow, pow_is_per⟩ = equiv := by 
      simp only [Permutations_toFun]
      have pp := pow_is_per
      simp only [Permutations, specification_axiom'', powerset_axiom] at pp
      have pspec := pp.choose.choose_spec
      rw[← coe_of_fun_inj,pspec]
      simp[dpow]; rfl
    aesop
}

/- Exercise 3.6.12 involves a lot of moving between `Fin n` and `Fin (n + 1)` so let's add some conveniences. -/

/-- Any `Fin n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.castSucc`. -/
def SetTheory.Set.Fin.castSucc {n} (x : Fin n) : Fin (n + 1) :=
  Fin_embed _ _ (by omega) x

@[simp]
lemma SetTheory.Set.Fin.castSucc_inj {n} {x y : Fin n} : castSucc x = castSucc y ↔ x = y := by
  constructor
  pick_goal 2; aesop
  intro heq; simp [castSucc, Fin_embed] at heq
  ext; assumption


@[simp]
theorem SetTheory.Set.Fin.castSucc_ne {n:ℕ} (x : Fin n) : castSucc x ≠ n := by
  have lt := Fin.toNat_lt x
  have : x≠ n := by omega
  unfold castSucc Fin_embed
  simp
  omega

/-- Any `Fin (n + 1)` except `n` can be cast to `Fin n`. Compare to Mathlib `Fin.castPred`. -/
noncomputable def SetTheory.Set.Fin.castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : Fin n :=
  Fin_mk _ (x : ℕ) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.castSucc_castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) :
    castSucc (castPred x h) = x := by
      unfold castSucc castPred
      simp

@[simp]
theorem SetTheory.Set.Fin.castPred_castSucc {n} (x : Fin n) (h : ((castSucc x : Fin (n + 1)) : ℕ) ≠ n) :
    castPred (castSucc x) h = x := by
      unfold castSucc castPred
      simp


/-- Any natural `n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.last`. -/
def SetTheory.Set.Fin.last (n : ℕ) : Fin (n + 1) := Fin_mk _ n (by omega)
lemma SetTheory.Set.iUnion_increament {n : ℕ } {S : Fin (n+1) → Set} :
    (Fin (n+1)).iUnion S = (Fin n).iUnion (fun i ↦ S (Fin.castSucc i)) ∪ S (Fin.last n) := by
      ext x
      simp only[mem_union, mem_iUnion]
      constructor
      . 
        rintro ⟨a, hxa⟩ 
        by_cases hn :a = n
        . 
          right
          simpa only [Fin.last, Fin_mk, ← hn, Fin.coe_toNat, Subtype.coe_eta]
        left
        use Fin.castPred a hn
        simpa
      rintro ( ⟨i',hi⟩ | h2 )
      use Fin.castSucc i'
      use Fin.last n

lemma SetTheory.Set.iUnion_pred_disjoint_last { n: ℕ } {S : Fin (n+1) → Set} 
  (hSd : Pairwise fun i j => Disjoint (S i) (S j)) :
    Disjoint ((Fin n).iUnion (fun i' ↦ S (Fin.castSucc i'))) (S (Fin.last n)) := by

      rw[disjoint_iff,eq_empty_iff_forall_notMem]
      intro x
      by_contra hxin
      rw[mem_inter] at hxin
      obtain ⟨hPrv, hLst⟩ := hxin 
      rw[mem_iUnion] at hPrv
      obtain ⟨i', hPrvi'⟩ := hPrv
      have sne := Fin.castSucc_ne i'
      set i := Fin.castSucc i'
      set j := Fin.last n
      have : (j:ℕ) = n := by simp
      have hne : i ≠ j := by
        contrapose! sne
        rwa [Fin.coe_inj, this] at sne
      have :=hSd hne
      simp only[disjoint_iff,eq_empty_iff_forall_notMem] at this
      specialize this x
      simp_all

/-- Now is a good time to prove this result, which will be useful for completing Exercise 3.6.12 (i). -/
theorem SetTheory.Set.card_iUnion_card_disjoint {n m: ℕ} {S : Fin n → Set}
    (hSc : ∀ i, (S i).has_card m)
    (hSd : Pairwise fun i j => Disjoint (S i) (S j)) :
    ((Fin n).iUnion S).finite ∧ ((Fin n).iUnion S).card = n * m := by
      -- we prove by induction
      induction' n with k hind
      . -- case 0 empty sets
        have fact : ((Fin 0).iUnion S).has_card 0 := by
          set f : ((Fin 0).iUnion S) → Fin 0 := fun ⟨x,hx⟩  ↦ by
            simp[mem_iUnion] at hx
          use f
          rw[Function.bijective_iff_existsUnique]
          rintro ⟨x,hx⟩ 
          simp at hx
        split_ands
        . use 0
        apply has_card_to_card at fact
        simpa
      -- induction steps
      set S' : Fin k → Set := fun i ↦ S (Fin.castSucc i)
      have hS'c : ∀ i, (S' i).has_card m := by
        intro i'; have hSi := hSc (Fin.castSucc i')
        simpa[S']
      have hS'd : Pairwise fun i' j' ↦ Disjoint (S' i') (S' j'):= by
        intro i' j' hne'
        have hne : (Fin.castSucc i') ≠ (Fin.castSucc j') := by 
          contrapose! hne'
          rwa [Fin.castSucc_inj] at hne'
        have hd := (hSd hne) 
        aesop
      --- get properties for Prv
      obtain⟨hPrvFin,hPrvCar⟩ := hind hS'c hS'd
      
      set Prv := (Fin k).iUnion S'
      set Nxt := (Fin (k+1)).iUnion S
      set Inc := S (Fin.last k)
      have hinc : Nxt = Prv ∪ Inc := by
        simp only [Nxt, Prv,Inc]
        apply iUnion_increament
      have hdinc : Disjoint Prv Inc := by
        simp[Prv,Inc]
        apply iUnion_pred_disjoint_last hSd
      have hIncCard : Inc.card = m := by
        simp[Inc]
        have := hSc (Fin.last k)
        apply has_card_to_card this

      have hIncFin : Inc.finite := by
        simp[Inc]
        use m
        exact hSc (Fin.last k)
      split_ands
      . 
        rw[hinc]
        exact (card_union hPrvFin hIncFin).1
      rw[hinc]
      have prod := card_union_disjoint  hPrvFin hIncFin hdinc
      rw[prod,hPrvCar,hIncCard]
      ring

/- Finally, we'll set up a way to shrink `Fin (n + 1)` into `Fin n` (or expand the latter) by making a hole. -/

/--
  If some `x : Fin (n+1)` is never equal to `i`, we can shrink it into `Fin n` by shifting all `x > i` down by one.
  Compare to Mathlib `Fin.predAbove`.
-/
noncomputable def SetTheory.Set.Fin.predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : Fin n :=
  if hx : (x:ℕ) < i then
    Fin_mk _ (x:ℕ) (by have := Fin.toNat_lt i; omega)
  else
    Fin_mk _ ((x:ℕ) - 1) (by 
      push_neg at hx
      have : (x:ℕ )≠ (i :ℕ ) := by aesop
      have := Fin.toNat_lt x
      omega
    )

/--
  We can expand `x : Fin n` into `Fin (n + 1)` by shifting all `x ≥ i` up by one.
  The output is never `i`, so it forms an inverse to the shrinking done by `predAbove`.
  Compare to Mathlib `Fin.succAbove`.
-/
noncomputable def SetTheory.Set.Fin.succAbove {n} (i : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if (x:ℕ) < i then
    Fin_embed _ _ (by omega) x
  else
    Fin_mk _ ((x:ℕ) + 1) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.succAbove_ne {n} (i : Fin (n + 1)) (x : Fin n) : succAbove i x ≠ i := by
  unfold succAbove
  by_cases hx : (x:ℕ) < (i:ℕ)
  <;> simp[hx] <;> omega

@[simp]
theorem SetTheory.Set.Fin.succAbove_predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) :
    (succAbove i) (predAbove i x h) = x := by
    unfold succAbove predAbove
    by_cases hx : (x:ℕ) < (i:ℕ) <;> simp[hx]
    simp[Fin.coe_inj] at h
    have : ¬  (x:ℕ) - 1 < (i:ℕ) := by omega
    simp[this]; omega

@[simp]
theorem SetTheory.Set.Fin.predAbove_succAbove {n} (i : Fin (n + 1)) (x : Fin n) :
    (predAbove i) (succAbove i x) (succAbove_ne i x) = x := by
    set hne := succAbove_ne i x
    set s := succAbove i x with hs
    unfold predAbove at *
    by_cases hx : (s:ℕ) < (i:ℕ) <;> simp[hx]
    <;> unfold succAbove at *
    all_goals 
      by_cases hx' :(x:ℕ) < i <;> simp[hx'] at hs ⊢ 
      omega

/-- Exercise 3.6.12 (i), second part -/
noncomputable def SetTheory.Set.equiv_shink {n:ℕ} {i : Fin (n + 1)} (e: Fin (n+1) ≃ Fin (n+1)) (he : e (Fin.last n) = i) : Fin n ≃ Fin n := {
  toFun x := Fin.predAbove i (e (Fin.castSucc x)) (by
    by_contra hei
    rw[← he] at hei
    apply e.injective at hei
    simp at hei
  ) 
  invFun y := Fin.castPred (e.symm (Fin.succAbove i y)) (by
    by_contra eq
    have eq2 : e.symm (Fin.succAbove i y) = Fin.last n := by
      simpa
    rw[← eq2] at he
    simp at he
  )

  left_inv x := by simp
  right_inv y := by simp
}

open Classical in
noncomputable def SetTheory.Set.equiv_expand {n:ℕ} (i : Fin (n+1)) (e : Fin n ≃ Fin n) : Fin (n + 1) ≃ Fin (n + 1) :={
  toFun x := if hi : x = Fin.last n then i else Fin.succAbove i (e ( Fin.castPred x (by simp at hi; simp[hi] )))
  invFun y := if hi : y = i then Fin.last n else Fin.castSucc ( e.symm (Fin.predAbove i y (by simp[hi] ) ))
  left_inv x := by aesop
  right_inv y := by aesop
}
lemma SetTheory.Set.equiv_expand_pin {n: ℕ } (i : Fin (n+1)) (e: Fin n ≃ Fin n ) :
    equiv_expand i e (Fin.last n) = i := by
      simp[equiv_expand]
@[simp]
lemma  SetTheory.Set.equiv_expand_shink {n:ℕ} {i : Fin (n + 1)} (e: Fin (n+1) ≃ Fin (n+1)) (he : e (Fin.last n) = i) :
    equiv_expand i (equiv_shink e he) = e := by
      ext x
      by_cases hx : x = n
      <;> simp[hx, equiv_expand,equiv_shink]
      have : x = Fin.last n := by simpa
      simp only [← this] at he
      congr; symm ; assumption

@[simp]
lemma SetTheory.Set.equiv_shink_expand {n:ℕ} (i : Fin (n+1)) (e : Fin n ≃ Fin n) : 
    equiv_shink (equiv_expand i e) (equiv_expand_pin i e)  = e := by
      ext x
      simp[equiv_shink,equiv_expand]

theorem SetTheory.Set.Permutations_ih (n: ℕ):
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
      let S i := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i)
      have hSe : ∀ i, S i ≈ Permutations n := by
        intro i
        -- Hint: you might find `perm_equiv_equiv`, `Fin.succAbove`, and `Fin.predAbove` useful.
        have equiv : S i ≃ Permutations n := {
          toFun s := by
            obtain ⟨so, hs⟩ := s
            rw[specification_axiom''] at hs
            set hso := hs.choose
            set hsp := hs.choose_spec
            set equiv := perm_equiv_equiv ⟨so,hso⟩ 
            set equiv_s := equiv_shink equiv hsp
            exact perm_equiv_equiv.symm equiv_s
          invFun p := by
            set equiv_s := perm_equiv_equiv p
            have pinned :=  equiv_expand_pin i equiv_s
            set equiv := equiv_expand i equiv_s
            set s  := perm_equiv_equiv.symm equiv
            have : s.val ∈ S i := by
              rw[specification_axiom'']
              use s.property
              simp at pinned
              simpa [s]
            exact ⟨s.val, this⟩ 
          left_inv s := by simp
          right_inv p := by simp
        }
        use equiv, equiv.injective, equiv.surjective

      -- S i's are pairwise disjoint
      have hSdisj : Pairwise fun i j ↦ Disjoint (S i) (S j) := by
        intro i j hne
        rw[disjoint_iff,eq_empty_iff_forall_notMem]
        intro x; contrapose! hne with hint
        simp only [mem_inter, specification_axiom'', S] at hint
        obtain ⟨⟨hxp, hxi⟩ ,⟨_,hxj⟩ ⟩ := hint 
        rwa[hxi] at hxj

      -- (n+1)-perm is the Union of S i's 
      have hSiUnion : (Fin (n+1)).iUnion S = Permutations (n + 1) := by
        ext x
        simp only [mem_iUnion, Permutations,S,specification_axiom'']
        constructor
        . rintro ⟨i,⟨⟨hx,hbij⟩ ,hpin⟩ ⟩ 
          use hx
        rintro ⟨hx,hbij⟩ 
        use pow_fun_equiv ⟨x,hx⟩ (Fin.last n) , by use hx
        simp

      
      have hSCard : ∀ i , (S i).has_card ((Permutations n).card) := by
        intro i
        have pfin : (Permutations n).finite  := Permutations_finite n
        choose c pc using pfin
        have := (EquivCard_to_has_card_eq (hSe i)).mpr pc
        apply has_card_to_card at pc
        simp_all

      have hUCard := (card_iUnion_card_disjoint hSCard hSdisj).2
      rwa [hSiUnion] at hUCard

/-- Exercise 3.6.12 (ii) -/
theorem SetTheory.Set.Permutations_card (n: ℕ):
    (Permutations n).card = n.factorial := by
      induction' n with k hk
      . 
        let f : Fin 0 → Fin 0 := fun x ↦ by obtain ⟨x,hx⟩:=x; simp at hx 

        let p := (pow_fun_equiv.symm f)
        have : p.val ∈  Permutations 0 := by
          unfold Permutations
          rw[specification_axiom']
          rw[Function.bijective_iff_existsUnique]
          rintro ⟨b,hb⟩ 
          simp at hb
        set up : Permutations 0 := ⟨p,this⟩ 
        simp
        have : (Permutations 0).has_card 1 := by
          use fun x ↦ Fin.last 0
          rw[Function.bijective_iff_existsUnique]
          intro b
          have blt := Fin.toNat_lt b
          use up
          split_ands
          simp[Fin.last]
          omega
          intro y hy
          apply_fun perm_equiv_equiv
          ext x
          obtain ⟨x,hx⟩ := x
          simp at hx
        apply has_card_to_card this
      have := Permutations_ih k
      aesop

/-- Connections with Mathlib's `Finite` -/
theorem SetTheory.Set.finite_iff_finite {X:Set} : X.finite ↔ Finite X := by
  rw [finite_iff_exists_equiv_fin, finite]
  constructor
  · rintro ⟨n, hn⟩
    use n
    obtain ⟨f, hf⟩ := hn
    have eq := (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin n)
    exact ⟨eq⟩
  rintro ⟨n, hn⟩
  use n
  have eq := hn.some.trans (Fin.Fin_equiv_Fin n).symm
  exact ⟨eq, eq.bijective⟩

/-- Connections with Mathlib's `Set.Finite` -/
theorem SetTheory.Set.finite_iff_set_finite {X:Set} :
    X.finite ↔ (X :_root_.Set Object).Finite := by
  rw [finite_iff_finite]
  rfl

/-- Connections with Mathlib's `Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by
  by_cases hf : X.finite
  · by_cases hz : X.card = 0
    · rw [hz]; symm
      have : X = ∅ := empty_of_card_eq_zero hf hz
      rw [this, Nat.card_eq_zero, isEmpty_iff]
      aesop
    symm
    have hc := has_card_card hf
    obtain ⟨f, hf⟩ := hc
    apply Nat.card_eq_of_equiv_fin
    exact (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin X.card)
  simp only [card, hf, ↓reduceDIte]; symm
  rw [Nat.card_eq_zero, ←not_finite_iff_infinite]
  right
  rwa [finite_iff_set_finite] at hf

/-- Connections with Mathlib's `Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by
  rw [card_eq_nat_card]
  rfl

end Chapter3
