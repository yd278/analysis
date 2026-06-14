import Mathlib.Tactic
import Analysis.Section_4_4

/-!
# Analysis I, Section 8.1: Countability

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Custom notions for "equal cardinality", "countable", and "at most countable".  Note that Mathlib's
{name}`Countable` typeclass corresponds to what we call "at most countable" in this text.
- Countability of the integers and rationals.

Note that as the Chapter 3 set theory has been deprecated, we will not re-use relevant constructions from that theory here, replacing them with Mathlib counterparts instead.

-/

namespace Chapter8

/-- The definition of equal cardinality. For simplicity we restrict attention to the Type 0 universe.
This is analogous to `Chapter3.SetTheory.Set.EqualCard`, but we are not using the latter since
the Chapter 3 set theory is deprecated. -/
abbrev EqualCard (X Y : Type) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Relation with Mathlib's {name}`Equiv` concept -/
theorem EqualCard.iff {X Y : Type} : EqualCard X Y ↔ Nonempty (X ≃ Y) := by
  simp [EqualCard]; constructor
  . intro ⟨ f, hf ⟩; exact ⟨ .ofBijective f hf ⟩
  intro ⟨ e ⟩; exact ⟨ e.toFun, e.bijective ⟩

/-- Equivalence with Mathlib's {name}`Cardinal.mk` concept -/
theorem EqualCard.iff' {X Y : Type} : EqualCard X Y ↔ Cardinal.mk X = Cardinal.mk Y := by
  simp [Cardinal.eq, iff]

theorem EqualCard.refl (X : Type) : EqualCard X X := by
  rw[iff']


theorem EqualCard.symm {X Y : Type} (hXY : EqualCard X Y) : EqualCard Y X := by
  rw[iff'] at ⊢ hXY
  grind

theorem EqualCard.trans {X Y Z : Type} (hXY : EqualCard X Y) (hYZ : EqualCard Y Z) :
  EqualCard X Z := by
    rw[iff'] at  hXY hYZ ⊢ 
    grind

instance EqualCard.instSetoid : Setoid Type := ⟨ EqualCard, ⟨ refl, symm, trans ⟩ ⟩

theorem EqualCard.univ (X : Type) : EqualCard (.univ : Set X) X :=
  ⟨ Subtype.val, Subtype.val_injective, by intro _; aesop ⟩

abbrev CountablyInfinite (X : Type) : Prop := EqualCard X ℕ

abbrev AtMostCountable (X : Type) : Prop := CountablyInfinite X ∨ Finite X

theorem CountablyInfinite.equiv {X Y: Type} (hXY : EqualCard X Y) :
  CountablyInfinite X ↔ CountablyInfinite Y := ⟨ hXY.symm.trans, hXY.trans ⟩

theorem Finite.equiv {X Y: Type} (hXY : EqualCard X Y) :
  Finite X ↔ Finite Y := by obtain ⟨ f, hf ⟩ := hXY; exact (Equiv.ofBijective f hf).finite_iff

theorem AtMostCountable.equiv {X Y: Type} (hXY : EqualCard X Y) :
  AtMostCountable X ↔ AtMostCountable Y := by
  simp [AtMostCountable, CountablyInfinite.equiv hXY, Finite.equiv hXY]

/-- Equivalence with Mathlib's {name}`Denumerable` concept (cf. Remark 8.1.2) -/
theorem CountablyInfinite.iff (X : Type) : CountablyInfinite X ↔ Nonempty (Denumerable X) := by
  simp [CountablyInfinite, EqualCard.iff]; constructor
  . intro ⟨ e ⟩; exact ⟨ Denumerable.mk' e ⟩
  intro ⟨ h ⟩; exact ⟨ h.eqv X ⟩

/-- Equivalence with Mathlib's {name}`Countable` typeclass -/
theorem CountablyInfinite.iff' (X : Type) : CountablyInfinite X ↔ Countable X ∧ Infinite X := by
  rw [iff, nonempty_denumerable_iff]

theorem CountablyInfinite.toCountable {X : Type} (hX: CountablyInfinite X) : Countable X := by
  simp_all [iff']

theorem CountablyInfinite.toInfinite {X : Type} (hX: CountablyInfinite X) : Infinite X := by
  simp_all [iff']

theorem AtMostCountable.iff (X : Type) : AtMostCountable X ↔ Countable X := by
  observe h1 : CountablyInfinite X ↔ Countable X ∧ Infinite X
  observe h2 : Finite X ∨ Infinite X
  observe h3 : Finite X → Countable X
  tauto
theorem CountablyInfinite.iff_image_inj {A:Type} (X: Set A) : CountablyInfinite X ↔ ∃ f : ℕ ↪ A, X = f '' .univ := by
  constructor
  . intro ⟨ g, hg ⟩
    choose f hleft hright using Function.bijective_iff_has_inverse.mp hg
    refine ⟨ ⟨ Subtype.val ∘ f, ?_ ⟩, ?_ ⟩
    . intro x y hxy; apply hright.injective; simp_all [Subtype.val_inj]
    ext; simp; constructor
    . intro hx; use g ⟨ _, hx ⟩; simp [hleft _]
    rintro ⟨ _, rfl ⟩; aesop
  intro ⟨ f, hf ⟩
  have := Function.leftInverse_invFun (Function.Embedding.injective f)
  use (Function.invFun f) ∘ Subtype.val; split_ands
  . rintro ⟨ x, hx ⟩ ⟨ y, hy ⟩ h; grind
  intro n; use ⟨ f n, by aesop ⟩; grind

/-- Examples 8.1.3 -/
example : CountablyInfinite ℕ := by use fun n ↦ n; exact Function.Involutive.bijective (congrFun rfl)


example : CountablyInfinite (.univ \ {0}: Set ℕ) := by
  apply EqualCard.symm
  use fun n ↦ ⟨n+1, by simp⟩ 
  constructor
  . intro n m; simp
  rintro ⟨y,hy⟩ 
  simp at hy;simp;grind

example : CountablyInfinite ((fun n:ℕ ↦ 2*n) '' .univ) := by
  apply EqualCard.symm
  use fun n ↦ ⟨2*n, by simp⟩ 
  constructor
  . intro n m; simp
  rintro ⟨y,hy⟩;simp at hy 
  choose x hx using hy.exists_two_nsmul
  simp at hx;use x;simp[hx]

/-- Proposition 8.1.4 (Well ordering principle / Exercise 8.1.2 -/
theorem Nat.exists_unique_min {X : Set ℕ} (hX : X.Nonempty) :
  ∃! m ∈ X, ∀ n ∈ X, m ≤ n := by
    apply existsUnique_of_exists_of_unique
    . by_contra! hcon
      choose x hx using hX
      set next : X → X := fun (n:X) ↦ ⟨ (hcon n (by grind)).choose , by grind⟩ 
      have hnext (n:X) : (next n:ℕ) < n := by
        have := (hcon n (by grind)).choose_spec.2
        unfold next;simp[this];
      set a' : ℕ → X := fun n ↦ Nat.rec ⟨x,hx⟩  (fun n pr ↦ next pr  ) n
      set a : ℕ → ℕ := fun n ↦ (a' n).val
      apply Nat.no_infinite_descent
      use a; intro n
      unfold a;
      have : a' (n+1) = next (a' n) := by
        exact SetCoe.ext rfl
      rw[this];simp[hnext]
    rintro y1 y2 ⟨hy1,hy1m⟩ ⟨hy2,hy2m⟩  
    by_contra! hne
    obtain hgt|hlt := gt_or_lt_of_ne hne
    . specialize hy1m y2 hy2; linarith
    specialize hy2m y1 hy1; linarith
def Int.exists_unique_min : Decidable (∀ (X : Set ℤ) (hX : X.Nonempty), ∃! m ∈ X, ∀ n ∈ X, m ≤ n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse
  simp;use .univ ;simp
  by_contra hcon
  choose m hmmin hmuniq using hcon
  specialize hmmin (m-1)
  linarith

def NNRat.exists_unique_min : Decidable (∀ (X : Set NNRat) (hX : X.Nonempty), ∃! m ∈ X, ∀ n ∈ X, m ≤ n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse
  simp;use .univ \ {0} 
  split_ands
  . use 1;simp
  by_contra hcon
  obtain ⟨m,⟨hmpos,hmmin⟩ ,hmuniq⟩  := hcon
  simp at hmpos
  specialize hmmin (m/2) (by simpa)
  field_simp at hmmin;simp at hmmin

open Classical in
noncomputable abbrev Nat.min (X : Set ℕ) : ℕ := if hX : X.Nonempty then (exists_unique_min hX).exists.choose else 0

theorem Nat.min_spec {X : Set ℕ} (hX : X.Nonempty) : min X ∈ X ∧ ∀ n ∈ X, min X ≤ n := by
  simp [hX, min]; exact (exists_unique_min hX).exists.choose_spec

theorem Nat.min_eq {X : Set ℕ} (hX : X.Nonempty) {a:ℕ} (ha : a ∈ X ∧ ∀ n ∈ X, a ≤ n) : min X = a :=
  (exists_unique_min hX).unique (min_spec hX) ha

@[simp]
theorem Nat.min_empty : min ∅ = 0 := by simp [Nat.min]

example : Nat.min ((fun n ↦ 2*n) '' (.Ici 1)) = 2 := by
  apply Nat.min_eq
  . use 2;simp
  simp


theorem Nat.min_eq_sInf {X : Set ℕ} (hX : X.Nonempty) : min X = sInf X := by
  apply min_eq hX
  constructor
  . apply Nat.sInf_mem hX
  intro n hn 
  apply Nat.sInf_le hn

open Classical in
/-- Equivalence with Mathlib's {name}`Nat.find` method -/
theorem Nat.min_eq_find {X : Set ℕ} (hX : X.Nonempty) : min X = Nat.find hX := by
  symm; rw [Nat.find_eq_iff]; have := min_spec hX; grind
lemma Nat.min_subset {X Y: Set ℕ} (hX : X.Nonempty)(hY : Y.Nonempty) (hXY : X ⊆ Y) : min Y ≤ min X := by
  have ⟨hmX, hmnX⟩ := min_spec hX
  obtain ⟨hmY,hmnY⟩  := min_spec hY
  apply hXY at hmX
  apply hmnY _ hmX
/-- Proposition 8.1.5 -/

theorem Nat.monotone_enum_of_infinite (X : Set ℕ) [Infinite X] : ∃! f : ℕ → X, Function.Bijective f ∧ StrictMono f := by
  -- This proof is written to follow the structure of the original text.
  let a : ℕ → ℕ := Nat.strongRec (fun n a ↦ min { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m h })
  have ha : ∀ n, a n = min { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := Nat.strongRec.eq_def _
  have ha_infinite (n:ℕ) : Infinite { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := by
    have hunion : X = { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } ∪ {x ∈ X | ∃ (m:ℕ) (h: m < n), x = a m} := by
      ext x ;simp
      constructor
      . intro hx
        rw[or_iff_not_imp_left]
        intro hm; simp[hx] at hm
        simp[hx,hm]
      tauto
    by_contra! hfin 
    have hsfin : Finite {x ∈ X | ∃ (m:ℕ) (h: m < n), x = a m}  := by
      have : {x ∈ X | ∃ (m:ℕ) (h: m < n), x = a m} ⊆ a '' Finset.Iio n  := by
        intro x hx
        simp at hx
        simp;tauto
      apply Set.Finite.subset _ this
      apply Finite.Set.finite_image
    have hcon : ¬ Infinite X := by
      simp; rw[hunion]
      apply Finite.Set.finite_union
    contradiction
  have ha_nonempty (n:ℕ) : { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m }.Nonempty := Set.Nonempty.of_subtype
  have ha_mono : StrictMono a := by
    intro x1 x2 hlt
    apply lt_of_le_of_ne'
    .
      rw[ha,ha]
      apply min_subset (ha_nonempty x2) (ha_nonempty x1)
      simp;intro x hx hmx2
      simp[hx];intro m hm
      apply hmx2 m (by omega)
    have ⟨hmx1,hmnx1⟩ := min_spec (ha_nonempty x1) 
    have ⟨hmx2,hmnx2⟩ := min_spec (ha_nonempty x2) 
    rw[← ha] at hmx1 hmnx1 hmx2 hmnx2
    by_contra heq
    rw[heq] at hmx2
    simp at hmx2
    obtain ⟨_,hocn⟩ := hmx2 
    specialize hocn x1 hlt
    simp at hocn
  have ha_injective : Function.Injective a := by
    exact ha_mono.injective
  have haX (n:ℕ) : a n ∈ X := by
    rw[ha]
    have : {x | x ∈ X ∧ ∀ m < n, x ≠ a m} ⊆ X := by simp
    apply this
    apply (min_spec (ha_nonempty n)).1
  set f : ℕ → X := fun n ↦ ⟨ a n, haX n ⟩
  have hf_injective : Function.Injective f := by
    intro x y hxy; simp [f] at hxy; solve_by_elim
  have hf_surjective : Function.Surjective f := by
    intro ⟨ x, hx ⟩; simp [f]; by_contra
    have h1 (n:ℕ) : x ∈ { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := by
      simp;tauto
    have h2 (n:ℕ) : x ≥ a n := by
      rw [ha n]; exact ge_iff_le.mpr ((min_spec (ha_nonempty n)).2 _ (h1 n))
    have h3 (n:ℕ) : a n ≥ n := by
      apply ha_mono.le_apply
    have h4 (n:ℕ) : x ≥ n := (h3 n).trans (h2 n)
    linarith [h4 (x+1)]
  apply ExistsUnique.intro _ ⟨ ⟨ hf_injective, hf_surjective ⟩, ha_mono ⟩
  intro g ⟨ hg_bijective, hg_mono ⟩; by_contra!
  replace : { n | g n ≠ f n }.Nonempty := by
    contrapose! this
    apply funext; simpa [Set.eq_empty_iff_forall_notMem] using this
  set m := min { n | g n ≠ f n }
  have hm : g m ≠ f m := (min_spec this).1
  have hm' {n:ℕ} (hn: n < m) : g n = f n := by by_contra hgfn; linarith [(min_spec this).2 n (by simp [hgfn])]
  have hgm : g m = min { x ∈ X | ∀ (n:ℕ) (h:n < m), x ≠ a n } := by
    symm;apply min_eq
    . use a m; simp[haX];intro n hn; rw[← ha_mono.lt_iff_lt] at hn;omega
    simp;split_ands
    . peel hm' with n hn hne 
      have : g n = a n := by simp[f] at hne; grind
      rw[← this]; push_neg;rw[Subtype.coe_ne_coe]
      have := hg_mono hn;grind
    intro x hx hnm
    have : ∀ n < m , x ≠ g n := by
      intro n hn
      specialize hnm n hn
      specialize hm' hn 
      have : g n = a n := by simp[f] at hm'; grind
      grind
    choose l hl using hg_bijective.surjective ⟨x, hx⟩ 
    have hlm : m ≤ l := by
      by_contra! hlt
      specialize this _ hlt
      simp[hl] at this
    rw[← hg_mono.le_iff_le] at hlm
    rw[hl] at hlm
    simpa
  rw [←ha m] at hgm; contrapose! hm; exact Subtype.val_injective hgm

theorem Nat.countable_of_infinite (X : Set ℕ) [Infinite X] : CountablyInfinite X := by
  have := (monotone_enum_of_infinite X).exists
  exact EqualCard.symm ⟨ this.choose, this.choose_spec.1 ⟩

/-- Corollary 8.1.6 -/
theorem Nat.atMostCountable_subset (X: Set ℕ) : AtMostCountable X := by
  obtain _ | _ := finite_or_infinite X
  . tauto
  simp [AtMostCountable, countable_of_infinite]

/-- Corollary 8.1.7 -/
theorem AtMostCountable.subset {X: Type} (hX : AtMostCountable X) (Y: Set X) : AtMostCountable Y := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ f, hf ⟩ | hX := hX
  . let f' : Y → f '' Y := fun y ↦ ⟨ f y, by aesop ⟩
    have hf' : Function.Bijective f' := by
      constructor
      . rintro ⟨y1, hy1⟩ ⟨y2,hy2⟩ heq  
        simp[f'] at heq
        simp;apply hf.injective heq 
      intro z 
      choose x hx using hf.surjective z
      have := z.property
      rw[← hx] at this; simp at this;
      choose x' hx'Y hxx' using this
      simp[f'];use x', hx'Y
      simp[hxx',hx]
    rw [equiv ⟨ _, hf' ⟩ ]; apply Nat.atMostCountable_subset
  simp [AtMostCountable, show Finite Y by infer_instance]

theorem AtMostCountable.subset' {A: Type} {X Y: Set A} (hX: AtMostCountable X) (hY: Y ⊆ X) : AtMostCountable Y := by
  refine' (equiv ⟨ fun y ↦ ⟨ ↑↑y, y.property ⟩, _, _ ⟩).mp (subset hX { x : X | ↑x ∈ Y })
  . intro ⟨ ⟨ _, _ ⟩, _ ⟩ ⟨ ⟨ _, _ ⟩, _ ⟩ _; simp_all
  intro ⟨ y, hy ⟩; use ⟨ ⟨ y, hY hy ⟩, by aesop ⟩

/-- Proposition 8.1.8 / Exercise 8.1.4 -/
theorem AtMostCountable.image_nat (Y: Type) (f: ℕ → Y) : AtMostCountable (f '' .univ) := by

  simp
  set g : (Set.range f) → ℕ := fun y ↦  Nat.min {x | f x = y }
  have hg (y:Set.range f) : g y ∈ {x | f x = y} := by
    choose x hx using y.property
    simp[g]
    set S :=  {x | f x = y}
    have hS : S.Nonempty := by use x; simp[S,hx]
    have ⟨hspec,_⟩  := Nat.min_spec hS
    simp [S] at hspec ⊢ 
    assumption
  rw[iff]
  use g
  intro y1 y2 heq
  contrapose! heq with hne
  have disj: Disjoint {x | f x = y1} {x | f x = y2} := by
    simp[disjoint_iff]
    ext x;simp
    intro hfx
    rw[hfx];grind
  have hg1 := hg y1
  have hg2 := hg y2
  grind

/-- Corollary 8.1.9 / Exercise 8.1.5 -/
theorem AtMostCountable.image {X:Type} (hX: CountablyInfinite X) {Y: Type} (f: X → Y) : AtMostCountable (f '' .univ) := by
  choose g hg using hX.symm
  set f' := f ∘ g
  have : f '' .univ = f' '' .univ := by
    ext y; simp
    refine Function.Surjective.exists hg.surjective
  rw[this]
  apply AtMostCountable.image_nat


/-- Proposition 8.1.10 / Exercise 8.1.7 -/
theorem CountablyInfinite.union {A:Type} {X Y: Set A} (hX: CountablyInfinite X) (hY: CountablyInfinite Y) :
  CountablyInfinite (X ∪ Y: Set A) := by
    choose fx hfx using hX.symm
    choose fy hfy using hY.symm
    set g : ℕ → (X ∪ Y : Set A)  :=  fun n ↦ if Even n then ⟨ fx (n / 2), by grind ⟩ else ⟨ fy (n/2), by grind ⟩ 
    have hg : g.Surjective := by
      rintro ⟨a,ha⟩ 
      obtain (haX | haY) := ha
      . use ((fx.invFun ⟨a,haX⟩) * 2)
        simp[g]
        rw[Function.rightInverse_invFun hfx.surjective]
      set n := ((fy.invFun ⟨a,haY⟩) * 2 + 1)
      have hn : ¬ Even n := by simp[n]
      use n
      simp[g,hn,n]
      have (n:ℕ) : (n * 2 + 1) / 2 = n := by omega
      simp[this]
      rw[Function.rightInverse_invFun hfy.surjective]
    have hXi := hX.toInfinite
    suffices hunion : Countable (X ∪ Y :Set A) from by
      rw[← AtMostCountable.iff ] at hunion
      unfold AtMostCountable  at hunion
      obtain (h1| hunion ) := hunion 
      . exact h1
      contrapose! hunion
      rw[Set.infinite_coe_iff, Set.infinite_union, ← Set.infinite_coe_iff]
      left; apply hX.toInfinite
    have hune : Nonempty (X ∪ Y:Set A) := by
      rw[Set.nonempty_coe_sort];simp;left; exact Set.Nonempty.of_subtype
    rw[countable_iff_exists_surjective]
    use g

/-- Corollary 8.1.11 --/
theorem Int.countablyInfinite : CountablyInfinite ℤ := by
  -- This proof is written to follow the structure of the original text.
  have h1 : CountablyInfinite {n:ℤ | n ≥ 0} := by
    rw [CountablyInfinite.iff_image_inj]
    use ⟨ (↑·:ℕ → ℤ), by intro _ _ _; simp_all ⟩
    ext n; simp; refine ⟨ ?_, by aesop ⟩
    . intro h; use n.toNat; simp [h]
  have h2 : CountablyInfinite {n:ℤ | n ≤ 0} := by
    rw [CountablyInfinite.iff_image_inj]
    use ⟨ (-↑·:ℕ → ℤ), by intro _ _ _; simp_all ⟩
    ext n; simp; refine ⟨ ?_, by aesop ⟩
    intro h; use (-n).toNat; simp [h]
  have : CountablyInfinite (.univ : Set ℤ) := by
    convert h1.union h2; ext; simp; omega
  rwa [←CountablyInfinite.equiv (.univ _)]

/-- Lemma 8.1.12 -/
theorem CountablyInfinite.lower_diag : CountablyInfinite { n : ℕ × ℕ | n.2 ≤ n.1 } := by
  -- This proof is written to follow the structure of the original text.
  let A := { n : ℕ × ℕ | n.2 ≤ n.1 }
  let a : ℕ → ℕ := fun n ↦ ∑ m ∈ .range (n+1), m
  have ha : StrictMono a := by
    apply strictMono_of_lt_succ
    intro n hn
    simp[a]
    nth_rw 2 [Finset.sum_range_succ]
    simp
  let f : A → ℕ := fun ⟨ (n, m), _ ⟩ ↦ a n + m
  have hf : Function.Injective f := by
    rintro ⟨ ⟨ n, m ⟩, hnm ⟩ ⟨ ⟨ n',m'⟩, hnm' ⟩ h
    simp [A,f] at hnm hnm' ⊢ h
    obtain hnn' | rfl | hnn' := lt_trichotomy n n'
    . have : a n' + m' > a n + m := by calc
        _ ≥ a n' := by linarith
        _ ≥ a (n+1) := ha.monotone (by linarith)
        _ = a n + (n + 1) := Finset.sum_range_succ id _
        _ > a n + m := by linarith
      linarith
    . simpa using h
    have : a n + m > a n' + m' := by calc
        _ ≥ a n := by linarith
        _ ≥ a (n'+1) := ha.monotone (by linarith)
        _ = a n' + (n' + 1) := Finset.sum_range_succ id _
        _ > a n' + m' := by linarith
    linarith
  let f' : A → f '' .univ := fun p ↦ ⟨ f p, by aesop ⟩
  have hf' : Function.Bijective f' := by
    constructor
    . intro p q hpq; simp [f'] at hpq; solve_by_elim
    intro ⟨ l, hl ⟩; simp at hl
    obtain ⟨ n, m, q, rfl ⟩ := hl; use ⟨ (n, m), q ⟩
  have : AtMostCountable A := by rw [AtMostCountable.equiv ⟨ _, hf' ⟩]; apply Nat.atMostCountable_subset
  have hfi : ¬ Finite A := by
    simp;rw[Set.infinite_coe_iff]
    set fi : ℕ → (ℕ × ℕ) := fun n ↦ (n,n)
    have hfi : fi.Injective := by
      intro x1 x2 feq
      simpa[fi] using feq
    apply Set.infinite_of_injective_forall_mem hfi
    intro x;simp[fi,A]
  simp [AtMostCountable] at this; tauto

/-- Corollary 8.1.13 -/
theorem CountablyInfinite.prod_nat : CountablyInfinite (ℕ × ℕ) := by
  have upper_diag : CountablyInfinite { n : ℕ × ℕ | n.1 ≤ n.2 } := by
    refine (equiv ⟨ fun ⟨ (n, m), _ ⟩ ↦ ⟨ (m, n), by aesop ⟩, ?_, ?_ ⟩).mp lower_diag
    . intro ⟨ (_, _), _ ⟩ ⟨ (_, _), _ ⟩ _; aesop
    intro ⟨ (n, m), _ ⟩; use ⟨ (m, n), by aesop ⟩
  have : CountablyInfinite (.univ : Set (ℕ × ℕ)) := by
    convert union lower_diag upper_diag; ext ⟨ n, m ⟩; simp; omega
  exact (equiv (.univ _)).mp this

/-- Corollary 8.1.14 / Exercise 8.1.8 -/
theorem CountablyInfinite.prod {X Y:Type} (hX: CountablyInfinite X) (hY: CountablyInfinite Y) :
  CountablyInfinite (X × Y) := by
    choose fx hfx using hX.symm
    choose fy hfy using hY.symm
    set g : (ℕ × ℕ) → (X × Y) := fun n ↦ (fx n.1, fy n.2)
    have hg : g.Bijective := by
      constructor
      . intro s1 s2 heq
        simp[g] at heq
        choose heq1 heq2 using heq
        ext
        apply hfx.injective heq1
        apply hfy.injective heq2
      intro p
      choose a1 ha1 using hfx.surjective p.1
      choose a2 ha2 using hfy.surjective p.2
      use (a1, a2)
      simp[g,ha1,ha2]
    have hequiv : EqualCard  (ℕ × ℕ)  (X × Y) := by use g
    rw[← CountablyInfinite.equiv hequiv]
    exact prod_nat


/-- Corollary 8.1.15 -/
theorem Rat.countablyInfinite : CountablyInfinite ℚ := by
  -- This proof is written to follow the structure of the original text.
  have : CountablyInfinite { n:ℤ | n ≠ 0 } := by
    suffices hequiv : EqualCard { n:ℤ | n ≠ 0 } ℤ from by
      rw[CountablyInfinite.equiv hequiv]
      exact Int.countablyInfinite
    unfold EqualCard
    set f : {n:ℤ|n≠ 0} → ℤ := fun n ↦ if hn : (n:ℤ) > 0 then n - 1 else n;use f
    constructor
    . intro n1 n2 heq
      simp[f] at heq
      split_ifs at heq with hn1 hn2 <;> grind
    intro z
    obtain hp| hn := le_or_gt 0 z
    . use  ⟨z+1, by simp;omega⟩; simp[f,hp] 
    use ⟨z, by simp;omega⟩ 
    simp[f];omega
  apply Int.countablyInfinite.prod at this
  let f : ℤ × { n:ℤ | n ≠ 0 } → ℚ := fun (a,b) ↦ (a/b:ℚ)
  replace := AtMostCountable.image this f
  have h : f '' .univ = .univ := by
    simp;rw[Set.range_eq_univ]
    intro x
    have hdef := x.num_div_den
    have hnz := x.den_ne_zero
    use (x.num, ⟨x.den,by grind⟩) 
    simp[f,hdef]
  rcases this with h1 | h2
  · have h1' : CountablyInfinite (Set.univ : Set ℚ) := h ▸ h1
    rwa [CountablyInfinite.equiv (EqualCard.univ _)] at h1'
  · have h2' : Finite (Set.univ : Set ℚ) := h ▸ h2
    rw [Set.finite_coe_iff, Set.finite_univ_iff] at h2'
    exact absurd h2' (not_finite_iff_infinite.mpr inferInstance)

open Classical in
/-- Exercise 8.1.1 -/
example (X: Type) : Infinite X ↔ ∃ Y : Set X, Y ≠ .univ ∧ EqualCard Y X := by
  rw[← Set.infinite_univ_iff]
  set U := Set.univ
  have heq : EqualCard X U := by
    use (Equiv.Set.univ X).symm
    exact Equiv.bijective (Equiv.Set.univ X).symm
  replace heq  (Y:Set X): EqualCard Y X ↔ EqualCard Y U := by
    constructor <;> intro h
    . apply h.trans heq
    apply h.trans heq.symm
  simp[heq]
  
  constructor
  . intro hfin
    set f := hfin.natEmbedding 
    use (U \ {(f 0:X)});simp
    apply EqualCard.symm
    use fun x ↦ if h: ∃ n, f n = x then ⟨ f (h.choose +1) , by grind ⟩  else ⟨ x, by grind ⟩ 
    constructor
    . intro x1 x2 heq
      simp at heq
      split_ifs at heq with hn1 hn2 <;> simp at heq <;>  grind
    . rintro ⟨x,hx⟩; simp at hx 
      by_cases hexist : ∃ n, f n = x
      .
        set hn := hexist.choose_spec
        set n := hexist.choose
        have hn0 : n ≠ 0 := by grind
        use f (n-1)
        simp;grind
      use ⟨x,hx.1⟩
      simp;split_ifs with hcoe
      . contrapose! hexist; peel hcoe with n hcoe ; grind
      grind
  rintro ⟨Y,hssub, ⟨f,hf⟩  ⟩ 
  have hYU : Y ⊂ U := by grind
  by_contra! hfin
  have hncard : Y.ncard = U.ncard := by
    have hY : Y.Finite := hfin.of_injective f hf.1
    have hY' : Fintype Y := by exact hY.fintype
    have hU' := hfin.fintype 
    rw [Set.ncard_eq_toFinset_card Y hY, Set.ncard_eq_toFinset_card U hfin]
    simpa using Fintype.card_congr (Equiv.ofBijective f hf)
  rw[← Set.finite_coe_iff] at hfin
  have := Set.ncard_lt_ncard  hYU
  linarith

/-- Exercise 8.1.6 -/
example (A: Type) : AtMostCountable A ↔ ∃ f : A → ℕ, Function.Injective f := by
  --eeto... 
  constructor
  . rintro (hinf|hfin)
    . choose f hf using hinf
      use f; apply hf.1
    obtain ⟨ n, hn⟩   := hfin.exists_equiv_fin
    set f := hn.some
    use fun a ↦ f a
    intro a1 a2 heq
    simpa[Fin.val_eq_val] using heq
  rintro ⟨f,hf⟩ 
  by_cases hae : ¬ Nonempty A
  . right; simp at hae;exact Finite.of_subsingleton
  simp at hae
  rw[AtMostCountable.iff]
  rw[countable_iff_exists_surjective]
  use f.invFun
  exact Function.invFun_surjective hf

/-- Exercise 8.1.9 -/
example {I X:Type} (hI: AtMostCountable I) (A: I → Set X) (hA: ∀ i, AtMostCountable (A i)) :
  AtMostCountable (⋃ i, A i) := by
    simp_rw[AtMostCountable.iff] at hI hA ⊢ 
    simp_rw[Set.countable_coe_iff] at hA ⊢ 
    rwa[Set.countable_iUnion_iff]
def Calkin_Wilf (n:ℕ) : ℚ := 
  if n = 0 then 0
  else if n = 1 then 1
  else if Even n then let q := Calkin_Wilf (n/2); q/(q+1)
  else let q:= Calkin_Wilf (n/2); q+1
  termination_by n
  decreasing_by grind;grind

lemma Calkin_Wilf.pos {n:ℕ} (hn: n≠0) : 0 < Calkin_Wilf n := by
  fun_induction Calkin_Wilf n with
  | case1 => simp at hn
  | case2 => simp
  | case3 n hn0 hn1 heven q hq =>  specialize hq (by omega); rw[div_pos_iff_of_pos_left] <;> linarith
  | case4 n hn0 hn1 hodd q hq => specialize hq (by omega);linarith

lemma Calkin_Wilf.zero {n:ℕ} : n = 0 ↔ Calkin_Wilf n = 0 := by
  constructor; intro hn; simp[Calkin_Wilf,hn]
  contrapose!;intro hn;  apply ne_of_gt; apply pos hn

abbrev Calkin_Wilf.complexity (q:ℚ)  : ℕ := q.num.toNat + q.den


lemma div_one_sub_eq_num_div_den_sub_num (q : ℚ) (hq1 : q < 1) :
    q / (1 - q) = (q.num : ℚ) / ((q.den : ℤ) - q.num) := by
  have hnum_lt_den : q.num < (q.den : ℤ) := Rat.num_lt_denom_iff.mpr hq1
  have hden_sub_pos : 0 < (q.den : ℤ) - q.num := sub_pos.mpr hnum_lt_den
  calc
    q / (1 - q) =
        ((q.num : ℚ) / q.den) / (1 - (q.num : ℚ) / q.den) := by
      rw [q.num_div_den]
    _ = (q.num : ℚ) / ((q.den : ℤ) - q.num) := by
      field_simp [show ((q.den : ℚ) : ℚ) ≠ 0 by exact_mod_cast q.den_ne_zero,
        show (((q.den : ℤ) - q.num : ℚ) : ℚ) ≠ 0 by exact_mod_cast hden_sub_pos.ne']
      congr 1

lemma coprime_num_den_sub_num (q : ℚ) (hq0 : 0 < q) (hq1 : q < 1) :
    Nat.Coprime q.num.natAbs (((q.den : ℤ) - q.num).natAbs) := by
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq0
  have hnum_lt_den : q.num < (q.den : ℤ) := Rat.num_lt_denom_iff.mpr hq1
  have hnum_natCast : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg hnum_pos.le
  have hle : q.num.natAbs ≤ q.den := by
    have : (q.num.natAbs : ℤ) ≤ (q.den : ℤ) := by
      rw [hnum_natCast]
      exact hnum_lt_den.le
    exact_mod_cast this
  have hsub :
      ((q.den : ℤ) - q.num).natAbs = q.den - q.num.natAbs := by
    rw [← hnum_natCast]
    omega
  rw [hsub]
  exact (Nat.coprime_sub_self_right hle).mpr q.reduced

theorem num_eq_num_div_one_sub (q : ℚ) (hq0 : 0 < q) (hq1 : q < 1) :
    (q / (1 - q)).num = q.num := by
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq0
  have hnum_lt_den : q.num < (q.den : ℤ) := Rat.num_lt_denom_iff.mpr hq1
  have hden_sub_pos : 0 < (q.den : ℤ) - q.num := sub_pos.mpr hnum_lt_den
  rw [div_one_sub_eq_num_div_den_sub_num q hq1]
  have hcop := coprime_num_den_sub_num q hq0 hq1
  simpa [sub_eq_add_neg, add_comm] using Rat.num_div_eq_of_coprime hden_sub_pos hcop

theorem den_eq_den_sub_num_div_one_sub (q : ℚ) (hq0 : 0 < q) (hq1 : q < 1) :
    ((q / (1 - q)).den : ℤ) = (q.den : ℤ) - q.num := by
  have hnum_lt_den : q.num < (q.den : ℤ) := Rat.num_lt_denom_iff.mpr hq1
  have hden_sub_pos : 0 < (q.den : ℤ) - q.num := sub_pos.mpr hnum_lt_den
  rw [div_one_sub_eq_num_div_den_sub_num q hq1]
  have hcop := coprime_num_den_sub_num q hq0 hq1
  simpa [sub_eq_add_neg, add_comm] using Rat.den_div_eq_of_coprime hden_sub_pos hcop

def Calkin_Wilf_inv (q:ℚ) : ℕ :=
  if hqp: q ≤ 0 then 0 --dummy
  else if hq1 : q = 1 then 1
  else if hqlt : q < 1 then Calkin_Wilf_inv (q/(1-q)) * 2
  else Calkin_Wilf_inv (q-1) * 2 + 1
  termination_by Calkin_Wilf.complexity q
  decreasing_by
  . simp at hqp
    simp[Calkin_Wilf.complexity]
    rw[num_eq_num_div_one_sub q hqp hqlt]
    zify
    rw[den_eq_den_sub_num_div_one_sub q hqp hqlt]
    simp[hqp]
  . 
    simp at hqp hqlt hq1
    simp[Calkin_Wilf.complexity,hqp]
    have hqgt : ¬ q ≤ 1 := by grind
    have hqd : q.den < q.num := by
      simpa [← Rat.num_le_denom_iff] using hqgt
    rcases q with ⟨n, d, hd, hcop⟩
    simp[Rat.sub_def] at hqd ⊢
    have hg_nat : 0 < (n - d).natAbs.gcd d := by
      apply Nat.gcd_pos_of_pos_left
      omega
    zify at hg_nat
    have hle : (n-d)/((n-d).natAbs.gcd d :ℤ ) ≤ n - d := by
      apply Int.ediv_le_self
      omega
    omega

lemma Calkin_Wilf_inv_div_add_one {q : ℚ} (hq : 0 < q) :
    Calkin_Wilf_inv (q / (q + 1)) = Calkin_Wilf_inv q * 2 := by
  have hp : 0 < q / (q + 1) := by positivity
  have hlt : q / (q + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hne : q / (q + 1) ≠ 1 := ne_of_lt hlt
  have heq : q / (q + 1) / (1 - q / (q + 1)) = q := by
    field_simp [show q + 1 ≠ 0 by positivity]
    ring
  rw [Calkin_Wilf_inv]
  simp [not_le.mpr hp, hne, hlt, heq]

lemma Calkin_Wilf_inv_add_one {q : ℚ} (hq : 0 < q) :
    Calkin_Wilf_inv (q + 1) = Calkin_Wilf_inv q * 2 + 1 := by
  have hp : ¬ q + 1 ≤ 0 := by linarith
  have hne : q + 1 ≠ 1 := by linarith
  have hnlt : ¬ q + 1 < 1 := by linarith
  rw [Calkin_Wilf_inv]
  simp [hp, hne, hnlt]

lemma Calkin_Wilf_mul_two {m : ℕ} (hm : m ≠ 0) :
    Calkin_Wilf (m * 2) = Calkin_Wilf m / (Calkin_Wilf m + 1) := by
  rw [Calkin_Wilf]
  have h0 : m * 2 ≠ 0 := by omega
  have h1 : m * 2 ≠ 1 := by omega
  have he : Even (m * 2) := by
    use m
    omega
  have hdiv : m * 2 / 2 = m := by omega
  simp [h0, h1, he, hdiv]

lemma Calkin_Wilf_mul_two_add_one (m : ℕ) :
    Calkin_Wilf (m * 2 + 1) = Calkin_Wilf m + 1 := by
  rw [Calkin_Wilf]
  have h0 : m * 2 + 1 ≠ 0 := by omega
  by_cases hm0 : m = 0
  · subst hm0
    simp [Calkin_Wilf]
  · have h1 : m * 2 + 1 ≠ 1 := by
      intro h
      omega
    have ho : ¬ Even (m * 2 + 1) := by
      rw [Nat.not_even_iff_odd]
      use m
      omega
    have hdiv : (m * 2 + 1) / 2 = m := by omega
    simp [ho, hdiv, hm0]

lemma Calkin_Wilf.leftInv : ∀ n, Calkin_Wilf_inv (Calkin_Wilf n) = n := by
  intro n
  fun_induction Calkin_Wilf n with
  | case1 =>
      simp [Calkin_Wilf_inv]
  | case2 =>
      simp [Calkin_Wilf_inv]
  | case3 n hn0 hn1 heven q ih =>
      rw [Calkin_Wilf_inv_div_add_one]
      · rw [ih]
        exact Nat.div_two_mul_two_of_even heven
      · apply Calkin_Wilf.pos
        omega
  | case4 n hn0 hn1 hodd q ih =>
      rw [Calkin_Wilf_inv_add_one]
      · rw [ih]
        have h := Nat.div_two_mul_two_add_one_of_odd (Nat.not_even_iff_odd.mp hodd)
        omega
      · apply Calkin_Wilf.pos
        omega

lemma Calkin_Wilf.rightInv : ∀ q ≥ 0, Calkin_Wilf (Calkin_Wilf_inv q) = q := by
  intro q hqnn
  fun_induction Calkin_Wilf_inv q with
  | case1 q hqp =>
      have : q = 0 := by linarith
      simp [this, Calkin_Wilf]
  | case2 a =>
      simp [Calkin_Wilf]
  | case3 a b c d e =>
      have ha_pos : 0 < a := lt_of_not_ge b
      have hden_pos : 0 < 1 - a := by linarith
      have hr_pos : 0 < a / (1 - a) := by positivity
      have hi := e (le_of_lt hr_pos)
      have hm : Calkin_Wilf_inv (a / (1 - a)) ≠ 0 := by
        intro hm
        have : a / (1 - a) = 0 := by
          simpa [hm, Calkin_Wilf] using hi.symm
        linarith
      rw [Calkin_Wilf_mul_two hm]
      rw [hi]
      field_simp [show (1 - a) ≠ 0 by linarith]
      ring
  | case4 a b c d e =>
      have ha_ge_one : 1 ≤ a := le_of_not_gt d
      have hr_nonneg : a - 1 ≥ 0 := by linarith
      have hi := e hr_nonneg
      rw [Calkin_Wilf_mul_two_add_one]
      rw [hi]
      ring


lemma Calkin_Wilf.injective : Function.Injective Calkin_Wilf := by
  intro n1 n2 heq
  have : Calkin_Wilf_inv (Calkin_Wilf n1) = Calkin_Wilf_inv (Calkin_Wilf n2) := by congr
  simpa[Calkin_Wilf.leftInv] using this

lemma Calkin_Wilf.posi_surjective : ∀ q > (0:ℚ), ∃n, Calkin_Wilf n = q := by
  intro q hq 
  have := rightInv q (le_of_lt hq)
  use Calkin_Wilf_inv  q

abbrev explicit_bijection : ℕ → ℚ := fun n ↦ if Even n then Calkin_Wilf (n/2) else - Calkin_Wilf ((n+1)/2)
lemma exp_bij_nonneg_of_even {n:ℕ} (hn : Even n) : 0 ≤ explicit_bijection n := by
  simp[explicit_bijection,hn]
  set n' := n /2
  by_cases! hn' : n' = 0
  . apply le_of_eq;symm; simpa[Calkin_Wilf.zero] using hn'
  apply le_of_lt; exact Calkin_Wilf.pos hn'

lemma exp_bij_neg_of_odd {n:ℕ} (hn : ¬ Even n) : explicit_bijection n < 0 := by
  simp[explicit_bijection,hn]
  apply Calkin_Wilf.pos
  simp;contrapose! hn
  observe : n = 0
  simp[this]

theorem explicit_bijection_spec : Function.Bijective explicit_bijection := by
  constructor
  . intro n1 n2 heq
    by_cases hn1 : Even n1 <;>
    by_cases hn2 : Even n2
    . unfold explicit_bijection at heq
      simp only [hn1, ↓reduceIte, hn2] at heq
      apply Calkin_Wilf.injective at heq
      have hd1 := Nat.div_two_mul_two_of_even hn1
      have hd2 := Nat.div_two_mul_two_of_even hn2
      omega
    . 
      have he1 := exp_bij_nonneg_of_even hn1
      have he2 := exp_bij_neg_of_odd hn2
      linarith
    . 
      have he2 := exp_bij_nonneg_of_even hn2
      have he1 := exp_bij_neg_of_odd hn1
      linarith
    unfold explicit_bijection at heq
    simp only [hn1, reduceIte ,hn2,neg_inj] at heq
    apply Calkin_Wilf.injective at heq
    simp at hn1 hn2
    apply Nat.div_two_mul_two_add_one_of_odd at hn1
    apply Nat.div_two_mul_two_add_one_of_odd at hn2
    omega
  intro q
  obtain (h|rfl|h) := lt_trichotomy q 0
  . 
    set q' := -q 
    observe hq' : q' > 0
    observe hqq : q = -q'
    choose n hn using Calkin_Wilf.posi_surjective q' hq'
    use 2*n - 1
    simp[explicit_bijection ]
    have hn0 : n ≠ 0 := by
      by_contra hn0 
      rw[Calkin_Wilf.zero] at hn0
      linarith
    have hodd : ¬ Even (2 * n - 1) := by
      simp; use n-1; omega

    simp only [hodd, ↓reduceIte ]
    have : (2*n-1+1)/2 = n := by omega
    simp[this,hqq,hn]
  . use 0; simp[explicit_bijection,Calkin_Wilf]
  choose n hn using Calkin_Wilf.posi_surjective q h
  use n*2; simp[explicit_bijection,hn]
    
end Chapter8
