import Mathlib.Tactic
import Analysis.Section_7_2
import Analysis.Section_7_3
import Analysis.Section_7_4
import Analysis.Section_8_1

/-!
# Analysis I, Section 8.2

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

-

-/

namespace Chapter8
open Chapter7

/-- Definition 8.2.1 (Series on countable sets).  Note that with this definition, functions defined
on finite sets will not be absolutely convergent; one should use `AbsConvergent'` instead for such
cases.-/
abbrev AbsConvergent {X:Type} (f: X → ℝ) : Prop := ∃ g: ℕ → X, Function.Bijective g ∧ (f ∘ g: Series).absConverges

theorem AbsConvergent.mk {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Function.Bijective g) (hfg: (f ∘ g:Series).absConverges) : AbsConvergent f := by use g

open Classical in
/-- The definition has been chosen to give a sensible value when `X` is finite, even though
`AbsConvergent` is by definition false in this context. -/
noncomputable abbrev Sum {X:Type} (f: X → ℝ) : ℝ := if h: AbsConvergent f then (f ∘ h.choose:Series).sum else
  if _hX: Finite X then (∑ x ∈ @Finset.univ X (Fintype.ofFinite X), f x) else 0

theorem Sum.of_finite {X:Type} [hX:Finite X] (f:X → ℝ) : Sum f = ∑ x ∈ @Finset.univ X (Fintype.ofFinite X), f x := by
  have : ¬ AbsConvergent f := by
    by_contra!
    obtain ⟨ g, hg, _ ⟩ := this
    rw [←hg.finite_iff, ←not_infinite_iff_finite] at hX
    exact hX (by infer_instance)
  simp [Sum, this, hX]

theorem AbsConvergent.comp {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Function.Bijective g) (hf: AbsConvergent f) : (f ∘ g:Series).absConverges := by
  obtain ⟨ hbij, hconv ⟩ := hf.choose_spec
  set g' := hf.choose
  obtain ⟨ g'_inv, hleft, hright ⟩ := Function.bijective_iff_has_inverse.mp hbij
  have hG : Function.Bijective (g'_inv ∘ g) :=
    Function.Bijective.comp ⟨ Function.LeftInverse.injective hright, Function.RightInverse.surjective hleft⟩ h
  convert (Series.absConverges_of_permute hconv hG).1 using 4 with n
  simp [hright (g n.toNat)]

theorem Sum.eq {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Function.Bijective g) (hfg: (f ∘ g:Series).absConverges) : (f ∘ g:Series).convergesTo (Sum f) := by
  have : AbsConvergent f := AbsConvergent.mk h hfg
  simp [Sum, this]
  obtain ⟨ hbij, hconv ⟩ := this.choose_spec
  set g' := this.choose
  obtain ⟨ g'_inv, hleft, hright ⟩ := Function.bijective_iff_has_inverse.mp hbij
  convert Series.convergesTo_sum (Series.converges_of_absConverges hfg) using 1
  have hG : Function.Bijective (g'_inv ∘ g) :=
    Function.Bijective.comp ⟨ Function.LeftInverse.injective hright, Function.RightInverse.surjective hleft⟩ h
  convert (Series.absConverges_of_permute hconv hG).2 using 4 with _ n
  by_cases hn : n ≥ 0 <;> simp [hn, hright (g n.toNat)]

theorem Sum.of_comp {X Y:Type} {f:X → ℝ} (h: AbsConvergent f) {g: Y → X} (hbij: Function.Bijective g) : AbsConvergent (f ∘ g) ∧ Sum f = Sum (f ∘ g) := by
  obtain ⟨ hbij', hconv' ⟩ := h.choose_spec
  set g' := h.choose
  obtain ⟨ g_inv, hleft, hright ⟩ := Function.bijective_iff_has_inverse.mp hbij
  have hbij_g_inv_g' : Function.Bijective (g_inv ∘ g') :=
    Function.Bijective.comp ⟨ Function.LeftInverse.injective hright, Function.RightInverse.surjective hleft⟩ hbij'
  have hident : (f ∘ g) ∘ g_inv ∘ g' = f ∘ g' := by ext n; simp [hright (g' n)]
  refine ⟨ ⟨ g_inv ∘ g', ⟨ hbij_g_inv_g', by convert hconv' ⟩ ⟩, ?_ ⟩
  have h := eq (f := f ∘ g) hbij_g_inv_g' (by convert hconv')
  rw [hident] at h
  exact Series.convergesTo_uniq (eq hbij' hconv') h

@[simp]
theorem Finset.Icc_eq_cast (N:ℕ) : Finset.Icc 0 (N:ℤ) = Finset.map Nat.castEmbedding (Finset.Icc 0 N) := by
  ext n
  simp; constructor
  . intro ⟨ hn, hn' ⟩; lift n to ℕ using hn; use n; simp_all
  rintro ⟨ m, ⟨ hm, rfl ⟩ ⟩; simp_all

theorem Finset.Icc_empty {N:ℤ} (h: ¬ N ≥ 0) : Finset.Icc 0 N = ∅ := by
  ext n; simp; intro hn; contrapose! h; linarith

/-- Theorem 8.2.2, preliminary version.  The arguments here are rearranged slightly from the text. -/
theorem sum_of_sum_of_AbsConvergent_nonneg {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) (hpos: ∀ n m, 0 ≤ f (n, m)) :
  (∀ n, ((fun m ↦ f (n, m)):Series).converges) ∧
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set L := Sum f
  have hLpos : 0 ≤ L := by
    simp [L, Sum, hf]
    apply Series.sum_of_nonneg
    intro n; by_cases h: n ≥ 0 <;> simp [h]; exact hpos _ _
  have hfinsum (X: Finset (ℕ × ℕ)) : ∑ p ∈ X, f p ≤ L := by sorry
  have hfinsum' (n M:ℕ) : ((fun m ↦ f (n, m)):Series).partial M ≤ L := by
    simp [Series.partial, Finset.Icc_eq_cast]
    convert_to ∑ x ∈ Finset.map (Function.Embedding.sectR n ℕ) (Finset.Icc 0 M), f x ≤ L
    . simp
    solve_by_elim
  have hnon (n:ℕ) : ((fun m ↦ f (n, m)):Series).nonneg := by
    simp [Series.nonneg]
    intro m; by_cases h: m ≥ 0 <;> simp [h, hpos]
  have hconv (n:ℕ) : ((fun m ↦ f (n, m)):Series).converges := by
    rw [Series.converges_of_nonneg_iff (hnon n)]
    use L; intro N; by_cases h: N ≥ 0
    . lift N to ℕ using h; solve_by_elim
    rw [Series.partial_of_lt (by simp; linarith)]; simp [hLpos]
  have (N M:ℤ) : ∑ n ∈ Finset.Icc 0 N, ((fun m ↦ f (n.toNat, m)):Series).partial M ≤ L := by
    by_cases hN : N ≥ 0; swap
    . simp [Finset.Icc_empty hN, hLpos]
    lift N to ℕ using hN
    by_cases hM : M ≥ 0; swap
    . convert hLpos; unfold Series.partial
      apply Finset.sum_eq_zero; intro n _
      simp [Finset.Icc_empty hM]
    lift M to ℕ using hM
    convert_to ∑ x ∈ (Finset.Icc 0 N) ×ˢ (Finset.Icc 0 M), f x ≤ L
    . simp [Finset.sum_product, Series.partial]
    solve_by_elim
  replace (N:ℤ) : ∑ n ∈ Finset.Icc 0 N, ((fun m ↦ f (n.toNat, m)):Series).sum ≤ L := by
    apply le_of_tendsto' (x := Filter.atTop) (tendsto_finset_sum _ _) (this N)
    intro n _; exact Series.convergesTo_sum (by solve_by_elim)
  replace (N:ℤ) : (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).partial N ≤ L := by
    convert this N with n hn
    simp_all
  have hnon' : (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).nonneg := by
    intro n; by_cases h: n ≥ 0 <;> simp [h]
    exact Series.sum_of_nonneg (hnon n.toNat)
  have hconv' : (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).converges := by
    rw [Series.converges_of_nonneg_iff hnon']; use L
  replace : (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).sum ≤ L :=
    le_of_tendsto' ( Series.convergesTo_sum hconv') this
  replace : (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).sum = L := by
    apply le_antisymm this (le_of_forall_sub_le _); intro ε hε
    replace : ∃ X, ∑ p ∈ X, f p ≥ L - ε := by
      sorry
    obtain ⟨ X, hX ⟩ := this
    have : ∃ N, ∃ M, X ⊆ (Finset.Icc 0 N) ×ˢ (Finset.Icc 0 M) := by
      sorry
    obtain ⟨ N, M, hX' ⟩ := this
    calc
      _ ≤ ∑ p ∈ X, f p := hX
      _ ≤ ∑ p ∈ (Finset.Icc 0 N) ×ˢ (Finset.Icc 0 M), f p :=
        Finset.sum_le_sum_of_subset_of_nonneg hX' (by solve_by_elim)
      _ = ∑ n ∈ Finset.Icc 0 N, ∑ m ∈ Finset.Icc 0 M, f (n, m) := Finset.sum_product _ _ _
      _ ≤ ∑ n ∈ Finset.Icc 0 N, ((fun m ↦ f (n, m)):Series).sum := by
        apply Finset.sum_le_sum; intro n _
        convert Series.partial_le_sum_of_nonneg (hnon n) (hconv n) M
        simp [Series.partial]
      _ = (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).partial N := by simp [Series.partial]
      _ ≤ _ := Series.partial_le_sum_of_nonneg hnon' hconv' _
  simp [hconv, ← this, Series.convergesTo_sum hconv']

/-- Theorem 8.2.2, second version -/
theorem sum_of_sum_of_AbsConvergent {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (∀ n, ((fun m ↦ f (n, m)):Series).absConverges) ∧
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set fplus := max f 0
  set fminus := max (-f) 0
  have hfplus_nonneg : ∀ n m, 0 ≤ fplus (n, m) := by intro n m; simp [fplus]
  have hfminus_nonneg : ∀ n m, 0 ≤ fminus (n, m) := by intro n m; simp [fminus]
  have hdiff : f = fplus - fminus := by sorry
  have hfplus_conv : AbsConvergent fplus := by sorry
  have hfminus_conv : AbsConvergent fminus := by sorry
  obtain ⟨ hfplus_conv', hfplus_sum⟩ := sum_of_sum_of_AbsConvergent_nonneg hfplus_conv hfplus_nonneg
  obtain ⟨ hfminus_conv', hfminus_sum⟩ := sum_of_sum_of_AbsConvergent_nonneg hfminus_conv hfminus_nonneg
  constructor
  . intro n
    sorry
  convert Series.convergesTo.sub hfplus_sum hfminus_sum using 1
  . -- encountered surprising difficulty with definitional equivalence here
    simp [hdiff]
    change (fun n ↦ ((fun m ↦ (fplus - fminus) (n, m)):Series).sum:Series) =
      (fun n ↦ ((fun m ↦ fplus (n, m)):Series).sum:Series)
      - (fun n ↦ ((fun m ↦ (fminus) (n, m)):Series).sum:Series)
    convert_to (fun n ↦ ((fun m ↦ (fplus - fminus) (n, m)):Series).sum:Series) =
      (((fun n ↦ ((fun m ↦ fplus (n, m)):Series).sum) - (fun n ↦ ((fun m ↦ (fminus) (n, m)):Series).sum):ℕ → ℝ):Series)
    . convert Series.sub_coe _ _
    rcongr _ n
    simp
    convert (Series.sub _ _).2 with m
    . rfl
    by_cases h: m ≥ 0 <;> simp [h, HSub.hSub, Sub.sub]
    . solve_by_elim
    convert hfminus_conv' n.toNat
  have := hf
  obtain ⟨ g, hg, _ ⟩ := this
  have h1 := Sum.eq hg (hf.comp hg)
  have hplus := Sum.eq hg (hfplus_conv.comp hg)
  have hminus := Sum.eq hg (hfminus_conv.comp hg)
  apply Series.convergesTo_uniq h1 _
  convert (Series.convergesTo.sub hplus hminus) using 3 with n
  by_cases h:n ≥ 0 <;> simp [h,hdiff, HSub.hSub, Sub.sub]

/-- Theorem 8.2.2, third version -/
theorem sum_of_sum_of_AbsConvergent' {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (∀ m, ((fun n ↦ f (n, m)):Series).absConverges) ∧
  (fun m ↦ ((fun n ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set π: ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.2, p.1)
  have hπ: Function.Bijective π := Function.Involutive.bijective (congrFun rfl)
  have := hf
  obtain ⟨ g, hg, hconv ⟩ := this
  convert sum_of_sum_of_AbsConvergent (f := f ∘ π) _ using 2
  . exact (Sum.of_comp hf hπ).2
  refine ⟨ π ∘ g, Function.Bijective.comp hπ hg, ?_ ⟩
  convert hconv using 2

/-- Theorem 8.2.2, fourth version -/
theorem sum_comm {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).sum = (fun m ↦ ((fun n ↦ f (n, m)):Series).sum:Series).sum := by
  simp [Series.sum_of_converges (sum_of_sum_of_AbsConvergent hf).2,
        Series.sum_of_converges (sum_of_sum_of_AbsConvergent' hf).2]

/-- Lemma 8.2.3 / Exercise 8.2.1 -/
theorem AbsConvergent.iff {X:Type} (hX:CountablyInfinite X) (f : X → ℝ) :
  AbsConvergent f ↔ BddAbove ( (fun A ↦ ∑ x ∈ A, |f x|) '' Set.univ ) := by
    sorry

abbrev AbsConvergent' {X:Type} (f: X → ℝ) : Prop := BddAbove ( (fun A ↦ ∑ x ∈ A, |f x|) '' Set.univ )

theorem AbsConvergent'.of_finite {X:Type} [Finite X] (f:X → ℝ) : AbsConvergent' f := by
  have _ := Fintype.ofFinite X
  simp [bddAbove_def]
  use ∑ x, |f x|
  intro A
  apply Finset.sum_le_univ_sum_of_nonneg; simp

/-- Not in textbook, but should have been included. -/
theorem AbsConvergent'.of_countable {X:Type} (hX:CountablyInfinite X) {f:X → ℝ} :
  AbsConvergent' f ↔ AbsConvergent f := by
  constructor
  . intro hf
    simp [bddAbove_def] at hf
    obtain ⟨ L, hL ⟩ := hf
    obtain ⟨ g, hg ⟩ := hX.symm
    refine ⟨ g, hg, ?_ ⟩
    unfold Series.absConverges
    rw [Series.converges_of_nonneg_iff]
    . use L; intro N
      by_cases hN: N ≥ 0
      . lift N to ℕ using hN
        set g':= Function.Embedding.mk g hg.1
        convert hL (Finset.map g' (Finset.Icc 0 N))
        simp [Series.partial]; rfl
      convert hL ∅
      simp
      apply Series.partial_of_lt
      simp; contrapose! hN; assumption
    simp [Series.nonneg]
    intro n; by_cases h: n ≥ 0 <;> simp [h]
  intro hf
  rwa [AbsConvergent.iff hX f] at hf

/-- Lemma 8.2.5 / Exercise 8.2.2-/
theorem AbsConvergent'.countable_supp {X:Type} (f:X → ℝ) (hf: AbsConvergent' f) :
  AtMostCountable { x | f x ≠ 0 } := by
    sorry

/-- A generalized sum.  Note that this will give junk values if `f` is not `AbsConvergent'`. -/
noncomputable abbrev Sum' {X:Type} (f: X → ℝ) : ℝ := Sum (fun x : { x | f x ≠ 0 } ↦ f x)

/-- Not in textbook, but should have been included (the series laws are significantly harder
to establish without this) -/
theorem Sum'.of_finsupp {X:Type} {f:X → ℝ} {A: Finset X} (h: ∀ x ∉ A, f x = 0) : Sum' f = ∑ x ∈ A, f x := by
  unfold Sum'
  set E := { x | f x ≠ 0 }
  have hE : E ⊆ A := by
    intro x; simp [E]; by_contra!; specialize h x this.2; tauto
  have hfin : Finite E := Finite.Set.subset _ hE
  set E' := E.toFinite.toFinset
  rw [Sum.of_finite (fun x:E ↦ f x), ←Finset.sum_subtype E' (by simp [E'])]
  replace hE : E' ⊆ A := by aesop
  apply Finset.sum_subset hE
  aesop

/-- Not in textbook, but should have been included (the series laws are significantly harder
to establish without this) -/
theorem Sum'.of_countable_supp {X:Type} {f:X → ℝ} {A: Set X} (hA: CountablyInfinite A)
  (hfA : ∀ x ∉ A, f x = 0) (hconv: AbsConvergent' f):
  AbsConvergent' (fun x:A ↦ f x) ∧ Sum' f = Sum (fun x:A ↦ f x) := by
  -- We can adapt the proof of `AbsConvergent'.of_countable` to establish absolute convergence on A.
  have hconv' : AbsConvergent (fun x:A ↦ f x) := by
    simp [bddAbove_def] at hconv
    obtain ⟨ L, hL ⟩ := hconv
    obtain ⟨ g, hg ⟩ := hA.symm
    refine ⟨ g, hg, ?_ ⟩
    unfold Series.absConverges
    rw [Series.converges_of_nonneg_iff]
    . use L; intro N
      by_cases hN: N ≥ 0
      . lift N to ℕ using hN
        set g':= Function.Embedding.mk (Subtype.val ∘ g)
          (Function.Injective.comp (Subtype.val_injective) hg.1)
        convert hL (Finset.map g' (Finset.Icc 0 N))
        simp [Series.partial]; rfl
      convert hL ∅
      simp
      apply Series.partial_of_lt
      simp; contrapose! hN; assumption
    simp [Series.nonneg]
    intro n; by_cases h: n ≥ 0 <;> simp [h]
  rw [AbsConvergent'.of_countable hA]
  refine ⟨ hconv', ?_ ⟩
  unfold Sum'
  set E := { x | f x ≠ 0 }
  -- The main challenge here is to relate a sum on E with a sum on A.  First, we show containment.
  have hE : E ⊆ A := by
    intro x; simp [E]; by_contra!; specialize hfA x this.2; tauto
  -- Now, we map A back to the natural numbers, thus identifying E with a subset E' of ℕ.
  obtain ⟨ g, hg ⟩ := hA.symm
  have hsum := Sum.eq hg (AbsConvergent.comp hg hconv')
  set E' := { n | ↑(g n) ∈ E }
  set ι : E' → E := fun ⟨ n, hn ⟩ ↦ ⟨ (g n).val, by aesop ⟩
  have hι: Function.Bijective ι := by
    constructor
    . intro ⟨ n, hn ⟩ ⟨ m, hm ⟩ h
      simp [ι, E', Subtype.val_inj] at hn hm h ⊢; exact hg.1 h
    . intro ⟨ x, hx ⟩
      obtain ⟨ n, hn ⟩ := hg.2 ⟨ x, hE hx ⟩
      use ⟨ n, by aesop ⟩
      simp [ι, hn]
  -- The cases of infinite and finite E' are handled separately.
  rcases Nat.atMostCountable_subset E' with hE' | hE'
  . --   use Nat.monotone_enum_of_infinite to enumerate E'
    --   show the partial sums of E' are a subsequence of the partial sums of A
    set hinf : Infinite E' := hE'.toInfinite
    obtain ⟨ a, ha_bij, ha_mono ⟩ := (Nat.monotone_enum_of_infinite E').exists
    have : Filter.Tendsto (Nat.cast ∘ Subtype.val ∘ a: ℕ → ℤ) Filter.atTop Filter.atTop := by
      apply tendsto_natCast_atTop_atTop.comp
      apply StrictMono.tendsto_atTop
      intro n m hnm
      simp [ha_mono hnm]
    replace hsum := hsum.comp this
    apply tendsto_nhds_unique  _ hsum
    have hconv'' : AbsConvergent (fun x:E ↦ f x) := by
      rw [←AbsConvergent'.of_countable]
      . sorry
      apply (CountablyInfinite.equiv _).mp hE'; use ι
    replace := Sum.eq (hι.comp ha_bij) (AbsConvergent.comp (hι.comp ha_bij) hconv'')
    replace := this.comp tendsto_natCast_atTop_atTop
    convert this using 1; ext N
    simp [Series.partial, ι]
    calc
      _ = ∑ x ∈ Finset.image (Subtype.val ∘ a) (Finset.Icc 0 N), f ↑(g x) := by
        apply (Finset.sum_subset _ _).symm
        . intro m hm; simp at hm ⊢
          obtain ⟨ n, hn, rfl ⟩ := hm
          simp [ha_mono.monotone hn]
        intro x hx hx'; simp at hx hx'
        contrapose! hx'
        obtain ⟨ n, hn ⟩ := (hι.comp ha_bij).2 ⟨ ↑(g x), hx' ⟩
        simp [ι, Subtype.val_inj] at hn
        replace hn := hg.1 hn; subst hn
        use n; simp [ha_mono.le_iff_le] at ⊢ hx
        assumption
      _ = _ := by
        apply Finset.sum_image _
        intro n hn m hm h
        simp [Subtype.val_inj] at h
        exact ha_bij.1 h
  -- When E' is finite, we show that all sufficiently large partial sums of A are equal to
  -- the sum of E'.
  let hEfin : Finite E := hι.finite_iff.mp hE'
  let hE'fintype : Fintype E' := Fintype.ofFinite _
  let hEfintype : Fintype E := Fintype.ofFinite _
  apply Series.convergesTo_uniq _ hsum
  simp [Sum.of_finite, Series.convergesTo]
  apply tendsto_nhds_of_eventually_eq
  have hE'bound : BddAbove E' := Set.Finite.bddAbove hE'
  rw [bddAbove_def] at hE'bound; obtain ⟨ N, hN ⟩ := hE'bound
  rw [Filter.eventually_atTop]
  use N; intro N' hN'
  have : N' ≥ 0 := by apply LE.le.trans _ hN'; positivity
  lift N' to ℕ using this
  simp at hN'
  simp [Series.partial]
  calc
    _ = ∑ n ∈ E', f ↑(g n) := by
      apply (Finset.sum_subset _ _).symm
      . intro x; simp; intro hx; linarith [hN x hx]
      intro x hx hx'
      simp [E',E] at hx'; assumption
    _ = ∑ n:E', f ↑(g ↑n) := by
      convert (Finset.sum_set_coe _).symm
    _ = ∑ n, f ↑(ι n) := by
      apply Finset.sum_congr rfl
      intro ⟨ x, hx ⟩ _
      simp [ι]
    _ = _ := hι.sum_comp (g := fun x ↦ f ↑x)








-- make connections with Summable and tsum




end Chapter8
