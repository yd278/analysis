import Mathlib.Tactic
import Analysis.Section_7_2
import Analysis.Section_7_3
import Analysis.Section_7_4
import Analysis.Section_8_1

/-!
# Analysis I, Section 8.2: Summation on infinite sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Absolute convergence and summation on countably infinite or general sets.
- Connections with Mathlib's {name}`Summable` and {name}`tsum`.
- The Riemann rearrangement theorem.

Some non-trivial API is provided beyond what is given in the textbook in order connect these
notions with existing summation notions.

After this section, the summation notation developed here will be deprecated in favor of Mathlib's API for {name}`Summable` and {name}`tsum`.

-/

namespace Chapter8
open Chapter7 Chapter7.Series Finset Function Filter

/-- Definition 8.2.1 (Series on countable sets).  Note that with this definition, functions defined
on finite sets will not be absolutely convergent; one should use {lit}`AbsConvergent'` instead for such
cases.-/
abbrev AbsConvergent {X:Type} (f: X → ℝ) : Prop := ∃ g: ℕ → X, Bijective g ∧ (f ∘ g: Series).absConverges

theorem AbsConvergent.mk {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hfg: (f ∘ g:Series).absConverges) : AbsConvergent f := by use g

open Classical in
/-- The definition has been chosen to give a sensible value when {name}`X` is finite, even though
{name}`AbsConvergent` is by definition false in this context. -/
noncomputable abbrev Sum {X:Type} (f: X → ℝ) : ℝ := if h: AbsConvergent f then (f ∘ h.choose:Series).sum else
  if _hX: Finite X then (∑ x ∈ @univ X (Fintype.ofFinite X), f x) else 0

theorem Sum.of_finite {X:Type} [hX:Finite X] (f:X → ℝ) : Sum f = ∑ x ∈ @Finset.univ X (Fintype.ofFinite X), f x := by
  have : ¬ AbsConvergent f := by
    by_contra!; choose g hg _ using this
    rw [←hg.finite_iff, ←not_infinite_iff_finite] at hX; apply hX; infer_instance
  simp [Sum, this, hX]

theorem AbsConvergent.comp {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hf: AbsConvergent f) : (f ∘ g:Series).absConverges := by
  choose g' hbij hconv using hf
  choose g'_inv hleft hright using bijective_iff_has_inverse.mp hbij
  have hG : Bijective (g'_inv ∘ g) := .comp ⟨hright.injective, hleft.surjective⟩ h
  convert (absConverges_of_permute hconv hG).1 using 4 with n
  simp [hright (g n.toNat)]

theorem Sum.eq {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hfg: (f ∘ g:Series).absConverges) : (f ∘ g:Series).convergesTo (Sum f) := by
  have : AbsConvergent f := .mk h hfg
  simp [Sum, this]
  choose hbij hconv using this.choose_spec
  set g' := this.choose
  choose g'_inv hleft hright using bijective_iff_has_inverse.mp hbij
  convert convergesTo_sum (converges_of_absConverges hfg) using 1
  have hG : Bijective (g'_inv ∘ g) := .comp ⟨hright.injective, hleft.surjective⟩ h
  convert (absConverges_of_permute hconv hG).2 using 4 with _ n
  by_cases hn : n ≥ 0 <;> simp [hn, hright (g n.toNat)]

theorem Sum.of_comp {X Y:Type} {f:X → ℝ} (h: AbsConvergent f) {g: Y → X} (hbij: Bijective g) : AbsConvergent (f ∘ g) ∧ Sum f = Sum (f ∘ g) := by
  choose g' hbij' hconv' using h
  choose g_inv hleft hright using bijective_iff_has_inverse.mp hbij
  have hbij_g_inv_g' : Bijective (g_inv ∘ g') := .comp ⟨hright.injective, hleft.surjective⟩ hbij'
  have hident : (f ∘ g) ∘ g_inv ∘ g' = f ∘ g' := by ext n; simp [hright (g' n)]
  refine ⟨ ⟨ g_inv ∘ g', ⟨ hbij_g_inv_g', by convert hconv' ⟩ ⟩, ?_ ⟩
  have h := eq (f := f ∘ g) hbij_g_inv_g' (by convert hconv')
  rw [hident] at h
  solve_by_elim [convergesTo_uniq, eq]

@[simp]
theorem Finset.Icc_eq_cast (N:ℕ) : Icc 0 (N:ℤ) = map Nat.castEmbedding (.Icc 0 N) := by
  ext n; simp; constructor
  . intro ⟨ hn, _ ⟩; lift n to ℕ using hn; use n; simp_all
  rintro ⟨ _, ⟨ _, rfl ⟩ ⟩; simp_all

theorem Finset.Icc_empty {N:ℤ} (h: ¬ N ≥ 0) : Icc 0 N = ∅ := by
  ext; simp; intros; contrapose! h; linarith

/-- Theorem 8.2.2, preliminary version.  The arguments here are rearranged slightly from the text. -/
theorem sum_of_sum_of_AbsConvergent_nonneg {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) (hpos: ∀ n m, 0 ≤ f (n, m)) :
  (∀ n, ((fun m ↦ f (n, m)):Series).converges) ∧
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set L := Sum f
  set a : ℕ → Series := fun n ↦ ((fun m ↦ f (n, m)):Series)
  have hLpos : 0 ≤ L := by
    simp [L, Sum, hf]; apply sum_of_nonneg; intro n; by_cases h: n ≥ 0 <;> simp [h]; grind
  have hfinsum (X: Finset (ℕ × ℕ)) : ∑ p ∈ X, f p ≤ L := by
    -- edge case: empty set
    by_cases hX : X = ∅ 
    . simp[hX,hLpos]

    have hf' := hf
    choose g hgbij hgconv using hf'
    have h_comp_conv :=  Sum.eq hgbij hgconv
    replace hgconv := converges_of_absConverges hgconv
    have hnonneg : (f ∘ g : Series).nonneg  := by
      simp[nonneg];intro z;split_ifs with hz
      . lift z to ℕ using hz;simp[hpos]
      simp
    set g' := g.invFun 
    set N := (X.image g').max' (by simp [nonempty_iff_ne_empty, hX])
    have hpartial : (f ∘ g:Series).partial N ≤ L := by
      have := partial_le_sum_of_nonneg hnonneg hgconv N
      simp[L]; convert this;symm
      exact sum_of_converges h_comp_conv
    apply le_trans' hpartial
    simp[Series.partial]
    have hcong :   ∑ x ∈ X.image g', f (g x) = ∑ p ∈ X, f p := by
      rw [Finset.sum_image]
      . apply sum_congr rfl
        intro p hp
        simp [g', Function.rightInverse_invFun hgbij.surjective p]
      intro p _ q _ hpq
      simpa [g', Function.rightInverse_invFun hgbij.surjective p,
        Function.rightInverse_invFun hgbij.surjective q] using congrArg g hpq
    rw[← hcong]
    apply sum_le_sum_of_subset_of_nonneg
    . simp[N]
      intro x  hx
      simp
      apply le_max'
      assumption
    simp[hpos] 
  have hfinsum' (n M:ℕ) : (a n).partial M ≤ L := by
    simp [a, Series.partial, Finset.Icc_eq_cast]
    convert_to ∑ x ∈ .map (Embedding.sectR n ℕ) (.Icc 0 M), f x ≤ L
    . simp
    solve_by_elim
  have hnon (n:ℕ) : (a n).nonneg := by
    simp [a, nonneg]; intro m; split_ifs <;> simp [hpos]
  have hconv (n:ℕ) : (a n).converges := by
    rw [converges_of_nonneg_iff (hnon n)]
    use L; intro N; by_cases h: N ≥ 0
    . lift N to ℕ using h; solve_by_elim
    rw [partial_of_lt (by simp [a]; linarith)]; simp [hLpos]
  have (N M:ℤ) : ∑ n ∈ Icc 0 N, (a n.toNat).partial M ≤ L := by
    by_cases hN : N ≥ 0; swap
    . simp [Finset.Icc_empty hN, hLpos]
    lift N to ℕ using hN
    by_cases hM : M ≥ 0; swap
    . convert hLpos; unfold Series.partial
      apply sum_eq_zero; intro n _
      simp [a, Finset.Icc_empty hM]
    lift M to ℕ using hM
    convert_to ∑ x ∈ (Icc 0 N) ×ˢ (.Icc 0 M), f x ≤ L
    . simp [a, sum_product, Series.partial]
    solve_by_elim
  replace (N:ℤ) : ∑ n ∈ Icc 0 N, (a n.toNat).sum ≤ L := by
    apply le_of_tendsto' (x := .atTop) (tendsto_finset_sum _ _) (this N)
    solve_by_elim [convergesTo_sum]
  replace (N:ℤ) : (fun n ↦ (a n).sum:Series).partial N ≤ L := by
    convert this N with n hn; simp_all
  have hnon' : (fun n ↦ (a n).sum:Series).nonneg := by
    intro n; simp; split_ifs
    . exact sum_of_nonneg (hnon n.toNat)
    simp
  have hconv' : (fun n ↦ (a n).sum:Series).converges := by
    rw [converges_of_nonneg_iff hnon']; use L
  replace : (fun n ↦ (a n).sum:Series).sum ≤ L := le_of_tendsto' (convergesTo_sum hconv') this
  replace : (fun n ↦ (a n).sum:Series).sum = L := by
    apply le_antisymm this (le_of_forall_sub_le _); intro ε hε
    replace : ∃ X, ∑ p ∈ X, f p ≥ L - ε := by
      choose g hgbij hgconv using hf
      set C := (f ∘ g:Series) with hC
      have hnonneg : C.nonneg  := by
        simp[C,nonneg];intro n;split_ifs <;> grind
      have hple:=  partial_le_sum_of_nonneg hnonneg (converges_of_absConverges hgconv)
      have hsum := Sum.eq hgbij hgconv
      rw[← hC] at hsum
      have hCsum := sum_of_converges hsum
      simp[convergesTo] at hsum
      rw[Metric.tendsto_atTop] at hsum
      specialize hsum ε hε 
      choose N' hN' using hsum
      set N := (max N' 0).toNat
      specialize hN' N (by omega)
      simp[dist] at hN'
      rw[abs_of_nonpos (by simp;convert (hple N);simp[hCsum])] at hN'
      simp at hN'
      rw[sub_lt_comm] at hN'
      use (Icc 0 N).image g
      apply le_of_lt
      convert hN'
      simp[C,Series.partial]
      apply sum_image
      intro p _ q _ hpq
      apply hgbij.injective hpq
    choose X hX using this
    have : ∃ N, ∃ M, X ⊆ (Icc 0 N) ×ˢ (Icc 0 M) := by
      by_cases hXe : X ≠ ∅ ; swap
      . simp at hXe; simp[hXe]
      set N := (X.image (Prod.fst)).max' (by rwa[image_nonempty,nonempty_iff_ne_empty])
      set M := (X.image (Prod.snd)).max' (by rwa[image_nonempty,nonempty_iff_ne_empty])
      use N,M
      intro x hx 
      simp[N,M]
      split_ands
      <;> apply le_max'
      <;> simp only [mem_image ]
      <;> use x
    choose N M hX' using this
    calc
      _ ≤ ∑ p ∈ X, f p := hX
      _ ≤ ∑ p ∈ (Icc 0 N) ×ˢ (Icc 0 M), f p := sum_le_sum_of_subset_of_nonneg hX' (by solve_by_elim)
      _ = ∑ n ∈ Icc 0 N, ∑ m ∈ Icc 0 M, f (n, m) := sum_product _ _ _
      _ ≤ ∑ n ∈ Icc 0 N, (a n).sum := by
        apply sum_le_sum; intro n _
        convert partial_le_sum_of_nonneg (hnon n) (hconv n) M
        simp [a, Series.partial]
      _ = (fun n ↦ (a n).sum:Series).partial N := by simp [Series.partial]
      _ ≤ _ := partial_le_sum_of_nonneg hnon' hconv' _
  simp [a, hconv, ← this, Series.convergesTo_sum hconv']

/-- Theorem 8.2.2, second version -/
theorem sum_of_sum_of_AbsConvergent {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (∀ n, ((fun m ↦ f (n, m)):Series).absConverges) ∧
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set fplus := max f 0
  set fminus := max (-f) 0
  have hfplus_nonneg : ∀ n m, 0 ≤ fplus (n, m) := by intro n m; simp [fplus]
  have hfminus_nonneg : ∀ n m, 0 ≤ fminus (n, m) := by intro n m; simp [fminus]
  have hdiff : f = fplus - fminus := by 
    ext n
    simp[fplus,fminus]
  have hfplus_conv : AbsConvergent fplus := by 
    choose g hgbij hconv using hf
    use g;simp only [hgbij, true_and]
    unfold absConverges  at hconv 
    set t := (f ∘ g:Series)
    set s := (fplus ∘ g:Series)
    have hm :s.m = t.abs.m := by simp[s,t]
    refine (converges_of_le  hm ?_ hconv).1
    intro n hn; simp[s] at hn
    lift n to ℕ using hn
    simp[s,t,fplus]
    grind
  have hfminus_conv : AbsConvergent fminus := by 
    choose g hgbij hconv using hf
    use g;simp only [hgbij, true_and]
    unfold absConverges  at hconv 
    set t := (f ∘ g:Series)
    set s := (fminus ∘ g:Series)
    have hm :s.m = t.abs.m := by simp[s,t]
    refine (converges_of_le  hm ?_ hconv).1
    intro n hn; simp[s] at hn
    lift n to ℕ using hn
    simp[s,t,fminus]
    grind
  choose hfplus_conv' hfplus_sum using sum_of_sum_of_AbsConvergent_nonneg hfplus_conv hfplus_nonneg
  choose hfminus_conv' hfminus_sum using sum_of_sum_of_AbsConvergent_nonneg hfminus_conv hfminus_nonneg
  split_ands
  . intro n
    specialize hfplus_conv' n
    specialize hfminus_conv' n
    unfold absConverges
    set splus := (fun m ↦ fplus (n,m))
    set sminus := (fun m ↦ fminus (n,m))
    convert (Series.add hfplus_conv' hfminus_conv').1 using 1
    unfold Series.abs
    rw[add_coe]
    ext m;.simp
    simp[splus,sminus,fplus,fminus]
    grind
  convert convergesTo.sub hfplus_sum hfminus_sum using 1
  . -- encountered surprising difficulty with definitional equivalence here
    simp [hdiff]
    change (fun n ↦ ((fun m ↦ (fplus - fminus) (n, m)):Series).sum:Series) =
      (fun n ↦ ((fun m ↦ fplus (n, m)):Series).sum:Series)
      - (fun n ↦ ((fun m ↦ (fminus) (n, m)):Series).sum:Series)
    convert_to (fun n ↦ ((fun m ↦ (fplus - fminus) (n, m)):Series).sum:Series) =
      (((fun n ↦ ((fun m ↦ fplus (n, m)):Series).sum) - (fun n ↦ ((fun m ↦ (fminus) (n, m)):Series).sum):ℕ → ℝ):Series)
    . convert sub_coe _ _
    rcongr _ n; simp
    convert (sub _ _).2 with m; rfl
    split_ifs with h <;> simp [h, HSub.hSub, Sub.sub]
    . solve_by_elim
    convert hfminus_conv' n.toNat
  have ⟨ g, hg, _ ⟩ := hf
  have h1 := Sum.eq hg (hf.comp hg)
  have hplus := Sum.eq hg (hfplus_conv.comp hg)
  have hminus := Sum.eq hg (hfminus_conv.comp hg)
  apply convergesTo_uniq h1 _
  convert (convergesTo.sub hplus hminus) using 3 with n
  split_ifs with h <;> simp [h, hdiff, HSub.hSub, Sub.sub]

/-- Theorem 8.2.2, third version -/
theorem sum_of_sum_of_AbsConvergent' {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (∀ m, ((fun n ↦ f (n, m)):Series).absConverges) ∧
  (fun m ↦ ((fun n ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set π: ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.2, p.1)
  have hπ: Bijective π := Involutive.bijective (congrFun rfl)
  have ⟨ g, hg, hconv ⟩ := hf
  convert sum_of_sum_of_AbsConvergent (f := f ∘ π) _ using 2
  . exact (Sum.of_comp hf hπ).2
  refine ⟨ _, hπ.comp hg, ?_ ⟩
  convert hconv using 2

/-- Theorem 8.2.2, fourth version -/
theorem sum_comm {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).sum = (fun m ↦ ((fun n ↦ f (n, m)):Series).sum:Series).sum := by
  simp [sum_of_converges (sum_of_sum_of_AbsConvergent hf).2,
        sum_of_converges (sum_of_sum_of_AbsConvergent' hf).2]

/-- Lemma 8.2.3 / Exercise 8.2.1 -/
theorem AbsConvergent.iff {X:Type} (hX:CountablyInfinite X) (f : X → ℝ) :
  AbsConvergent f ↔ BddAbove ( (fun A ↦ ∑ x ∈ A, |f x|) '' .univ ) := by
    constructor
    . intro hf
      choose g hgbij hgconv using hf
      set s := (f ∘ g:Series)
      have hnonneg : s.abs.nonneg  := by
        simp[nonneg];intro n; split_ifs <;>simp
      have := partial_le_sum_of_nonneg hnonneg  hgconv
      choose L hL using hgconv
      have hLpos : 0 ≤ L := by 
        rw[← sum_of_converges hL]
        apply sum_of_nonneg hnonneg
      rw[sum_of_converges hL] at this
      unfold convergesTo  at hL
      use L;rw[mem_upperBounds]
      intro l hl
      simp at hl
      choose A hA using hl
      by_cases! hl0 : l = 0
      . linarith
      rw[← hA] at hl0
      have hAnone:= nonempty_of_sum_ne_zero hl0
      set N := (A.image (g.invFun)).max' (by rwa[image_nonempty])
      specialize this N
      apply le_trans' this 
      rw[← hA];unfold Series.partial
      simp[s,N]
      have hcong :   ∑ x ∈ A.image g.invFun, |f (g x)| = ∑ p ∈ A, |f p| := by
        rw [Finset.sum_image]
        . apply sum_congr rfl
          intro p hp
          simp [Function.rightInverse_invFun hgbij.surjective p]
        intro p _ q _ hpq
        simpa [ Function.rightInverse_invFun hgbij.surjective p,
          Function.rightInverse_invFun hgbij.surjective q] using congrArg g hpq
      rw[← hcong]
      apply sum_le_sum_of_subset_of_nonneg
      . intro n hn 
        simp;apply le_max';assumption
      simp
    rintro ⟨L,hL⟩ 
    have ⟨hXC, hXI⟩  := (CountablyInfinite.iff' X).mp hX
    rw[mem_upperBounds] at hL
    choose g hgbij using hX
    have hLpos : 0 ≤ L := by
      observe hXn : Nonempty X
      set x := hXn.some
      specialize hL |f x|
      simp at hL
      specialize hL {x}
      simp at hL
      grind
    set ge := Equiv.ofBijective g hgbij
    use ge.symm;constructor; apply Equiv.bijective
    unfold absConverges
    set s := (f ∘ ge.symm:Series).abs
    have hsnonneg : s.nonneg  := by
      simp[nonneg,s];intro n; split_ifs <;> grind
    rw[converges_of_nonneg_iff hsnonneg]
    use L;intro N
    by_cases! hN0 : N ≥ 0;swap
    . rwa[partial_of_lt (by simpa[s])]
    lift N to ℕ using hN0
    unfold Series.partial;simp[s]
    apply hL;simp
    use (Icc 0 N).map ge.symm.toEmbedding
    simp

abbrev AbsConvergent' {X:Type} (f: X → ℝ) : Prop := BddAbove ( (fun A ↦ ∑ x ∈ A, |f x|) '' .univ )

theorem AbsConvergent'.of_finite {X:Type} [Finite X] (f:X → ℝ) : AbsConvergent' f := by
  have _ := Fintype.ofFinite X
  simp [bddAbove_def]; use ∑ x, |f x|; intro A; apply Finset.sum_le_univ_sum_of_nonneg; simp
/-- Not in textbook, but should have been included. -/
-- Isn't that just  AbsConvergent.iff ??
theorem AbsConvergent'.of_countable {X:Type} (hX:CountablyInfinite X) {f:X → ℝ} :
  AbsConvergent' f ↔ AbsConvergent f := by
  constructor
  . intro hf; simp [bddAbove_def] at hf; choose L hL using hf
    have ⟨ g, hg ⟩ := hX.symm; refine ⟨ g, hg, ?_ ⟩
    unfold absConverges; rw [converges_of_nonneg_iff]
    . use L; intro N; by_cases hN: N ≥ 0
      . lift N to ℕ using hN
        set g':= Embedding.mk g hg.1
        convert hL (map g' (Icc 0 N))
        simp [Series.partial]; rfl
      convert hL ∅
      simp; apply partial_of_lt; grind
    simp [nonneg]
    intro n; by_cases h: n ≥ 0 <;> simp [h]
  intro hf; rwa [AbsConvergent.iff hX f] at hf

lemma AbsConvergent'.of_AbsConvergent {X:Type} {f: X → ℝ} (hf: AbsConvergent f) : AbsConvergent' f := by
  have hX : CountablyInfinite X := by
    choose g hg _ using hf
    set seq := Equiv.ofBijective g hg
    use seq.symm
    apply Equiv.bijective
  rwa[AbsConvergent'.of_countable hX]


/-- Lemma 8.2.5 / Exercise 8.2.2-/
theorem AbsConvergent'.countable_supp {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) :
  AtMostCountable { x | f x ≠ 0 } := by
    unfold AbsConvergent' at hf
    choose M hM using hf
    simp[mem_upperBounds] at hM
    set A : ℕ → Set X := fun n ↦ {x | 1 / ((n:ℝ) + 1) < |f x| }
    suffices hA : ∀ n, AtMostCountable (A n) from by
      have hres : AtMostCountable (⋃ i, A i) := by
        simp_rw[AtMostCountable.iff] at hA ⊢ 
        simp_rw[Set.countable_coe_iff] at hA ⊢ 
        rwa[Set.countable_iUnion_iff]
      convert hres
      ext x; simp
      constructor
      . intro hfx
        replace hfx : |f x| > 0 := by simpa
        choose n hn using exists_nat_one_div_lt hfx
        use n; simpa[A, add_comm] using hn
      . rintro ⟨n,hn⟩ 
        simp[A] at hn
        contrapose! hn
        simp[hn];linarith
    intro n; right
    by_contra hfin
    rw [not_finite_iff_infinite, Set.infinite_coe_iff] at hfin
    have hM_nonneg : 0 ≤ M := by simpa using hM ∅
    obtain ⟨k, hk⟩ := exists_nat_gt (M * ((n:ℝ) + 1))
    obtain ⟨t, htA, htcard⟩ := Set.Infinite.exists_subset_card_eq hfin k
    have hdenpos : 0 < (n:ℝ) + 1 := by positivity
    have htpos : t.Nonempty := by
      rw [← Finset.card_pos, htcard]
      exact Nat.cast_pos.mp (lt_of_le_of_lt (mul_nonneg hM_nonneg hdenpos.le) hk)
    have hconst_lt : (↑t.card:ℝ) * (1 / ((n:ℝ) + 1)) < ∑ x ∈ t, |f x| := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_lt_sum_of_nonempty htpos
      intro x hx
      exact htA hx
    have hM_lt : M < ∑ x ∈ t, |f x| := by
      have hkdiv : M < (k:ℝ) / ((n:ℝ) + 1) := (lt_div_iff₀ hdenpos).mpr hk
      rw [← htcard, div_eq_mul_inv] at hkdiv
      exact lt_trans hkdiv (by simpa [one_div] using hconst_lt)
    have hsum_le : ∑ x ∈ t, |f x| ≤ M := hM t
    linarith

/-- Compare with Mathlib's {name}`Summable.subtype`-/
theorem AbsConvergent'.subtype {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) (A: Set X) :
  AbsConvergent' (fun x:A ↦ f x) := by
  apply BddAbove.mono _ hf
  intro z hz; simp at *; choose A hA using hz
  use A.map (Embedding.subtype _); simp [hA]

/-- A generalized sum.  Note that this will give junk values if {name}`f` is not {name}`AbsConvergent'`. -/
noncomputable abbrev Sum' {X:Type} (f: X → ℝ) : ℝ := Sum (fun x : { x | f x ≠ 0 } ↦ f x)

/-- Not in textbook, but should have been included (the series laws are significantly harder
to establish without this) -/
theorem Sum'.of_finsupp {X:Type} {f:X → ℝ} {A: Finset X} (h: ∀ x ∉ A, f x = 0) : Sum' f = ∑ x ∈ A, f x := by
  unfold Sum'
  set E := { x | f x ≠ 0 }
  have hE : E ⊆ A := by intro _; simp [E]; grind
  have hfin : Finite E := Finite.Set.subset _ hE
  set E' := E.toFinite.toFinset
  rw [Sum.of_finite (fun x:E ↦ f x), ←E'.sum_subtype (by simp [E'])]
  replace hE : E' ⊆ A := by aesop
  apply sum_subset hE; aesop

/-- Not in textbook, but should have been included (the series laws are significantly harder
to establish without this) -/
theorem Sum'.of_countable_supp {X:Type} {f:X → ℝ} {A: Set X} (hA: CountablyInfinite A)
  (hfA : ∀ x ∉ A, f x = 0) (hconv: AbsConvergent' f):
  AbsConvergent' (fun x:A ↦ f x) ∧ Sum' f = Sum (fun x:A ↦ f x) := by
  -- We can adapt the proof of `AbsConvergent'.of_countable` to establish absolute convergence on A.
  have hconv' : AbsConvergent (fun x:A ↦ f x) :=
    (AbsConvergent'.of_countable hA).mp (hconv.subtype A)
  rw [AbsConvergent'.of_countable hA]
  refine ⟨ hconv', ?_ ⟩
  set E := { x | f x ≠ 0 }
  -- The main challenge here is to relate a sum on E with a sum on A.  First, we show containment.
  have hE : E ⊆ A := by intro _; simp [E]; by_contra!; aesop
  -- Now, we map A back to the natural numbers, thus identifying E with a subset E' of ℕ.
  choose g hg using hA.symm
  have hsum := Sum.eq hg (hconv'.comp hg)
  set E' := { n | ↑(g n) ∈ E }
  set ι : E' → E := fun ⟨ n, hn ⟩ ↦ ⟨ g n, by aesop ⟩
  have hι: Bijective ι := by
    split_ands
    . intro ⟨ _, _ ⟩ ⟨ _, _ ⟩ h; simp [ι, E', Subtype.val_inj] at *; exact hg.1 h
    . intro ⟨ x, hx ⟩; choose n hn using hg.2 ⟨ _, hE hx ⟩; use ⟨ n, by aesop ⟩; grind
  -- The cases of infinite and finite E' are handled separately.
  obtain hE' | hE' := Nat.atMostCountable_subset E'
  . --   use Nat.monotone_enum_of_infinite to enumerate E'
    --   show the partial sums of E' are a subsequence of the partial sums of A
    set hinf : Infinite E' := hE'.toInfinite
    choose a ha_bij ha_mono using (Nat.monotone_enum_of_infinite E').exists
    have : atTop.Tendsto (Nat.cast ∘ Subtype.val ∘ a: ℕ → ℤ) atTop := by
      apply tendsto_natCast_atTop_atTop.comp (StrictMono.tendsto_atTop _)
      intro _ _ hnm; simp [ha_mono hnm]
    apply tendsto_nhds_unique  _ (hsum.comp this)
    have hconv'' : AbsConvergent (fun x:E ↦ f x) := by
      rw [←AbsConvergent'.of_countable]
      . exact hconv.subtype E
      apply (CountablyInfinite.equiv _).mp hE'; use ι
    replace := Sum.eq (hι.comp ha_bij) (hconv''.comp (hι.comp ha_bij))
    convert this.comp tendsto_natCast_atTop_atTop using 1; ext N
    simp [Series.partial, ι]
    calc
      _ = ∑ x ∈ .image (Subtype.val ∘ a) (.Icc 0 N), f ↑(g x) := by
        symm; apply sum_subset
        . intro m hm; simp at hm ⊢; obtain ⟨ n, hn, rfl ⟩ := hm
          simp [ha_mono.monotone hn]
        intro x hx hx'; simp at hx hx'; contrapose! hx'
        choose n hn using (hι.comp ha_bij).2 ⟨ g x, hx' ⟩
        simp [ι, Subtype.val_inj] at hn
        apply hg.1 at hn; subst hn
        use n; simpa [ha_mono.le_iff_le] using hx
      _ = _ := by
        apply sum_image
        intro _ _ _ _ h; simp [Subtype.val_inj] at h; exact ha_bij.1 h
  -- When E' is finite, we show that all sufficiently large partial sums of A are equal to
  -- the sum of E'.
  let hEfin : Finite E := hι.finite_iff.mp hE'
  let hE'fintype : Fintype E' := .ofFinite _
  let hEfintype : Fintype E := .ofFinite _
  apply convergesTo_uniq _ hsum
  simp [Sum.of_finite, Series.convergesTo]
  apply tendsto_nhds_of_eventually_eq
  have hE'bound : BddAbove E' := Set.Finite.bddAbove hE'
  rw [bddAbove_def] at hE'bound; choose N hN using hE'bound
  rw [eventually_atTop]
  use N; intro N' hN'
  lift N' to ℕ using (LE.le.trans (by positivity) hN')
  simp [Series.partial] at hN' ⊢
  calc
    _ = ∑ n ∈ E', f (g n) := by
      symm; apply sum_subset
      . intro x hx; simp at *; linarith [hN _ hx]
      intro _ _ hx'; simpa [E',E] using hx'
    _ = ∑ n:E', f (g n) := by convert (sum_set_coe _).symm
    _ = ∑ n, f (ι n) := sum_congr rfl (by grind)
    _ = _ := hι.sum_comp (g := fun x ↦ f x)

/-- Connection with Mathlib's {name}`Summable` property. Some version of this might be suitable
    for Mathlib? -/
theorem AbsConvergent'.iff_Summable {X:Type} (f:X → ℝ) : AbsConvergent' f ↔ Summable f := by
  simp [←summable_abs_iff, AbsConvergent']
  simp [summable_iff_vanishing_norm]
  classical
  constructor
  . intro h ε hε
    set s := Set.range fun A ↦ ∑ x ∈ A, |f x|
    have hnon : s.Nonempty := by simp [s]; use 0, ∅; simp
    have : (sSup s)-ε < sSup s := by linarith
    simp [lt_csSup_iff h hnon,s] at this; choose S hS using this
    use S; intro T hT
    rw [abs_of_nonneg (by positivity)]
    have : ∑ x ∈ T, |f x| + ∑ x ∈ S, |f x| ≤ sSup s := by
      apply le_csSup h
      simp [s]; exact ⟨ T ∪ S, sum_union hT ⟩
    linarith
  intro h; choose S hS using h 1 (by norm_num)
  rw [bddAbove_def]
  use ∑ x ∈ S, |f x| + 1; simp; intro T
  calc
    _ = ∑ x ∈ (T ∩ S), |f x| + ∑ x ∈ (T \ S), |f x| := (sum_inter_add_sum_diff _ _ _).symm
    _ ≤ _ := by
      gcongr
      . exact inter_subset_right
      apply le_of_lt (lt_of_abs_lt (hS _ disjoint_sdiff_self_left))

/-- Maybe suitable for porting to Mathlib?-/
theorem Filter.Eventually.int_natCast_atTop (p: ℤ → Prop) :
  (∀ᶠ n in .atTop, p n) ↔ ∀ᶠ n:ℕ in .atTop, p ↑n := by
  refine ⟨ Eventually.natCast_atTop, ?_ ⟩
  simp [eventually_atTop]
  intro N hN; use N; intro n hn
  lift n to ℕ using (by omega)
  simp at hn; solve_by_elim

theorem Filter.Tendsto.int_natCast_atTop {R:Type} (f: ℤ → R) (l: Filter R) :
atTop.Tendsto f l ↔ atTop.Tendsto (f ∘ Nat.cast) l := by
  simp [tendsto_iff_eventually]
  peel with p h
  simp [←eventually_atTop]
  convert Eventually.int_natCast_atTop _

/-- Connection with Mathlib's {name}`tsum` (or {kw (of := «termΣ'_,_»)}`Σ'`) operation -/
theorem Sum'.eq_tsum {X:Type} (f:X → ℝ) (h: AbsConvergent' f) :
  Sum' f = ∑' x, f x := by
  set E := {x | f x ≠ 0}
  obtain hE | hE := h.countable_supp
  . simp [Sum']
    choose g hg using hE.symm
    have : ((f ∘ Subtype.val) ∘ g:Series).absConverges := by
      apply AbsConvergent.comp hg
      rw [←AbsConvergent'.of_countable hE]
      exact h.subtype E
    replace this := Sum.eq hg this
    convert convergesTo_uniq this _ using 1
    · replace : ∑' x, f x = ∑' n, f (g n) := calc
        _ = ∑' x:E, f x := by
          exact (tsum_subtype_eq_of_support_subset (fun x hx => hx)).symm
        _ = _ := (Equiv.tsum_eq (Equiv.ofBijective _ hg) _).symm
      rw [this]
      unfold convergesTo; rw [Filter.Tendsto.int_natCast_atTop]
      convert (Summable.tendsto_sum_tsum_nat ?_).comp (tendsto_add_atTop_nat 1) with n
      . ext N; simp [Series.partial, Nat.range_succ_eq_Icc_zero]
      rw [AbsConvergent'.iff_Summable] at h
      exact h.comp_injective (i := Subtype.val ∘ g) (Subtype.val_injective.comp hg.1)
  rw [of_finsupp (A := E.toFinite.toFinset)]; symm; apply tsum_eq_sum
  all_goals simp [E]

lemma permuted_abs {X:Type} {f:X → ℝ} {g h:ℕ → X} (hg : Bijective g) (hh : Bijective h)
    (hf : (f ∘ g:Series).absConverges) {L:ℝ} (hfL: (f ∘ g:Series).convergesTo L): (f ∘ h:Series).absConverges ∧ (f ∘ h:Series).convergesTo L:= by
  let e : ℕ → ℕ := g.invFun ∘ h
  have he : Bijective e := .comp
    ⟨(Function.rightInverse_invFun hg.surjective).injective,
      (Function.leftInverse_invFun hg.injective).surjective⟩ hh
  have hperm := Series.absConverges_of_permute hf he
  have hseries : (f ∘ h:Series) = (fun n ↦ (f ∘ g) (e n):Series) := by
    ext z
    · rfl
    · by_cases hz : z ≥ 0
      · simp [hz, e, Function.rightInverse_invFun hg.surjective (h z.toNat)]
      · simp [hz]
  rw [hseries]
  refine ⟨ hperm.1 , ?_ ⟩ 
  apply sum_of_converges at hfL
  rw[hperm.2] at hfL
  rw[← hfL]
  apply convergesTo_sum
  apply converges_of_absConverges hperm.1

/-- Proposition 8.2.6 (a) (Absolutely convergent series laws) / Exercise 8.2.3 -/
lemma Sum.add {X:Type}  {f₁ f₂:X → ℝ} (hf₁ : AbsConvergent f₁) (hf₂ : AbsConvergent f₂) (hf₁f₂ : AbsConvergent (f₁ + f₂)):
    Sum (f₁+f₂) = Sum f₁ + Sum f₂ := by
  choose g₁ hg₁ hs₁ using hf₁
  choose g₂ hg₂ hs₂ using hf₂
  choose g₁₂ hg₁₂ hs₁₂ using hf₁f₂
  have hsum₁ := Sum.eq hg₁ hs₁
  have hsum₂ := Sum.eq hg₂ hs₂
  have hsum₁₂ := Sum.eq hg₁₂ hs₁₂
  set s₁ := (f₁ ∘ g₁:Series)
  set s₂ := (f₂ ∘ g₂:Series)
  set s₂' := (f₂ ∘ g₁:Series)
  set s₁₂ := ((f₁ + f₂) ∘ g₁₂:Series)
  set s₁₂' := ((f₁ + f₂) ∘ g₁:Series)
  have ⟨hs₂', hsum₂'⟩  : s₂'.absConverges ∧ s₂'.convergesTo (Sum f₂) := by
    exact permuted_abs hg₂ hg₁ hs₂ hsum₂
  symm; apply Series.convergesTo_uniq (hsum₁.add hsum₂')
  have ⟨hs₁₂', hsum₁₂'⟩  : s₁₂'.absConverges ∧ s₁₂'.convergesTo (Sum (f₁ + f₂)) := by
    exact permuted_abs hg₁₂ hg₁ hs₁₂ hsum₁₂
  convert hsum₁₂'
  unfold s₁ s₂' s₁₂'
  rw[Series.add_coe]
  simp
theorem Sum'.add {X:Type} {f g:X → ℝ} (hf: AbsConvergent' f) (hg: AbsConvergent' g) :
  AbsConvergent' (f+g) ∧ Sum' (f + g) = Sum' f + Sum' g := by
    have hf' := hf
    choose U hU using hf'
    have hg' := hg
    choose V hV using hg'
    simp[mem_upperBounds] at hU hV
    have hconv : AbsConvergent' (f + g) := by
      use U+V
      simp[mem_upperBounds]
      intro A;specialize_all A
      calc 
        _ ≤ ∑ x ∈ A, (|f x| + |g x|) := by apply sum_le_sum; intro x hx; apply abs_add_le
        _ ≤ _ := by rw[sum_add_distrib];linarith
    refine ⟨hconv, ?_⟩ 
    set A := {x:X | f x ≠ 0 ∨  g x ≠ 0}
    have hA : AtMostCountable A := by
      have hfA := hf.countable_supp
      have hgA := hg.countable_supp
      rw[AtMostCountable.iff] at hfA hgA ⊢ 
      have := And.intro hfA hgA
      replace := Set.countable_union.mpr this
      convert this
    have hAf : ∀ x ∉ A, f x = 0 := by grind
    have hAg : ∀ x ∉ A, g x = 0 := by grind
    have hAs : ∀ x ∉ A, (f+g) x = 0 := by
      simp[A];intro _ _ _;linarith
    obtain hcont | hfin := hA
    . 
      have ⟨hsc,hs⟩  := (Sum'.of_countable_supp hcont hAs hconv)
      have ⟨hfc,hf⟩ := (Sum'.of_countable_supp hcont hAf hf)
      have ⟨hgc,hg⟩ := (Sum'.of_countable_supp hcont hAg hg)
      simp_all
      rw[AbsConvergent'.of_countable hcont] at hsc hfc hgc
      apply Sum.add hfc hgc hsc
    set E := A.toFinite.toFinset
    have hEf : ∀ x ∉ E, f x = 0 := by simpa[E]
    have hEg : ∀ x ∉ E, g x = 0 := by simpa[E]
    have hEs : ∀ x ∉ E, (f+g) x = 0 := by simpa[E]
    rw[Sum'.of_finsupp hEs]
    rw[Sum'.of_finsupp hEf]
    rw[Sum'.of_finsupp hEg]
    simp[sum_add_distrib]

/-- Proposition 8.2.6 (b) (Absolutely convergent series laws) / Exercise 8.2.3 -/
lemma Sum.smul {X:Type} {f:X → ℝ} (hf: AbsConvergent f) (c: ℝ) (hsmul: AbsConvergent (c • f) ) :
  Sum (c • f) = c * Sum f := by
    choose g hg hs using hf
    choose gsmul hgsmul hssmul using hsmul
    have hsum := Sum.eq hg hs
    have hsum_smul := Sum.eq hgsmul hssmul
    have hsum_smul' : ((c • f) ∘ g:Series).convergesTo (Sum (c • f)) := by
      have := permuted_abs hgsmul hg hssmul hsum_smul
      exact this.2
    apply convergesTo_uniq hsum_smul'
    have := hsum.smul (c:=c)
    rw[smul_coe] at this
    convert this
theorem Sum'.smul {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) (c: ℝ) :
  AbsConvergent' (c • f) ∧ Sum' (c • f) = c * Sum' f := by
    have hf' := hf
    choose U hU using hf'
    simp[mem_upperBounds] at hU
    have hconv' : AbsConvergent' (c • f) := by
      use |c| * U;simp[mem_upperBounds]
      peel hU with a hfU
      simp_rw[← smul_eq_mul]
      rw[← smul_sum]
      simp;apply mul_le_mul_of_nonneg_left hfU
      simp
    refine ⟨hconv', ?_⟩ 
    set A := {x:X | f x ≠ 0}
    have hA : AtMostCountable A := hf.countable_supp
    have hAf : ∀ x ∉ A, f x = 0 := by grind
    have hAs : ∀ x ∉ A, (c • f) x = 0 := by
      intro x; simp[A];tauto
    obtain hcont | hfin := hA
    . 
      have ⟨hfc,hf⟩ := (Sum'.of_countable_supp hcont hAf hf)
      have ⟨hfs,hs⟩ := (Sum'.of_countable_supp hcont hAs hconv')
      rw[hf,hs]
      rw[AbsConvergent'.of_countable hcont] at hfc hfs
      exact Sum.smul hfc c hfs
    set E := A.toFinite.toFinset
    have hEf : ∀ x ∉ E, f x = 0 := by simpa[E]
    have hEs : ∀ x ∉ E, (c • f) x = 0 := by simp[E];tauto
    rw[Sum'.of_finsupp hEs]
    rw[Sum'.of_finsupp hEf]
    simp only [Pi.smul_apply]
    rw[ ← smul_sum]
    simp

/-- This law is not explicitly stated in Proposition 8.2.6, but follows easily from parts (a) and (b).-/
theorem Sum'.sub {X:Type} {f g:X → ℝ} (hf: AbsConvergent' f) (hg: AbsConvergent' g) :
  AbsConvergent' (f-g) ∧ Sum' (f - g) = Sum' f - Sum' g := by
  convert add hf (smul hg (-1)).1 using 2
  . simp; abel
  . congr; simp; abel
  rw [(smul hg (-1)).2]; ring

/-- Proposition 8.2.6 (c) (Absolutely convergent series laws) / Exercise 8.2.3.  The first
    part of this proposition has been moved to {lean}`AbsConvergent'.subtype`. -/
theorem Sum'.of_disjoint_union {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) {X₁ X₂ : Set X} (hdisj: Disjoint X₁ X₂):
  Sum' (fun x: (X₁ ∪ X₂: Set X) ↦ f x) = Sum' (fun x : X₁ ↦ f x) + Sum' (fun x : X₂ ↦ f x) := by
  classical
  set U : Set X := X₁ ∪ X₂
  set A : Set U := {u | (u : X) ∈ X₁}
  have hU := hf.subtype U
  have hX₁ := hf.subtype X₁
  have hX₂ := hf.subtype X₂
  rw [Sum'.eq_tsum _ hU, Sum'.eq_tsum _ hX₁, Sum'.eq_tsum _ hX₂]
  rw [AbsConvergent'.iff_Summable] at hU
  let e₁ : A ≃ X₁ :=
    { toFun := fun a ↦ ⟨a, a.2⟩
      invFun := fun x ↦ ⟨⟨x, Or.inl x.2⟩, x.2⟩
      left_inv := by intro a; exact Subtype.ext rfl
      right_inv := by intro x; exact Subtype.ext rfl }
  let e₂ : ↥((A : Set U)ᶜ) ≃ X₂ :=
    { toFun := fun a ↦ ⟨a.1, by
        rcases a.1.2 with hx₁ | hx₂
        · exact False.elim (a.2 (by simpa [A] using hx₁))
        · exact hx₂⟩
      invFun := fun x ↦ ⟨⟨x, Or.inr x.2⟩, by
        simp only [Set.mem_compl_iff]
        intro hx₁
        exact (Set.disjoint_left.1 hdisj hx₁ x.2)⟩
      left_inv := by intro a; exact Subtype.ext rfl
      right_inv := by intro x; exact Subtype.ext rfl }
  have he₁ : (∑' a : A, f a) = ∑' x : X₁, f x := by
    simpa [e₁] using e₁.tsum_eq (fun x : X₁ ↦ f x)
  have he₂ : (∑' a : ↥((A : Set U)ᶜ), f a) = ∑' x : X₂, f x := by
    simpa [e₂] using e₂.tsum_eq (fun x : X₂ ↦ f x)
  calc
    ∑' x : U, f x = (∑' a : A, f a) + ∑' a : ↥((A : Set U)ᶜ), f a :=
      (hU.tsum_subtype_add_tsum_subtype_compl A).symm
    _ = _ := by rw [he₁, he₂]
/-- This technical claim, the analogue of {name}`tsum_univ`, is required due to the way Mathlib handles
    sets.-/
theorem Sum'.of_univ {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) :
  Sum' (fun x: (.univ : Set X) ↦ f x) = Sum' f := by
  have hU := hf.subtype (Set.univ : Set X)
  rw [Sum'.eq_tsum _ hU, Sum'.eq_tsum _ hf]
  exact (Equiv.Set.univ X).tsum_eq f

theorem Sum'.of_comp {X Y:Type} {f:X → ℝ} (hf: AbsConvergent' f) {φ: Y → X}
  (hφ: Function.Bijective φ) :
  AbsConvergent' (f ∘ φ) ∧ Sum' f = Sum' (f ∘ φ) := by
    set eXY : Y ≃ X := Equiv.ofBijective _  hφ 
    have heXY (y) : φ y = eXY y := by simp[eXY]
    have hconv' : AbsConvergent' (f ∘ φ) := by
      choose M hM using hf
      use M; simp[mem_upperBounds] at hM ⊢ 
      intro A
      set φ' := Embedding.mk _ hφ.1
      specialize hM (A.map φ')
      convert hM
      exact Eq.symm (sum_map A φ' fun x ↦ |f x|)
    refine ⟨hconv', ?_⟩ 
    rw[Sum'.eq_tsum _ hf, Sum'.eq_tsum _ hconv']
    set esp : support f ≃ support (f ∘ φ) :={
      toFun := fun ⟨x,hx⟩ ↦ ⟨ eXY.symm x  , by simpa[heXY] using hx ⟩ 
      invFun := fun ⟨y,hy⟩ ↦ ⟨eXY y, by simpa[← heXY] using hy ⟩  
      left_inv  := by
        rintro ⟨x,hx⟩; simp 
      right_inv := by rintro ⟨y,hy⟩; simp
    }
    apply Equiv.tsum_eq_tsum_of_support esp
    . rintro ⟨x,hx⟩
      simp;congr
      simp[esp,heXY]

/-- Lemma 8.2.7 / Exercise 8.2.4 -/
lemma divergent_parts_of_conditional_convergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha' : ¬ (a:Series).absConverges) : 
  ¬ AbsConvergent' (fun n : {n | a n ≥ 0} ↦ a n) ∧ ¬ AbsConvergent' (fun n : {n | a n < 0} ↦ a n) := by
  classical
  -- A summable function also converges in the textbook's ordered-series notation.
  have hconv {b : ℕ → ℝ} (hb : Summable b) : (b : Series).converges := by
    refine ⟨∑' n, b n, ?_⟩
    unfold Series.convergesTo
    rw [Filter.Tendsto.int_natCast_atTop]
    convert hb.tendsto_sum_tsum_nat.comp (tendsto_add_atTop_nat 1) using 1
    ext N
    simp [Series.partial, Finset.Icc_eq_cast, Nat.range_succ_eq_Icc_zero]
  have habs : (a : Series).abs = (fun n ↦ |a n| : Series) := by
    ext n
    · rfl
    · by_cases hn : n ≥ 0 <;> simp [hn]
  constructor
  · intro hpos
    let p : ℕ → ℝ := {n | 0 ≤ a n}.indicator a
    have hp : (p : Series).converges := hconv
      (summable_subtype_iff_indicator.mp ((AbsConvergent'.iff_Summable _).mp hpos))
    -- |aₙ| = 2 pₙ - aₙ, where p retains precisely the nonnegative terms.
    have hid : (fun n ↦ |a n|) = (fun n ↦ p n + p n - a n) := by
      funext n
      by_cases hn : 0 ≤ a n
      · simp [p, hn, abs_of_nonneg hn]
      · simp [p, hn, abs_of_neg (lt_of_not_ge hn)]
    apply ha'
    unfold Series.absConverges
    rw [habs, hid]
    have h := (Series.sub (Series.add hp hp).1 ha).1
    rwa [Series.add_coe, Series.sub_coe (fun n ↦ p n + p n) a] at h
  · intro hneg
    let q : ℕ → ℝ := {n | a n < 0}.indicator a
    have hq : (q : Series).converges := hconv
      (summable_subtype_iff_indicator.mp ((AbsConvergent'.iff_Summable _).mp hneg))
    -- |aₙ| = aₙ - 2 qₙ, where q retains precisely the negative terms.
    have hid : (fun n ↦ |a n|) = (fun n ↦ a n - (q n + q n)) := by
      funext n
      by_cases hn : a n < 0
      · simp [q, hn, abs_of_neg hn]
      · simp [q, hn, abs_of_nonneg (le_of_not_gt hn)]
    apply ha'
    unfold Series.absConverges
    rw [habs, hid]
    have h := (Series.sub ha (Series.add hq hq).1).1
    rwa [Series.add_coe, Series.sub_coe a (fun n ↦ q n + q n)] at h

theorem divergent_parts_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges) :
  ¬ AbsConvergent (fun n : {n | a n ≥ 0} ↦ a n) ∧ ¬ AbsConvergent (fun n : {n | a n < 0} ↦ a n)
  := by 
  choose h1 h2 using divergent_parts_of_conditional_convergent ha ha'
  constructor
  . contrapose! h1; exact AbsConvergent'.of_AbsConvergent h1
  contrapose! h2; apply AbsConvergent'.of_AbsConvergent h2

lemma Nat.exists_mem_range_of_eventually_min {A : Set ℕ} {u : ℕ → ℕ}
    (hu : Injective u) (K : ℕ)
    (hmin : ∀ j > K, u j = Nat.min {n ∈ A | ∀ i : Fin j, n ≠ u i})
    {x : ℕ} (hx : x ∈ A) : ∃ j, u j = x := by
  by_contra! hxseen
  have htail : ∀ j ∈ Set.Ici (K + 1), u j ≤ x := by
    intro j hj
    have hjK : j > K := by simpa using hj
    rw [hmin j hjK]
    have hxmem : x ∈ {n ∈ A | ∀ i : Fin j, n ≠ u i} := by
      simp only [Set.mem_setOf_eq]
      exact ⟨hx, fun i ↦ (hxseen i).symm⟩
    exact (Nat.min_spec ⟨x, hxmem⟩).2 x hxmem
  have hinj : Set.InjOn u (Set.Ici (K + 1)) := fun _ _ _ _ h ↦ hu h
  have hinfinite : (u '' Set.Ici (K + 1)).Infinite :=
    (Set.infinite_image_iff hinj).mpr (Set.Ici_infinite _)
  have hfinite : (u '' Set.Ici (K + 1)).Finite :=
    (Set.finite_Iic x).subset (by
      rintro y ⟨j, hj, rfl⟩
      simpa using htail j hj)
  exact hinfinite hfinite

/-- A finite set of elements which all occur in a sequence occurs before one common index. -/
lemma Finset.exists_bound_of_mem_range {α : Type} {u : ℕ → α} (T : Finset α)
    (hseen : ∀ x ∈ T, ∃ j, u j = x) :
    ∃ J, ∀ x ∈ T, ∃ i : Fin J, u i = x := by
  by_cases hT : T = ∅
  · refine ⟨0, ?_⟩
    simp [hT]
  choose j hj using hseen
  let U : Finset {x // x ∈ T} := T.attach
  have hU : U.Nonempty := by
    simpa [U] using Finset.nonempty_iff_ne_empty.mpr hT
  have himage : (U.image fun x ↦ j x.1 x.2).Nonempty := hU.image _
  let J := (U.image fun x ↦ j x.1 x.2).max' himage + 1
  refine ⟨J, ?_⟩
  intro x hx
  refine ⟨⟨j x hx, by
    have hxU : (⟨x, hx⟩ : {x // x ∈ T}) ∈ U := by simp [U]
    have hjmem : j x hx ∈ U.image (fun x ↦ j x.1 x.2) :=
      Finset.mem_image.2 ⟨⟨x, hx⟩, hxU, rfl⟩
    exact Nat.lt_succ_of_le (Finset.le_max' _ _ hjmem)⟩, hj x hx⟩

lemma Finset.sum_le_sum_of_seen {u : ℕ → ℕ} (hu : Injective u) (T : Finset ℕ)
    {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hseen : ∀ x ∈ T, ∃ j, u j = x) :
    ∃ J, ∑ x ∈ T, f x ≤ ∑ i : Fin J, f (u i) := by
  obtain ⟨J, hJ⟩ := Finset.exists_bound_of_mem_range T hseen
  let e : Fin J ↪ ℕ := ⟨fun i ↦ u i, fun i j hij ↦ by
    apply Fin.ext
    exact hu hij⟩
  refine ⟨J, ?_⟩
  calc
    ∑ x ∈ T, f x ≤ ∑ x ∈ (Finset.univ.map e), f x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        obtain ⟨i, hi⟩ := hJ x hx
        exact Finset.mem_map.mpr ⟨i, by simp, hi⟩
      · intro x _ _
        exact hf x
    _ = ∑ i : Fin J, f (u i) := by
      simp [e]

lemma abs_partial_bound_of_eventually_neg {a : ℕ → ℝ} {u : ℕ → ℕ} {K : ℕ} {L : ℝ}
    (hpartial_ge : ∀ {j : ℕ}, K < j → L ≤ ∑ i : Fin j, a (u i))
    (htail_neg : ∀ {j : ℕ}, K < j → a (u j) < 0) :
    ∃ M, ∀ J, ∑ i : Fin J, |a (u i)| ≤ M := by
  let P : ℕ → ℝ := fun J ↦ ∑ i ∈ Finset.range J, a (u i)
  let Q : ℕ → ℝ := fun J ↦ ∑ i ∈ Finset.range J, |a (u i)|
  let M : ℝ := Q (K + 1) + P (K + 1) - L
  have hP_eq (J : ℕ) : (∑ i : Fin J, a (u i)) = P J :=
    Fin.sum_univ_eq_sum_range (fun i ↦ a (u i)) J
  have hQ_eq (J : ℕ) : (∑ i : Fin J, |a (u i)|) = Q J :=
    Fin.sum_univ_eq_sum_range (fun i ↦ |a (u i)|) J
  have hpartial_geP {j : ℕ} (hj : K < j) : L ≤ P j := by
    simpa [hP_eq j] using hpartial_ge hj
  have hQ_formula : ∀ J ≥ K + 1, Q J = Q (K + 1) + P (K + 1) - P J := by
    intro J hJ
    exact Nat.le_induction (m := K + 1) (n := J)
      (by simp [P, Q])
      (by
        intro J hKJ hJformula
        have hJgt : K < J := by omega
        have hneg : a (u J) < 0 := htail_neg hJgt
        simp [P, Q, Finset.sum_range_succ, hJformula, abs_of_neg hneg]
        ring)
      hJ
  have hQ_bound (J : ℕ) : Q J ≤ M := by
    by_cases hJ : J ≤ K + 1
    · calc
        Q J ≤ Q (K + 1) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp only [Finset.mem_range] at hx ⊢
            omega
          · intro x _ _
            exact abs_nonneg _
        _ ≤ M := by
          have hge : L ≤ P (K + 1) := hpartial_geP (by omega)
          simp [M]
          linarith
    · have hJ' : K + 1 ≤ J := by omega
      rw [hQ_formula J hJ']
      have hge : L ≤ P J := hpartial_geP (by omega)
      simp [M]
      linarith
  exact ⟨M, fun J ↦ (hQ_eq J).trans_le (hQ_bound J)⟩

lemma abs_partial_bound_of_eventually_nonneg {a : ℕ → ℝ} {u : ℕ → ℕ} {K : ℕ} {L : ℝ}
    (hpartial_lt : ∀ {j : ℕ}, K < j → ∑ i : Fin j, a (u i) < L)
    (htail_nonneg : ∀ {j : ℕ}, K < j → 0 ≤ a (u j)) :
    ∃ M, ∀ J, ∑ i : Fin J, |a (u i)| ≤ M := by
  let P : ℕ → ℝ := fun J ↦ ∑ i ∈ Finset.range J, a (u i)
  let Q : ℕ → ℝ := fun J ↦ ∑ i ∈ Finset.range J, |a (u i)|
  let M : ℝ := Q (K + 1) + L - P (K + 1)
  have hP_eq (J : ℕ) : (∑ i : Fin J, a (u i)) = P J :=
    Fin.sum_univ_eq_sum_range (fun i ↦ a (u i)) J
  have hQ_eq (J : ℕ) : (∑ i : Fin J, |a (u i)|) = Q J :=
    Fin.sum_univ_eq_sum_range (fun i ↦ |a (u i)|) J
  have hpartial_ltP {j : ℕ} (hj : K < j) : P j < L := by
    simpa [hP_eq j] using hpartial_lt hj
  have hQ_formula : ∀ J ≥ K + 1, Q J = Q (K + 1) + P J - P (K + 1) := by
    intro J hJ
    exact Nat.le_induction (m := K + 1) (n := J)
      (by simp [P, Q])
      (by
        intro J hKJ hJformula
        have hJgt : K < J := by omega
        have hnonneg : 0 ≤ a (u J) := htail_nonneg hJgt
        simp [P, Q, Finset.sum_range_succ, hJformula, abs_of_nonneg hnonneg]
        ring)
      hJ
  have hQ_bound (J : ℕ) : Q J ≤ M := by
    by_cases hJ : J ≤ K + 1
    · calc
        Q J ≤ Q (K + 1) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp only [Finset.mem_range] at hx ⊢
            omega
          · intro x _ _
            exact abs_nonneg _
        _ ≤ M := by
          have hlt : P (K + 1) < L := hpartial_ltP (by omega)
          simp [M]
          linarith
    · have hJ' : K + 1 ≤ J := by omega
      rw [hQ_formula J hJ']
      have hlt : P J < L := hpartial_ltP (by omega)
      simp [M]
      linarith
  exact ⟨M, fun J ↦ (hQ_eq J).trans_le (hQ_bound J)⟩

lemma AbsConvergent'.of_seen_partial_abs_bound {A : Set ℕ} {a : ℕ → ℝ} {u : ℕ → ℕ}
    (hu : Injective u) (g : ℕ → A) (hg : Bijective g)
    (hseen : ∀ x ∈ A, ∃ j, u j = x)
    (hbound : ∃ M, ∀ J, ∑ i : Fin J, |a (u i)| ≤ M) :
  AbsConvergent' (fun n : A ↦ a n) := by
  have hA_count : CountablyInfinite A := by
    let e := Equiv.ofBijective g hg
    use e.symm
    exact e.symm.bijective
  rw [AbsConvergent'.of_countable hA_count]
  use g
  simp [hg]
  unfold absConverges
  rw [converges_of_nonneg_iff (by simp [nonneg]; intro n; split_ifs <;> simp)]
  obtain ⟨M, hM⟩ := hbound
  use M
  intro N
  by_cases hN : N ≥ 0
  · lift N to ℕ using hN
    let T : Finset ℕ := (Finset.range (N + 1)).image (fun i ↦ (g i : ℕ))
    have hseen_T : ∀ x ∈ T, ∃ j, u j = x := by
      intro x hx
      simp [T] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact hseen (g i) (g i).2
    obtain ⟨J, hJ⟩ := Finset.sum_le_sum_of_seen hu T (fun n ↦ abs_nonneg (a n)) hseen_T
    calc
      ((fun n ↦ a ↑(g n) : Series).abs).partial (N : ℤ)
          = ∑ x ∈ T, |a x| := by
        simp [Series.partial, Finset.Icc_eq_cast, T]
        have hIcc : Finset.Icc 0 N = Finset.range (N + 1) := by
          ext x
          simp
        rw [hIcc]
        rw [Finset.sum_image]
        intro x hx y hy hxy
        exact hg.injective (Subtype.ext hxy)
      _ ≤ ∑ i : Fin J, |a (u i)| := hJ
      _ ≤ M := hM J
  · calc
      ((fun n ↦ a ↑(g n) : Series).abs).partial N = 0 := by
        apply Series.partial_of_lt
        simpa using hN
      _ ≤ M := by
        have hM0 := hM 0
        simp at hM0
        exact hM0

/-- Theorem 8.2.8 (Riemann rearrangement theorem) / Exercise 8.2.5 -/
theorem permute_convergesTo_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges) (L:ℝ) :
  ∃ f : ℕ → ℕ, Bijective f ∧ (a ∘ f:Series).convergesTo L := by
  -- This proof is written to follow the structure of the original text.
  choose h1 h2 using divergent_parts_of_conditional_convergent ha ha'
  set A_plus := { n | a n ≥ 0 }
  set A_minus := {n | a n < 0 }
  have hunion : A_plus ∪ A_minus = .univ := by
    ext; simp [A_plus, A_minus]; grind
  let F : (n : ℕ) → ((m : ℕ) → m < n → ℕ) → ℕ :=
    fun j n' ↦ if ∑ i:Fin j, a (n' i (by simp)) < L then
      Nat.min { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i (by simp) }
    else
      Nat.min { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i (by simp) }
  let n' : ℕ → ℕ := Nat.strongRec F
  have hn' (j:ℕ) : n' j = if ∑ i:Fin j, a (n' i) < L then
      Nat.min { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i }
    else
      Nat.min { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i }
    := Nat.strongRec.eq_def _ j
  have hA_plus_inf : Infinite A_plus := by
    contrapose! h1
    apply AbsConvergent'.of_finite
  have hA_minus_inf : Infinite A_minus := by
    contrapose! h2
    apply AbsConvergent'.of_finite
  have infinite_without_seen (A : Set ℕ) (hA : Infinite A) (j : ℕ) :
      Infinite {n ∈ A | ∀ i : Fin j, n ≠ n' i} := by
    rw [Set.infinite_coe_iff] at hA ⊢
    have hseen : Set.Finite {n | ∃ i : Fin j, n' i = n} := by
      simpa using Set.finite_range (fun i : Fin j ↦ n' i)
    have hdiff : (A \ {n | ∃ i : Fin j, n' i = n}).Infinite := hA.diff hseen
    convert hdiff using 1
    ext n
    simp [eq_comm]
  have hn'_plus_inf (j:ℕ) : Infinite { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i } :=
    infinite_without_seen A_plus hA_plus_inf j
  have hn'_minus_inf (j:ℕ) : Infinite { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i } :=
    infinite_without_seen A_minus hA_minus_inf j
  have hn'_ne_seen {x1 x2:ℕ } (hlt : x1 < x2) : n' x1 ≠ n' x2 := by
    simp[hn' x2]
    split_ifs with hL
    map_tacs [set S := {n | n ∈ A_plus ∧ ∀ (i : Fin x2), ¬n = n' ↑i}; set S := {n | n ∈ A_minus ∧ ∀ (i : Fin x2), ¬n = n' ↑i}]
    all_goals
      intro heq
      observe hnone : S.Nonempty 
      have hmem : n' x1 ∈ S := by
        rw[heq]
        apply (Nat.min_spec hnone).1
      simp[S] at hmem
      have := hmem.2 ⟨x1, hlt⟩ 
      simp at this
  have hn'_inj : Injective n' := by
    intro x1 x2 heq
    contrapose! heq with hne
    obtain hlt|hlt := hne.gt_or_lt
    <;> have := hn'_ne_seen hlt
    . symm; assumption
    assumption
  obtain ⟨ a_plus, ha_plus_bij, ha_plus_mono ⟩ := (Nat.monotone_enum_of_infinite A_plus).exists
  obtain ⟨ a_minus, ha_minus_bij, ha_minus_mono ⟩ := (Nat.monotone_enum_of_infinite A_minus).exists
  have h_case_I : Infinite { j | ∑ i:Fin j, a (n' i) < L } := by
    contrapose! h2
    have hSbdd : BddAbove { j | ∑ i:Fin j, a (n' i) < L } := Set.Finite.bddAbove h2
    rw [bddAbove_def] at hSbdd
    obtain ⟨K, hK⟩ := hSbdd
    have hpartial_ge {j : ℕ} (hj : K < j) : L ≤ ∑ i : Fin j, a (n' i) := by
      by_contra! hjL
      exact (not_lt_of_ge (hK j hjL)) hj
    have hminus_choice (j : ℕ) (hj : K < j) :
        n' j = Nat.min { n ∈ A_minus | ∀ i : Fin j, n ≠ n' i } := by
      rw [hn' j]
      have hjL : ¬ ∑ i : Fin j, a (n' i) < L := not_lt.mpr (hpartial_ge hj)
      simp [hjL]
    have hminus_seen {x : ℕ} (hx : x ∈ A_minus) : ∃ j, n' j = x :=
      Nat.exists_mem_range_of_eventually_min hn'_inj K hminus_choice hx
    have htail_minus {j : ℕ} (hj : K < j) : n' j ∈ A_minus := by
      rw [hminus_choice j hj]
      have hmin := Nat.min_spec (by
        observe hnone : ({ n ∈ A_minus | ∀ i : Fin j, n ≠ n' i } : Set ℕ).Nonempty
        exact hnone)
      exact hmin.1.1
    have hbound : ∃ M, ∀ J, ∑ i : Fin J, |a (n' i)| ≤ M :=
      abs_partial_bound_of_eventually_neg (a := a) (u := n') (K := K) (L := L)
        hpartial_ge (by
          intro j hj
          simpa [A_minus] using htail_minus hj)
    exact AbsConvergent'.of_seen_partial_abs_bound hn'_inj a_minus ha_minus_bij
      (fun x hx ↦ hminus_seen hx) hbound
  have h_case_II : Infinite { j | ∑ i:Fin j, a (n' i) ≥ L } := by
    contrapose! h1
    have hSbdd : BddAbove { j | ∑ i:Fin j, a (n' i) ≥ L } := Set.Finite.bddAbove h1
    rw [bddAbove_def] at hSbdd
    obtain ⟨K, hK⟩ := hSbdd
    have hpartial_lt {j : ℕ} (hj : K < j) : ∑ i : Fin j, a (n' i) < L := by
      by_contra! hjL
      exact (not_lt_of_ge (hK j hjL)) hj
    have hplus_choice (j : ℕ) (hj : K < j) :
        n' j = Nat.min { n ∈ A_plus | ∀ i : Fin j, n ≠ n' i } := by
      rw [hn' j]
      have hjL : ∑ i : Fin j, a (n' i) < L := hpartial_lt hj
      simp [hjL]
    have hplus_seen {x : ℕ} (hx : x ∈ A_plus) : ∃ j, n' j = x :=
      Nat.exists_mem_range_of_eventually_min hn'_inj K hplus_choice hx
    have htail_plus {j : ℕ} (hj : K < j) : n' j ∈ A_plus := by
      rw [hplus_choice j hj]
      have hmin := Nat.min_spec (by
        observe hnone : ({ n ∈ A_plus | ∀ i : Fin j, n ≠ n' i } : Set ℕ).Nonempty
        exact hnone)
      exact hmin.1.1
    have hbound : ∃ M, ∀ J, ∑ i : Fin J, |a (n' i)| ≤ M :=
      abs_partial_bound_of_eventually_nonneg (a := a) (u := n') (K := K) (L := L)
        hpartial_lt (by
          intro j hj
          simpa [A_plus] using htail_plus hj)
    exact AbsConvergent'.of_seen_partial_abs_bound hn'_inj a_plus ha_plus_bij
      (fun x hx ↦ hplus_seen hx) hbound
  have hn'_surj : Surjective n' := by
    have hplus_seen {x : ℕ} (hx : x ∈ A_plus) : ∃ j, n' j = x := by
      by_contra! hxseen
      have htail : ∀ j ∈ {j | ∑ i : Fin j, a (n' i) < L}, n' j ≤ x := by
        intro j hj
        change ∑ i : Fin j, a (n' i) < L at hj
        rw [hn' j]
        simp only [if_pos hj]
        have hxmem : x ∈ {n ∈ A_plus | ∀ i : Fin j, n ≠ n' i} := by
          exact ⟨hx, fun i ↦ (hxseen i).symm⟩
        exact (Nat.min_spec ⟨x, hxmem⟩).2 x hxmem
      have hinj : Set.InjOn n' {j | ∑ i : Fin j, a (n' i) < L} :=
        fun _ _ _ _ h ↦ hn'_inj h
      have hinfinite : (n' '' {j | ∑ i : Fin j, a (n' i) < L}).Infinite :=
        (Set.infinite_image_iff hinj).mpr (Set.infinite_coe_iff.mp h_case_I)
      have hfinite : (n' '' {j | ∑ i : Fin j, a (n' i) < L}).Finite :=
        (Set.finite_Iic x).subset (by
          rintro y ⟨j, hj, rfl⟩
          exact htail j hj)
      exact hinfinite hfinite
    have hminus_seen {x : ℕ} (hx : x ∈ A_minus) : ∃ j, n' j = x := by
      by_contra! hxseen
      have htail : ∀ j ∈ {j | ∑ i : Fin j, a (n' i) ≥ L}, n' j ≤ x := by
        intro j hj
        change ∑ i : Fin j, a (n' i) ≥ L at hj
        rw [hn' j]
        simp only [if_neg (not_lt.mpr hj)]
        have hxmem : x ∈ {n ∈ A_minus | ∀ i : Fin j, n ≠ n' i} := by
          exact ⟨hx, fun i ↦ (hxseen i).symm⟩
        exact (Nat.min_spec ⟨x, hxmem⟩).2 x hxmem
      have hinj : Set.InjOn n' {j | ∑ i : Fin j, a (n' i) ≥ L} :=
        fun _ _ _ _ h ↦ hn'_inj h
      have hinfinite : (n' '' {j | ∑ i : Fin j, a (n' i) ≥ L}).Infinite :=
        (Set.infinite_image_iff hinj).mpr (Set.infinite_coe_iff.mp h_case_II)
      have hfinite : (n' '' {j | ∑ i : Fin j, a (n' i) ≥ L}).Finite :=
        (Set.finite_Iic x).subset (by
          rintro y ⟨j, hj, rfl⟩
          exact htail j hj)
      exact hinfinite hfinite
    intro x
    have hx : x ∈ A_plus ∪ A_minus := by
      rw [hunion]
      exact Set.mem_univ x
    rcases hx with hx | hx
    · exact hplus_seen hx
    · exact hminus_seen hx
  have hconv : atTop.Tendsto (a ∘ n') (nhds 0) := by
    have : atTop.Tendsto n' atTop := by
      exact Injective.nat_tendsto_atTop hn'_inj
    have ha0 : atTop.Tendsto a (nhds 0) := by
      rw[Metric.tendsto_atTop] 
      rw[converges_iff_tail_decay] at ha
      intro ε hε 
      specialize ha (ε/2) (half_pos hε)
      simp at ha
      choose N hN hdecay using ha
      lift N to ℕ using hN
      use N;intro n hn
      specialize hdecay n (by simp[hn]) n (by simp[hn])
      simp at hdecay
      simp
      linarith
    apply ha0.comp this
  have hsum : (a ∘ n':Series).convergesTo L := by
    let P : ℕ → ℝ := fun j ↦ ∑ i : Fin j, a (n' i)
    have hPstep (j : ℕ) : P (j + 1) = P j + a (n' j) := by
      simp only [P]
      rw [Fin.sum_univ_castSucc]
      simp
    have hplus {j : ℕ} (hj : P j < L) : 0 ≤ a (n' j) := by
      rw [hn' j, if_pos hj]
      have hnone : ({n ∈ A_plus | ∀ i : Fin j, n ≠ n' i} : Set ℕ).Nonempty := by
        exact (Set.infinite_coe_iff.mp (hn'_plus_inf j)).nonempty
      simpa [A_plus] using (Nat.min_spec hnone).1.1
    have hminus {j : ℕ} (hj : L ≤ P j) : a (n' j) < 0 := by
      rw [hn' j, if_neg (not_lt.mpr hj)]
      have hnone : ({n ∈ A_minus | ∀ i : Fin j, n ≠ n' i} : Set ℕ).Nonempty := by
        exact (Set.infinite_coe_iff.mp (hn'_minus_inf j)).nonempty
      simpa [A_minus] using (Nat.min_spec hnone).1.1
    have hPconv : atTop.Tendsto P (nhds L) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hconv) ε hε
      have hsmall {j : ℕ} (hj : K ≤ j) : |a (n' j)| < ε := by
        simpa [Real.dist_eq] using hK j hj
      obtain ⟨p, hp, hKp⟩ := (Set.infinite_coe_iff.mp h_case_I).exists_gt K
      change P p < L at hp
      obtain ⟨q, hq, hpq⟩ := (Set.infinite_coe_iff.mp h_case_II).exists_gt p
      change L ≤ P q at hq
      have hcross : ∃ j, p < j ∧ L ≤ P j := ⟨q, hpq, hq⟩
      let t := Nat.find hcross
      have ht : p < t ∧ L ≤ P t := Nat.find_spec hcross
      have hprev : P (t - 1) < L := by
        by_contra! hprev
        by_cases htp : t - 1 = p
        · rw [htp] at hprev
          exact (not_le_of_gt hp) hprev
        · have hpt : p < t - 1 := by omega
          exact (Nat.find_min hcross (by omega)) ⟨hpt, hprev⟩
      have htK : K ≤ t - 1 := by omega
      have hinit : |P t - L| < ε := by
        rw [show t = (t - 1) + 1 by omega, hPstep]
        rw [abs_lt]
        have hsmall' := (abs_lt.mp (hsmall htK))
        have htL : L ≤ P (t - 1) + a (n' (t - 1)) := by
          calc
            L ≤ P t := ht.2
            _ = P (t - 1) + a (n' (t - 1)) := by
              rw [← hPstep]
              congr
              omega
        constructor <;> linarith
      use t
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => exact hinit
      | succ j hj hind =>
          rw [hPstep]
          change |P j + a (n' j) - L| < ε
          have hsmallj := hsmall (by omega : K ≤ j)
          have hsmallj' := abs_lt.mp hsmallj
          have hind' := abs_lt.mp hind
          rw [abs_lt]
          rcases lt_or_ge (P j) L with hbelow | habove
          · have hnonneg := hplus hbelow
            constructor <;> linarith [le_abs_self (a (n' j))]
          · have hneg := hminus habove
            constructor <;> linarith
    unfold Series.convergesTo
    rw [Filter.Tendsto.int_natCast_atTop]
    convert hPconv.comp (tendsto_add_atTop_nat 1) using 1
    ext N
    change (a ∘ n' : Series).partial (N : ℤ) = P (N + 1)
    simp [P, Series.partial, Finset.Icc_eq_cast]
    have hIcc : Finset.Icc 0 N = Finset.range (N + 1) := by
      ext x
      simp
    rw [hIcc, ← Fin.sum_univ_eq_sum_range]

  use n'
  refine ⟨ ⟨ hn'_inj, hn'_surj ⟩, ?_ ⟩; convert hsum

/-- Exercise 8.2.6 -/
theorem permute_diverges_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges)  :
  ∃ f : ℕ → ℕ,  Bijective f ∧ atTop.Tendsto (fun N ↦ ((a ∘ f:Series).partial N : EReal)) (nhds ⊤) := by
  obtain ⟨h1, h2⟩ := divergent_parts_of_conditional_convergent ha ha'
  let A_plus := {n | 0 ≤ a n}
  let A_minus := {n | a n < 0}
  have hA_plus_inf : Infinite A_plus := by
    contrapose! h1
    exact AbsConvergent'.of_finite _
  have hA_minus_inf : Infinite A_minus := by
    contrapose! h2
    exact AbsConvergent'.of_finite _
  -- The target is one more than the number of negative terms already used.
  let F : (j : ℕ) → ((i : ℕ) → i < j → ℕ) → ℕ := fun j u ↦
    if (∑ i : Fin j, a (u i i.2)) <
        ((∑ i : Fin j, if a (u i i.2) < 0 then 1 else 0 : ℕ) : ℝ) + 1 then
      Nat.min {n ∈ A_plus | ∀ i : Fin j, n ≠ u i i.2}
    else Nat.min {n ∈ A_minus | ∀ i : Fin j, n ≠ u i i.2}
  let u : ℕ → ℕ := Nat.strongRec F
  let P : ℕ → ℝ := fun j ↦ ∑ i : Fin j, a (u i) --partial sum
  let C : ℕ → ℕ := fun j ↦ ∑ i : Fin j, if a (u i) < 0 then 1 else 0 -- number of neg as used
  -- definition/construction rule of u
  have hu (j : ℕ) : u j = if P j < (C j : ℝ) + 1 then
      Nat.min {n ∈ A_plus | ∀ i : Fin j, n ≠ u i}
    else Nat.min {n ∈ A_minus | ∀ i : Fin j, n ≠ u i} :=
    Nat.strongRec.eq_def _ j
  -- an infinite set minus used is not empty
  have havail (A : Set ℕ) (hA : Infinite A) (j : ℕ) :
      ({n ∈ A | ∀ i : Fin j, n ≠ u i} : Set ℕ).Nonempty := by
    have hseen : Set.Finite {n | ∃ i : Fin j, u i = n} := by
      simpa using Set.finite_range (fun i : Fin j ↦ u i)
    have hdiff := (Set.infinite_coe_iff.mp hA).diff hseen
    have heq : A \ {n | ∃ i : Fin j, u i = n} =
        {n ∈ A | ∀ i : Fin j, n ≠ u i} := by
      ext n
      simp [eq_comm]
    rw [heq] at hdiff
    exact hdiff.nonempty
  -- property of u(j) : either choose from plus or minus
  have hchoice (j : ℕ) :
      (P j < (C j : ℝ) + 1 ∧ u j ∈ A_plus ∧ ∀ i : Fin j, u j ≠ u i) ∨
      ((C j : ℝ) + 1 ≤ P j ∧ u j ∈ A_minus ∧ ∀ i : Fin j, u j ≠ u i) := by
    rw [hu j]
    split_ifs with h
    · exact Or.inl ⟨h, (Nat.min_spec (havail A_plus hA_plus_inf j)).1⟩
    · exact Or.inr ⟨le_of_not_gt h, (Nat.min_spec (havail A_minus hA_minus_inf j)).1⟩
  -- u is injective as it will never choose seen one
  have hinj : Injective u := by
    have hne {i j : ℕ} (hij : i < j) : u j ≠ u i := by
      rcases hchoice j with h | h <;> exact h.2.2 ⟨i, hij⟩
    intro i j hij
    rcases lt_trichotomy i j with h | h | h
    · exact False.elim (hne h hij.symm)
    · exact h
    · exact False.elim (hne h hij)
  -- property of P
  have hPstep (j : ℕ) : P (j + 1) = P j + a (u j) := by
    simp [P, Fin.sum_univ_castSucc]
  -- property of C
  have hCstep (j : ℕ) : C (j + 1) = C j + if a (u j) < 0 then 1 else 0 := by
    dsimp only [C]
    rw [Fin.sum_univ_castSucc]
    rfl
  have hCmono : Monotone C := monotone_nat_of_le_succ (fun j ↦ by
    rw [hCstep]; omega)
  -- Both choices occur infinitely often, so choosing the least unused index omits no term.
  have hminus_inf : {j | a (u j) < 0}.Infinite := by
    -- assume it's finite, it will have a upper bound K
    intro hfin
    obtain ⟨K, hK⟩ := hfin.bddAbove
    -- for all j > K, a (u j) >= 0
    have hpos {j : ℕ} (hj : K < j) : 0 ≤ a (u j) := by
      by_contra! h
      exact (not_lt_of_ge (hK h)) hj
    -- and C keep constant after K
    have hCconst : ∀ j ≥ K + 1, C j = C (K + 1) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => rfl
      | succ j hj ih => rw [hCstep, if_neg (not_lt.mpr (hpos (by omega))), ih, add_zero]
    -- but for all j > K, partial sum P(j) < C (K+1) + 1 as defined 
    have hlt {j : ℕ} (hj : K < j) : P j < (C (K + 1) : ℝ) + 1 := by
      rcases hchoice j with h | h
      · simpa [hCconst j (by omega)] using h.1
      · exact False.elim (not_lt_of_ge (hpos hj) h.2.1)
    -- Per definition, for all j > K, it's the minimal unused index from A_plus
    have hmin (j : ℕ) (hj : K < j) :
        u j = Nat.min {n ∈ A_plus | ∀ i : Fin j, n ≠ u i} := by
      rw [hu, if_pos]
      simpa [hCconst j (by omega)] using hlt hj
    obtain ⟨g, hg, _⟩ := (Nat.monotone_enum_of_infinite A_plus).exists
    -- Now we can show that A_plus is convergent
    apply h1
    exact AbsConvergent'.of_seen_partial_abs_bound hinj g hg
      (fun x hx ↦ Nat.exists_mem_range_of_eventually_min hinj K hmin hx)
      (abs_partial_bound_of_eventually_nonneg hlt (fun hj ↦ hpos hj))
  have hplus_inf : {j | 0 ≤ a (u j)}.Infinite := by
    intro hfin
    obtain ⟨K, hK⟩ := hfin.bddAbove
    have hneg {j : ℕ} (hj : K < j) : a (u j) < 0 := by
      by_contra! h
      exact (not_lt_of_ge (hK h)) hj
    have hge {j : ℕ} (hj : K < j) : (0 : ℝ) ≤ P j := by
      rcases hchoice j with h | h
      · exact False.elim (not_lt_of_ge h.2.1 (hneg hj))
      · exact le_trans (by positivity) h.1
    have hmin (j : ℕ) (hj : K < j) :
        u j = Nat.min {n ∈ A_minus | ∀ i : Fin j, n ≠ u i} := by
      rw [hu, if_neg]
      rcases hchoice j with h | h
      · exact False.elim (not_lt_of_ge h.2.1 (hneg hj))
      · exact not_lt.mpr h.1
    obtain ⟨g, hg, _⟩ := (Nat.monotone_enum_of_infinite A_minus).exists
    exact h2 (AbsConvergent'.of_seen_partial_abs_bound hinj g hg
      (fun x hx ↦ Nat.exists_mem_range_of_eventually_min hinj K hmin hx)
      (abs_partial_bound_of_eventually_neg hge (fun hj ↦ hneg hj)))
  have hsurj : Surjective u := by
    intro x
    by_contra! hmissing
    have hbounded (A : Set ℕ) (hx : x ∈ A)
        (hbranch : ∀ j, u j ∈ A → u j = Nat.min {n ∈ A | ∀ i : Fin j, n ≠ u i}) :
        {j | u j ∈ A}.Finite := by
      have hle : ∀ j, u j ∈ A → u j ≤ x := by
        intro j hj
        rw [hbranch j hj]
        have hxmem : x ∈ {n ∈ A | ∀ i : Fin j, n ≠ u i} :=
          ⟨hx, fun i ↦ (hmissing i).symm⟩
        exact (Nat.min_spec ⟨x, hxmem⟩).2 x hxmem
      apply Set.Finite.of_finite_image (f := u) _ hinj.injOn
      exact (Set.finite_Iic x).subset (by
        rintro y ⟨j, hj, rfl⟩
        exact hle j hj)
    by_cases hx : 0 ≤ a x
    · apply hplus_inf
      exact hbounded A_plus hx (by
        intro j hj
        rw [hu, if_pos]
        rcases hchoice j with h | h
        · exact h.1
        · exact False.elim (not_lt_of_ge (show 0 ≤ a (u j) from hj) (show a (u j) < 0 from h.2.1)))
    · apply hminus_inf
      exact hbounded A_minus (lt_of_not_ge hx) (by
        intro j hj
        rw [hu, if_neg]
        rcases hchoice j with h | h
        · exact False.elim (not_lt_of_ge (show 0 ≤ a (u j) from h.2.1) (show a (u j) < 0 from hj))
        · exact not_lt.mpr h.1)
  -- Convergence of the original series gives a uniform lower bound for its terms.
  have ha0 : Tendsto a atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN, htail⟩ := (converges_iff_tail_decay _).mp ha (ε / 2) (half_pos hε)
    lift N to ℕ using hN
    refine ⟨N, fun n hn ↦ ?_⟩
    have h := htail n (by exact_mod_cast hn) n (by exact_mod_cast hn)
    simp at h
    simpa [Real.dist_eq] using lt_of_le_of_lt h (half_lt_self hε)
  obtain ⟨b, hb⟩ := ha0.bddBelow_range
  let B := max 0 (-b)
  have hB : 0 ≤ B := le_max_left _ _
  have hab (n : ℕ) : -B ≤ a n := by
    have : -b ≤ B := le_max_right _ _
    linarith [hb (Set.mem_range_self n)]
  have hlower (j : ℕ) : (C j : ℝ) - B ≤ P j := by
    induction j with
    | zero => simpa [P, C] using hB
    | succ j ih =>
      rw [hPstep, hCstep]
      rcases hchoice j with h | h
      · have hpos : 0 ≤ a (u j) := h.2.1
        rw [if_neg (not_lt.mpr hpos), add_zero]
        linarith
      · have hneg : a (u j) < 0 := h.2.1
        rw [if_pos hneg, Nat.cast_add, Nat.cast_one]
        linarith [hab (u j), h.1]
  have hCtop : Tendsto C atTop atTop := by
    apply hCmono.tendsto_atTop_atTop
    intro m
    by_contra! hbound
    have hcard (j : ℕ) : ({i ∈ Finset.range j | a (u i) < 0}).card = C j := by
      dsimp only [C]
      rw [Fin.sum_univ_eq_sum_range (fun i ↦ if a (u i) < 0 then (1 : ℕ) else 0) j]
      simp
    obtain ⟨T, hT, hTm⟩ := hminus_inf.exists_subset_card_eq m
    obtain ⟨J, hJ⟩ := Finset.exists_bound_of_mem_range (u := id) T (fun x _ ↦ ⟨x, rfl⟩)
    have hsub : T ⊆ {i ∈ Finset.range J | a (u i) < 0} := by
      intro x hx
      obtain ⟨i, hi⟩ := hJ x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hi ▸ i.2), hT hx⟩
    have := Finset.card_le_card hsub
    rw [hTm, hcard] at this
    exact (not_le_of_gt (hbound J)) this
  have hPtop : Tendsto P atTop atTop := by
    apply tendsto_atTop_mono hlower
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-B)
        (tendsto_natCast_atTop_atTop.comp hCtop)
  refine ⟨u, ⟨hinj, hsurj⟩, ?_⟩
  rw [EReal.tendsto_coe_nhds_top_iff, Filter.Tendsto.int_natCast_atTop]
  convert hPtop.comp (tendsto_add_atTop_nat 1) using 1
  ext N
  change (a ∘ u : Series).partial (N : ℤ) = P (N + 1)
  simp [P, Series.partial, Finset.Icc_eq_cast]
  have hIcc : Finset.Icc 0 N = Finset.range (N + 1) := by ext x; simp
  rw [hIcc, ← Fin.sum_univ_eq_sum_range]
--
theorem permute_diverges_of_divergent' {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges)  :
  ∃ f : ℕ → ℕ,  Bijective f ∧ atTop.Tendsto (fun N ↦ ((a ∘ f:Series).partial N : EReal)) (nhds ⊥) := by
  have hpartial (b : ℕ → ℝ) (N : ℤ) :
      (fun n ↦ -b n : Series).partial N = -(b : Series).partial N := by
    simp only [Series.partial]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0 ≤ n := (Finset.mem_Icc.mp hn).1
    simp [hn0]
  have hneg : (fun n ↦ -a n : Series).converges := by
    obtain ⟨L, hL⟩ := ha
    refine ⟨-L, ?_⟩
    change Tendsto (fun N ↦ (fun n ↦ -a n : Series).partial N) atTop (nhds (-L))
    simp_rw [hpartial]
    exact hL.neg
  have hneg' : ¬ (fun n ↦ -a n : Series).absConverges := by
    intro h
    apply ha'
    change (fun n ↦ -a n : Series).abs.converges at h
    have habs : (fun n ↦ -a n : Series).abs = (a : Series).abs := by
      ext n
      · rfl
      · by_cases hn : n ≥ 0 <;> simp [hn]
    change (a : Series).abs.converges
    rwa [habs] at h
  obtain ⟨f, hf, htop⟩ := permute_diverges_of_divergent (a := fun n ↦ -a n) hneg hneg'
  refine ⟨f, hf, ?_⟩
  have heq (N : ℤ) : ((fun n ↦ -a n) ∘ f : Series).partial N =
      -(a ∘ f : Series).partial N := hpartial (a ∘ f) N
  have hneg_top : Tendsto (fun x : EReal ↦ -x) (nhds ⊤) (nhds ⊥) := by
    simpa using (continuous_neg : Continuous (fun x : EReal ↦ -x)).tendsto (⊤ : EReal)
  have hbot := hneg_top.comp htop
  change Tendsto (fun N ↦ -(((fun n ↦ -a n) ∘ f : Series).partial N : EReal))
    atTop (nhds ⊥) at hbot
  have hident : (fun N ↦ -(((fun n ↦ -a n) ∘ f : Series).partial N : EReal)) =
      (fun N ↦ ((a ∘ f : Series).partial N : EReal)) := by
    funext N
    rw [heq, EReal.coe_neg, neg_neg]
  rw [hident] at hbot
  exact hbot

-- end Chapter8
