import Mathlib.Tactic
import Analysis.Section_7_3
/-!
# Analysis I, Section 7.4: Rearrangement of series

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Rearrangement of non-negative or absolutely convergent series.
-/

namespace Chapter7

theorem Series.sum_eq_sum (b:ℕ → ℝ) {N:ℤ} (hN: N ≥ 0) : ∑ n ∈ .Icc 0 N, (if 0 ≤ n then b n.toNat else 0) = ∑ n ∈ .Iic N.toNat, b n := by
      convert Finset.sum_image (g := Int.ofNat) (by simp)
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind

/-- Proposition 7.4.1 -/
theorem Series.converges_of_permute_nonneg {a:ℕ → ℝ} (ha: (a:Series).nonneg) (hconv: (a:Series).converges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n) : Series).converges ∧ (a:Series).sum = (fun n ↦ a (f n) : Series).sum := by
  -- This proof is written to follow the structure of the original text.
  set af : ℕ → ℝ := fun n ↦ a (f n)
  have haf : (af:Series).nonneg := by
    intro n; by_cases h : n ≥ 0 <;> simp [h, af]
    specialize ha (f n.toNat); grind
  set S := (a:Series).partial
  set T := (af:Series).partial
  have hSmono : Monotone S := Series.partial_of_nonneg ha
  have hTmono : Monotone T := Series.partial_of_nonneg haf
  set L := iSup S
  set L' := iSup T
  have hSBound : ∃ Q, ∀ N, S N ≤ Q := (converges_of_nonneg_iff ha).mp hconv
  suffices : (∃ Q, ∀ M, T M ≤ Q) ∧ L = L'
  . have Ssum : L = (a:Series).sum := by
      symm; apply sum_of_converges; simp [convergesTo, L]
      apply tendsto_atTop_isLUB hSmono (isLUB_csSup _ _)
      . use (S 0); aesop
      choose Q hQ using hSBound; use Q; simp [upperBounds, hQ]
    have Tsum : L' = (af:Series).sum := by
      symm; apply sum_of_converges; simp [convergesTo, L']
      apply tendsto_atTop_isLUB hTmono (isLUB_csSup _ _)
      . use (T 0); aesop
      choose Q hQ using this.1; use Q; simp [upperBounds, hQ]
    simp [←Ssum, ←Tsum, this.2, converges_of_nonneg_iff haf]
    convert this.1
  have hTL (M:ℤ) : T M ≤ L := by
    by_cases hM : M ≥ 0
    swap
    . have hM' : M < 0 := by linarith
      simp [T, Series.partial, hM']
      convert le_ciSup (f := S) ?_ (-1)
      simp [BddAbove, Set.Nonempty, upperBounds, hSBound]
    set Y := Finset.Iic M.toNat
    have hN : ∃ N, ∀ m ∈ Y, f m ≤ N := by
      use (Y.image f).sup id; intro m hm
      apply Finset.le_sup (f := id); grind
    choose N hN using hN
    calc
      _ = ∑ m ∈ Y, af m := by simp [T, Series.partial, af]; exact sum_eq_sum af hM
      _ = ∑ n ∈ f '' Y, a n := by symm; convert Finset.sum_image (by solve_by_elim [hf.injective]); simp
      _ ≤ ∑ n ∈ .Iic N, a n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro _ _; aesop
        intro i _ _; specialize ha i; aesop
      _ = S N := by simp [S, Series.partial]; symm; apply sum_eq_sum (N:=N) a; positivity
      _ ≤ L := by apply le_ciSup _ (N:ℤ); simp [BddAbove, Set.Nonempty, upperBounds, hSBound]
  have hTbound : ∃ Q, ∀ M, T M ≤ Q := by use L
  simp [hTbound]
  have hSL' (N:ℤ) : S N ≤ L' := by
    by_cases hN : N ≥ 0
    swap
    . have hN' : N < 0 := by linarith
      simp [S, Series.partial, hN']
      convert le_ciSup (f := T) ?_ (-1)
      simp [BddAbove, Set.Nonempty, upperBounds, hTbound]
    set X := Finset.Iic N.toNat
    have hM : ∃ M, ∀ n ∈ X, ∃ m, f m = n ∧ m ≤ M := by
      use (X.preimage f (Set.injOn_of_injective hf.1)).sup id
      intro n hn; choose m hm using hf.2 n
      refine ⟨ _, hm, ?_ ⟩
      apply Finset.le_sup (f := id)
      simp [Finset.mem_preimage, hm, hn]
    choose M hM using hM
    have sum_eq_sum (b:ℕ → ℝ) {N:ℤ} (hN: N ≥ 0)
      : ∑ n ∈ .Icc 0 N, (if 0 ≤ n then b n.toNat else 0) = ∑ n ∈ .Iic N.toNat, b n := by
      convert Finset.sum_image (g := Int.ofNat) (by simp)
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind
    calc
      _ = ∑ n ∈ X, a n := by simp [S, sum_eq_sum, hN, X]
      _ = ∑ n ∈ ((Finset.Iic M).filter (f · ∈ X)).image f, a n := by
        congr; ext; simp; constructor
        . intro h; obtain ⟨ m, rfl, hm' ⟩ := hM _ h; use m
        rintro ⟨ _, ⟨ _, _⟩, rfl ⟩; simp_all
      _ ≤ ∑ m ∈ .Iic M, af m := by
        rw [Finset.sum_image (by solve_by_elim [hf.injective])]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        . aesop
        intro i _ _; specialize haf i; aesop
      _ = T M := by simp [T, Series.partial, af]; symm; apply sum_eq_sum af; positivity
      _ ≤ L' := by apply le_ciSup _ (M:ℤ); simp [BddAbove, Set.Nonempty, upperBounds, hTbound]
  linarith [ciSup_le hSL', ciSup_le hTL]

/-- Example 7.4.2 -/
theorem Series.zeta_2_converges : (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).converges := by
  set z := (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series)
  have hnonneg : z.nonneg := by
    simp[z,nonneg];intro n; split_ifs <;>simp
    apply pow_two_nonneg
  rw[converges_of_nonneg_iff hnonneg]
  use 2;intro N
  by_cases hN : 0 ≤ N
  .
    lift N to ℕ using hN
    have hzu : z.partial N ≤ 2 - (1 / (N+1)) := by
      induction' N with k hind
      . simp[Series.partial,z];norm_num
      simp
      rw[partial_succ']
      calc
        _ = z.partial k + 1 / (k+1+1)^2 := by simp[z,show 0 ≤ (k:ℤ)+1 by omega ];
        _ ≤ z.partial k + 1 / ((k+1)* (k+2)) := by simp;field_simp; ring_nf;norm_cast;omega
        _ ≤ 2 - 1 / (k+1) + 1 / ((k+1)* (k+2)) := by gcongr
        _ = _ := by field_simp;ring_nf
    apply le_trans hzu
    simp;norm_cast;omega
  rw[partial_of_lt (by simp_all[z])]
  simp

lemma Series.permuted_zeta_2_converges_and_eq :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).converges ∧ 
    (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).sum = (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).sum := by 
    set t:= fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2  
    set a := fun n:ℕ ↦ 1/(n+1:ℝ)^2 
    have ha : (a:Series).nonneg  := by
      simp[nonneg];intro n
      split_ifs
      . simp[a];apply pow_two_nonneg
      simp
    have hconv : (a:Series).converges  := zeta_2_converges
    set f := fun (n:ℕ) ↦ if Even n then n+1 else n-1 
    have hf : Function.Bijective f := by
      constructor
      . intro x1 x2
        contrapose!;intro h;simp[f]
        split_ifs <;> grind
      . intro x
        by_cases hx : Even x
        . use (x+1); grind
        use (x-1);grind
    have := (converges_of_permute_nonneg ha hconv hf)
    set a' := (a:Series)
    set t' := (t:Series)
    set t'' := (fun n ↦ a (f n) : Series)
    have heq : t' = t'' := by
      simp[t',t''];ext n
      split_ifs with hn
      lift n to ℕ using hn
      . simp[t,a,f]; split_ifs with hev
        . ring
        have hn1 : n ≥ 1 := by grind
        simp[hn1]
      simp
    rwa[heq]

theorem Series.permuted_zeta_2_converges :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).converges := by
    exact permuted_zeta_2_converges_and_eq.1

theorem Series.permuted_zeta_2_eq_zeta_2 :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).sum = (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).sum := by
    exact permuted_zeta_2_converges_and_eq.2.symm

/-- Proposition 7.4.3 (Rearrangement of series) -/
theorem Series.absConverges_of_permute {a:ℕ → ℝ} (ha : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n) : Series).sum := by
  -- This proof is written to follow the structure of the original text.
  set L := (a:Series).abs.sum
  have hconv := converges_of_absConverges ha
  unfold absConverges at ha
  have habs : (fun n ↦ |a (f n)| : Series).converges ∧ L = (fun n ↦ |a (f n)| : Series).sum := by
    convert converges_of_permute_nonneg (a := fun n ↦ |a n|) _ _ hf using 3
    . simp; ext n; by_cases n ≥ 0 <;> grind
    . intro n; by_cases h: n ≥ 0 <;> simp [h]
    convert ha with n; by_cases n ≥ 0 <;> grind
  set L' := (a:Series).sum
  set af : ℕ → ℝ := fun n ↦ a (f n)
  suffices : (af:Series).convergesTo L'
  . simp [sum_of_converges this, absConverges]
    convert habs.1 with n; by_cases n ≥ 0 <;> grind
  simp [convergesTo, LinearOrderedAddCommGroup.tendsto_nhds]
  intro ε hε
  rw [converges_iff_tail_decay] at ha
  choose N₁ hN₁ ha using ha _ (half_pos hε); simp at hN₁
  have : ∃ N ≥ N₁, |(a:Series).partial N - L'| < ε/2 := by
    apply convergesTo_sum at hconv
    simp [convergesTo, LinearOrderedAddCommGroup.tendsto_nhds] at hconv
    choose N hN using hconv _ (half_pos hε)
    use max N N₁, (by grind); apply hN; grind
  choose N hN hN2 using this
  have hNpos : N ≥ 0 := by linarith
  let finv : ℕ → ℕ := Function.invFun f
  have : ∃ M, ∀ n ≤ N.toNat, finv n ≤ M := by
    use ((Finset.Iic (N.toNat)).image finv).sup id
    intro n hn
    apply Finset.le_sup (f := id); simp [Finset.mem_image]; use n, hn; rfl
  choose M hM using this; use M; intro M' hM'
  have hM'_pos : M' ≥ 0 := by linarith
  have why : (Finset.Iic M'.toNat).image f ⊇ .Iic N.toNat := by
    lift M' to ℕ using hM'_pos
    simp[Superset,Subset]
    intro a ha ;use (finv a)
    split_ands; grind
    simp[finv]
    apply Function.invFun_eq
    apply hf.surjective
  set X : Finset ℕ := (Finset.Iic M'.toNat).image f \ .Iic N.toNat
  have claim : ∑ m ∈ .Iic M'.toNat, a (f m) = ∑ n ∈ .Iic N.toNat, a n + ∑ n ∈ X, a n := calc
    _ = ∑ n ∈ (Finset.Iic M'.toNat).image f , a n := by
      symm; apply Finset.sum_image; solve_by_elim [hf.1]
    _ = _ := by
      convert Finset.sum_union _ using 2
      . simp [X, why]
      . infer_instance
      rw [Finset.disjoint_right]; intro n hn; simp only [X, Finset.mem_sdiff] at hn; tauto
  choose q' hq using X.bddAbove
  set q := max q' N.toNat
  have why2 : X ⊆ Finset.Icc (N.toNat+1) q := by
    intro x hx ;simp
    split_ands
    . simp[X] at hx;tauto
    rw[mem_upperBounds] at hq
    specialize hq x hx
    grind

  have claim2 : |∑ n ∈ X, a n| ≤ ε/2 := calc
    _ ≤ ∑ n ∈ X, |a n| := X.abs_sum_le_sum_abs a
    _ ≤ ∑ n ∈ .Icc (N.toNat+1) q, |a n| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg why2; simp
    _ ≤ ε/2 := by
      convert ha (N.toNat+1) _ q _ <;> try omega
      simp [hNpos]; rw [abs_of_nonneg (by positivity)]; symm
      convert Finset.sum_image (g := fun (n:ℕ) ↦ (n:ℤ)) (by simp) using 2
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind
  calc
    _ ≤ |(af:Series).partial M' - (a:Series).partial N| + |(a:Series).partial N - L'| := abs_sub_le _ _ _
    _ < |(af:Series).partial M' - (a:Series).partial N| + ε/2 := by gcongr
    _ ≤ ε/2 + ε/2 := by
      gcongr; convert claim2
      simp [Series.partial, sum_eq_sum _ hM'_pos, sum_eq_sum _ hNpos]; grind
    _ = ε := by ring

/-- Example 7.4.4 -/
noncomputable abbrev Series.a_7_4_4 : ℕ → ℝ := fun n ↦ (-1:ℝ)^n / (n+2)

theorem Series.ex_7_4_4_conv : (a_7_4_4 : Series).converges := by
  set a: {n// n ≥ (0:ℤ)} → ℝ := fun n ↦  1/(n+2)
  suffices h: (mk' (fun n ↦ (-1)^(n:ℤ) * a n)).converges from by
    simp[mk',a] at h
    simp[a_7_4_4]
    convert h using 4 with n hn
    lift n to ℕ using hn
    simp;ring
  have ha: ∀ n, a n ≥ 0 := by
    simp[a];intro n hn; norm_cast;omega
  have ha': Antitone a := by
    rintro ⟨n1,hn1⟩ ⟨n2,hn2⟩  hle
    simp at hle
    lift n1 to ℕ using hn1
    lift n2 to ℕ using hn2
    simp at hle
    simp[a];field_simp; norm_cast
    omega
  rw[converges_of_alternating ha ha']
  simp[a]
  have hne : Nonempty {n // n ≥ (0:ℤ )} := by use 0
  rw[Metric.tendsto_atTop]
  intro ε hε
  use ⟨⌊ε⁻¹⌋,by simp;rw[Int.le_floor];simp;linarith ⟩ 
  rintro ⟨n,hn⟩  hle
  simp at hle;simp;rw[abs_of_nonneg  (by norm_cast;omega)]
  rw[Int.floor_le_iff] at hle
  apply inv_lt_of_inv_lt₀ hε
  linarith

theorem Series.ex_7_4_4_sum : (a_7_4_4 : Series).sum > 0 := by
  suffices h : 1/6 ≤ (a_7_4_4 :Series).sum from by
    apply lt_of_lt_of_le (by simp) h
  have hconv := convergesTo_sum Series.ex_7_4_4_conv
  unfold convergesTo at hconv
  apply ge_of_tendsto hconv
  rewrite[Filter.eventually_atTop]
  use 0; intro n hn 
  suffices h: ∀ (k:ℕ), (a_7_4_4 :Series).partial (2*k) ≥ 1/6 ∧ (a_7_4_4 :Series).partial (2*k+1) ≥ 1/6 from by
    obtain ⟨k,heven | hodd⟩  := Int.even_or_odd' n
    <;> lift k to ℕ using (by omega) 
    . rw[heven];exact(h k).1
    rw[hodd];exact(h k).2
  simp[a_7_4_4 ]
  intro k;induction' k with k hind
  . simp;split_ands
    swap;rw[show (1:ℤ) = (0+1) by omega, partial_succ']
    all_goals
      simp[Series.partial ];norm_num
  split_ands
  . rw[show (2:ℤ) * (k+1:ℕ) = 2 * k + 1 + 1 by omega,partial_succ']
    apply le_trans hind.2
    have :(0:ℤ) ≤ 2 * k + 1 + 1 := by omega
    simp[this]
    apply div_nonneg
    . apply Even.pow_nonneg
      use (k+1);omega
    . norm_cast;omega
  . rw[show (2:ℤ) * (k+1:ℕ) = 2 * k + 1 + 1 by omega,partial_succ',partial_succ']
    apply le_trans hind.2
    have hpos1 :(0:ℤ) ≤ 2 * k + 2 := by omega
    have hpos2 :(0:ℤ) ≤ 2 * k + 3 := by omega
    simp[add_assoc,hpos1,hpos2]
    rw[show ((2:ℤ) * k + 2).toNat = 2 * k +2 by rfl ]
    rw[show ((2:ℤ) * k + 3).toNat = 2 * k +3 by rfl ]
    field_simp;simp
    ring_nf;simp

abbrev Series.f_7_4_4 : ℕ → ℕ := fun n ↦ if n % 3 = 0 then 2 * (n/3) else 4 * (n/3) + 2 * (n % 3) - 1

theorem Series.f_7_4_4_bij : Function.Bijective f_7_4_4 := by
  unfold f_7_4_4
  constructor
  . intro x1 x2 heq
    by_cases hx1 : x1 % 3 = 0
    <;> by_cases hx2 : x2 % 3 = 0
    <;> simp[hx1,hx2] at heq
    <;> omega
  intro y
  obtain ⟨k,heven|hodd⟩ := y.even_or_odd' 
  . use 3 * k;simp[heven]
  obtain ⟨m, hkm|hkm⟩ := k.even_or_odd' 
  <;> simp[hkm] at hodd <;> ring_nf at hodd
  .  use 3 * m + 1; simp[hodd];omega
  use 3 * m + 2; simp[hodd];omega
    
lemma Series.sum_coe {a : ℕ → ℝ} {n m : ℕ } : (∑ x ∈ Finset.Icc (n:ℤ) m, (a:Series).seq x) = ∑ x ∈ Finset.Icc n m, a x := by
  by_cases hmn : m < n; . simp[hmn]
  simp at hmn
  
  induction' m,hmn using Nat.le_induction with k hk hind; simp
  simp
  rw[Finset.sum_Icc_succ_top (by omega)]
  rw[Finset.sum_of_nonempty (by omega)]
  simp[show (0:ℤ) ≤ k + 1 by omega]
  exact hind

lemma Series.converges_of_three_blocks  {c s: ℕ → ℝ} (hc : (c:Series).converges)
  (hblock: ∀ k:ℕ, s (3*k) + s (3*k+1) + s (3*k+2) = c k)
    (h0 : Filter.atTop.Tendsto (fun k => s (3*k)) (nhds 0))
    (h1 : Filter.atTop.Tendsto (fun k => s (3*k+1)) (nhds 0))
    (h2 : Filter.atTop.Tendsto (fun k => s (3*k+2)) (nhds 0)) :
    (s:Series).converges ∧ (s:Series).sum = (c:Series).sum:= by
      have hcL := convergesTo_sum hc
      suffices hsL :(s:Series).convergesTo (c:Series).sum from by
        split_ands
        . use (c:Series).sum
        exact sum_of_converges hsL
      set L := (c:Series).sum
      set s' := (s:Series)
      set c' := (c:Series)
      unfold convergesTo at  hcL ⊢ 
      rw[Metric.tendsto_atTop] at hcL ⊢ h1 h2
      intro ε hε
      have hte : ε/3 >0 := by linarith
      specialize hcL _ hte
      specialize h1 _ hte
      specialize h2 _ hte
      choose Nc hNc using hcL
      choose N1 hN1 using h1
      choose N2 hN2 using h2
      set N := max Nc (max N1 N2)
      use 3 * N;intro p hp
      simp[dist,Series.partial,c',s'] at ⊢ hNc
      lift p to ℕ using by omega
      set n := p / 3
      have hn : n ≥ N := by omega
      specialize hNc n (by omega)
      nth_rw 1 [← Int.natCast_zero] at ⊢ hNc
      rw[sum_coe] at ⊢ hNc
      have heq : ∑ x ∈ Finset.Icc 0 (3 * n + 2), s x = ∑ x ∈ Finset.Icc 0 n, c x := by
        induction' n with k hind
        . simp
          repeat rw[Finset.sum_Icc_succ_top (by omega)]
          simp[hblock 0]
        nth_rw 2[Finset.sum_Icc_succ_top (by omega)]
        rw[← hind]
        rw[show 3 * (k+1) + 2 = 3 * k + 5by omega]
        iterate 3 rw[Finset.sum_Icc_succ_top (by omega)]
        rw[add_assoc,add_assoc]
        specialize hblock (k+1)
        simp[← hblock]
        ring_nf
      specialize hN1 n (by omega)
      specialize hN2 n (by omega)
      simp[dist] at hN1 hN2
      by_cases hp2 : p % 3 = 2
      . have hnp : p = 3 * n + 2 := by omega
        rw[hnp,heq];linarith
      by_cases hp1 : p % 3 = 1
      . have hnp : p = 3 * n + 1 := by omega
        rw[hnp]
        have : ∑ x ∈ Finset.Icc 0 (3 * n + 1), s x = ∑ x ∈ Finset.Icc 0 n, c x - s (3 * n + 2) := by
          rw[← heq,eq_sub_iff_add_eq]
          rw[← Finset.sum_Icc_succ_top (by omega)]
        simp[this]
        grind
      have hnp : p = 3 * n := by omega
      rw[hnp]
      have : ∑ x ∈ Finset.Icc 0 (3 * n), s x = ∑ x ∈ Finset.Icc 0 n, c x - s (3 * n + 2) - s (3*n+1):= by
        rw[← heq,eq_sub_iff_add_eq,eq_sub_iff_add_eq]
        rw[← Finset.sum_Icc_succ_top (by omega)]
        rw[← Finset.sum_Icc_succ_top (by omega)]
      simp[this]
      grind

lemma Series.ex_7_4_4'_conv_sum :(fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).converges ∧ (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).sum < 0 := by
  set s := fun n ↦ a_7_4_4  (f_7_4_4 n)
  set c := fun (n:ℕ) ↦ - (1:ℝ) / (32* n^3 + 96 * n ^2 + 94 * n + 30)
  have hs0 {k:ℕ} : s (3*k) = 1 / (2*k+2) := by
    simp[s,a_7_4_4 ]
  have hs1 {k:ℕ}: s (3*k+1) = -(1 / (4*k+3)) := by
    simp[s,a_7_4_4 ]
    rw[show (3 * k + 1)/3 = k by omega]
    have : Odd (4 * k + 1) := by grind
    rw[Odd.neg_one_pow this];ring
  have hs2 {k:ℕ}: s (3*k+2) = -(1 / (4*k+5)) := by
    simp[s,a_7_4_4 ]
    rw[show (3 * k + 2)/3 = k by omega]
    have : Odd (4 * k + 3) := by grind
    rw[Odd.neg_one_pow this];ring
  have hblock: ∀ k:ℕ, s (3*k) + s (3*k+1) + s (3*k+2) = c k := by
    intro k
    simp[hs0,hs1,hs2,c]
    field_simp
    ring
  have hzero : Filter.atTop.Tendsto (fun k: ℕ ↦ 0) (nhds (0:ℝ)) := by exact tendsto_const_nhds
  have hpos : Filter.atTop.Tendsto (fun k :ℕ ↦ (1:ℝ)/(k+1)) (nhds (0:ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hneg : Filter.atTop.Tendsto (fun k :ℕ ↦ (-1)* ((1:ℝ)/(k+1))) (nhds (0:ℝ)) := by
    have := hpos.const_mul (-1)
    simpa
  have h0 : Filter.atTop.Tendsto (fun k => s (3*k)) (nhds 0) := by
    simp[hs0]
    apply Filter.Tendsto.squeeze hzero hpos
    . intro k; simp;norm_cast;omega
    . intro k;simp
      rw[inv_le_inv₀ (by norm_cast;omega) (by norm_cast;omega)]
      norm_cast;omega
  have h1 : Filter.atTop.Tendsto (fun k => s (3*k+1)) (nhds 0) := by
    simp[hs1]
    apply Filter.Tendsto.squeeze hneg hzero
    . intro k;simp
      rw[inv_le_inv₀ (by norm_cast;omega) (by norm_cast;omega)]
      norm_cast;omega
    . intro k; simp;norm_cast;omega
  have h2 : Filter.atTop.Tendsto (fun k => s (3*k+2)) (nhds 0) := by
    simp[hs2]
    apply Filter.Tendsto.squeeze hneg hzero
    . intro k;simp
      rw[inv_le_inv₀ (by norm_cast;omega) (by norm_cast;omega)]
      norm_cast;omega
    . intro k; simp;norm_cast;omega
  have hc : (c:Series).converges := by
    suffices habs : (c:Series).absConverges  from by
      exact converges_of_absConverges habs
    refine  (converges_of_le ?_ ?_ zeta_2_converges).1
    . simp
    simp
    intro n hn
    lift n to ℕ using hn
    simp[c]
    rw[abs_of_neg]
    field_simp;norm_cast;ring_nf;omega
    field_simp;simp
  choose hconv hsum using (converges_of_three_blocks hc hblock h0 h1 h2)
  simp[hconv]
  rw[hsum]
  set c' := fun (n:ℕ) ↦ (1:ℝ) / (32* n^3 + 96 * n ^2 + 94 * n + 30) 
  have hcc': (c':Series) = (-1:ℝ) • (c:Series) := by
    simp[smul_coe];ext n; split_ifs with hn; lift n to ℕ using hn
    . simp[c,c'];field_simp
    simp
  obtain ⟨hc'conv, hc'sum⟩  := Series.smul (c:=-1) hc
  rw[← hcc'] at hc'conv hc'sum
  have hcnonneg : (c':Series).nonneg  := by
    simp[nonneg];intro z;split_ifs with hz
    . lift z to ℕ using hz
      simp[c'];field_simp;norm_cast;omega
    simp
  have hc'sum : (c':Series).sum > 0 := by
    apply lt_of_le_of_ne'
    . apply sum_of_nonneg hcnonneg
    by_contra hcon
    rw[nonneg_sum_zero] at hcon
    . specialize hcon 0
      simp[c'] at hcon
    assumption'
  linarith

theorem Series.ex_7_4_4'_conv : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).converges := by
  exact Series.ex_7_4_4'_conv_sum.1

theorem Series.ex_7_4_4'_sum : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).sum < 0 := by
  exact Series.ex_7_4_4'_conv_sum.2

/-- Exercise 7.4.1 -/
lemma Series.abs_coe {a:ℕ → ℝ} : (a:Series).abs = (fun n ↦ |a n|:Series) := by
  simp;ext n
  split_ifs with hn
  lift n to ℕ using hn
  simp;simp

theorem Series.absConverges_of_subseries {a:ℕ → ℝ} (ha: (a:Series).absConverges) {f: ℕ → ℕ} (hf: StrictMono f) :
  (fun n ↦ a (f n):Series).absConverges := by
    have hf' (n:ℕ) : f n ≥ n := by
      induction' n with k hind
      simp
      have : k+1 > k := by omega
      have := hf this
      apply Nat.succ_le_of_lt
      omega
    set af := fun n ↦ a (f n)

    unfold absConverges  at ha ⊢
    rw[abs_coe] at ha ⊢
    rw[converges_iff_tail_decay] at ha ⊢
    peel ha with ε hε N hN ha
    lift N to ℕ using hN
    intro p hp q hq
    lift p to ℕ using by omega
    lift q to ℕ using by omega
    simp at hp hq
    specialize ha (f p) (by grind) (f q) (by grind)
    rw[sum_coe (a:= fun n ↦ |a n|)] at ha
    rw[sum_coe (a:= fun n ↦ |af n|)]

    apply le_trans' ha
    rw[Finset.abs_sum_of_nonneg (by simp)]
    rw[Finset.abs_sum_of_nonneg (by simp)]
    set a' := fun n ↦ |a n|
    have hsubtr (x:ℕ ): |af x| = a' (f x) := by simp[af,a']
    simp[hsubtr] 
    rw[← Finset.sum_image (by
      intro x1 hx1 x2 hx2
      contrapose! ;intro hne
      obtain hle |hle := lt_or_gt_of_ne hne
      <;> have := hf hle
      <;> omega
    )]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    intro x hx
    simp at hx
    obtain  ⟨ a ,⟨hap,haq⟩, hfa⟩  := hx
    simp[← hfa]
    have hf' {x y:ℕ } : x ≤ y → f x ≤ f y := by
      intro hxy
      obtain (hlt|rfl) := lt_or_eq_of_le hxy
      . apply le_of_lt (hf hlt)
      simp
    refine ⟨hf' hap, hf' haq ⟩ 
    simp[a']


/--
{given -show}`n : ℕ`
Exercise 7.4.2 : reprove Proposition 7.4.3 using Proposition 7.41, Proposition 7.2.14,
and expressing {lean}`a n` as the difference of {lean}`a n + |a n|` and {lean}`|a n|`.
-/
theorem Series.absConverges_of_permute' {a:ℕ → ℝ} (ha : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n):Series).sum := by
      set aabs := fun n ↦ |a n|
      have habsng : (aabs:Series).nonneg  := by 
        simp[nonneg];intro n;split_ifs
        simp[aabs]
        simp
      have habsconv : (aabs:Series).converges := by
        unfold absConverges  at ha
        convert ha with x
        split_ifs with hx
        simp[aabs,hx]
        simp
      have haabsf := converges_of_permute_nonneg habsng habsconv hf
      set ang := fun n ↦ aabs n - a n
      have hang : (ang:Series).nonneg := by
        simp[nonneg];intro n;split_ifs
        simp[ang,aabs]
        grind;grind
      have hangconv : (ang:Series).converges := by
        have hsub := (Series.sub habsconv (converges_of_absConverges ha)).1
        convert hsub with n
        rw[sub_coe]
      have hangf := converges_of_permute_nonneg hang hangconv hf
      split_ands
      . have := haabsf.1
        unfold absConverges 
        convert this with x
        simp;split_ifs with hx
        . simp[aabs]
        simp
      have hsub : (a:Series).sum = (aabs:Series).sum - (ang:Series).sum := by
        have := (Series.sub habsconv hangconv).2
        convert this with x
        rw[sub_coe]
        split_ifs with hx
        . simp[hx,aabs,ang]
        simp;tauto
      rw[hsub]
      rw[hangf.2,haabsf.2]
      have := (Series.sub haabsf.1 hangf.1).2
      rw[← this]
      congr
      rw[sub_coe (a:= fun n ↦ aabs (f n)) (b:= fun n ↦ ang (f n))]
      simp;ext n
      split_ifs with hn
      . simp[aabs,ang]
      simp

end Chapter7
