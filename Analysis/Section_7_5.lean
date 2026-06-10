import Mathlib.Tactic
import Analysis.Section_6_4
import Analysis.Section_7_4
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Analysis I, Section 7.5: The root and ratio tests

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- The root and ratio tests/

A point that is only implicitly stated in the text is that for the root and ratio tests, the lim inf and lim sup should be interpreted within the extended reals.  The Lean formalizations below make this point more explicit.

-/

namespace Chapter7

open Filter Real EReal

/-- Theorem 7.5.1(a) (Root test).  A technical condition is needed to ensure the limsup is finite. -/
theorem Series.root_test_pos {s : Series}
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) < 1) : s.absConverges := by
    -- This proof is written to follow the structure of the original text.
    set α':EReal := atTop.limsup (fun n ↦ ↑(|s.seq n|^(1/(n:ℝ)):ℝ))
    have hpos : 0 ≤ α' := by
      apply le_limsup_of_frequently_le (Frequently.of_forall _) (by isBoundedDefault)
      intros; positivity
    set α := α'.toReal
    have hαα' : α' = α := by
      symm; apply coe_toReal
      . contrapose! h; simp [h]; exact le_top
      contrapose! hpos; simp [hpos]
    rw [hαα'] at h hpos; norm_cast at h hpos
    set ε := (1-α)/2
    have hε : 0 < ε := by simp [ε]; linarith
    have hε' : α' < (α+ε:ℝ) := by rw [hαα', EReal.coe_lt_coe_iff]; linarith
    have hα : α + ε < 1 := by simp [ε]; linarith
    have hα' : 0 < α + ε := by linarith
    have := eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
    rw [eventually_atTop] at this
    choose N' hN using this; set N := max N' (max s.m 1)
    have (n:ℤ) (hn: n ≥ N) : |s.seq n| ≤ (α + ε)^n := by
      have : n ≥ N' := by omega
      have npos : 0 < n := by omega
      specialize hN n this
      rw [EReal.coe_lt_coe_iff] at hN
      calc
        _ = (|s.seq n|^(1/(n:ℝ)))^n := by
          rw [←rpow_intCast, ←rpow_mul (by positivity)]
          symm; convert rpow_one _; field_simp
        _ ≤ _ := by
          convert pow_le_pow_left₀ (by positivity) (le_of_lt hN) n.toNat
          all_goals convert zpow_natCast _ _; omega
    set k := (N - s.m).toNat
    have hNk : N = s.m + k := by omega
    have hgeom : (fun n ↦ (α+ε) ^ n : Series).converges := by
      simp [converges_geom_iff, abs_of_pos hα', hα]
    rw [converges_from _ N.toNat] at hgeom
    have : (s.from N).absConverges := by
      apply (converges_of_le _ _ hgeom).1
      . simp; omega
      intro n hn; simp at hn
      have hn' : n ≥ 0 := by omega
      simp [hn.1, hn.2, hn']
      convert this n hn.2; symm; convert zpow_natCast _ _; omega
    unfold absConverges at this ⊢
    rw [converges_from _ k]; convert this; simp; refine ⟨ by omega, ?_ ⟩
    ext n
    by_cases hnm : n ≥ s.m <;> simp [hnm]
    by_cases hn: n ≥ N <;> simp [hn] <;> grind


/-- Theorem 7.5.1(b) (Root test) -/
theorem Series.root_test_neg {s : Series}
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) > 1) : s.diverges := by
    -- This proof is written to follow the structure of the original text.
    apply frequently_lt_of_lt_limsup (by isBoundedDefault) at h
    apply diverges_of_nodecay
    by_contra this; rw [LinearOrderedAddCommGroup.tendsto_nhds] at this; specialize this 1 (by positivity)
    choose n hn hs hs' using (h.and_eventually this).forall_exists_of_atTop 1
    simp at hs'; replace hs' := rpow_lt_one ?_ hs' (?_:0 < 1/(n:ℝ)) <;> try positivity
    rw [show (1:EReal) = (1:ℝ) by simp, EReal.coe_lt_coe_iff] at hs
    linarith

/-- Theorem 7.5.1(c) (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive: ∃ s:Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) ∧ s.diverges := by
    use (fun (n:ℕ) ↦ (1:ℝ):Series)
    split_ands
    . simp[Metric.tendsto_atTop]
      intro ε hε 
      use 0;intro n hn
      simp[hn,hε]
    apply diverges_of_nodecay
    by_contra;simp[Metric.tendsto_atTop] at this
    specialize this (0.5) (by linarith)
    choose N hconv using this
    specialize hconv (max N 0) (by simp)
    have : 0 ≤ max N 0 := by omega
    simp[this] at hconv;linarith

    /- . set t : {n // n > 0} → ℝ := fun n ↦ (n:ℝ) ^ (1 / (n:ℝ)) -/
    /-   have htr : Nonempty {n // n > 0} := by use 1;simp -/
    /-   suffices ht : Tendsto (fun n ↦  (t n) ^ (-2:ℤ)) atTop (nhds 1) from by -/
    /-     rw[Metric.tendsto_atTop ] at ht ⊢  -/
    /-     peel ht with ε hε hdist -/
    /-     obtain ⟨ ⟨N,hN⟩, hdist⟩ := hdist -/
    /-     use N; intro n hn -/
    /-     lift n to ℕ using by omega -/
    /-     specialize hdist ⟨n,(by omega)⟩ (by simp;omega) -/
    /-     convert hdist -/
    /-     simp[t,s];field_simp -/
    /-     rw[div_rpow (by simp) (by simp), one_rpow] -/
    /-     simp -/
    /-     rw[rpow_pow_comm] -/
    /-     simp -/
    /-   suffices ht1 : Tendsto t atTop (nhds 1) from by -/
    /-     rw[show (1:ℝ) = 1 ^ (-2:ℤ) by simp] -/
    /-     apply ht1.zpow₀;simp -/


/-- Lemma 7.5.2 / Exercise 7.5.1 -/
theorem Series.ratio_ineq {c:ℤ → ℝ} (m:ℤ) (hpos: ∀ n ≥ m, c n > 0) :
  atTop.liminf (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) ≤
    atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ))
  ∧ atTop.liminf (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) ≤
    atTop.limsup (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ))
  ∧ atTop.limsup (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) ≤
    atTop.limsup (fun n ↦ ↑(c (n+1) / c n:ℝ))
    := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, liminf_le_limsup ?_ ?_, ?_ ⟩ <;> try isBoundedDefault
  . 
    set ra := (fun n ↦ ((c (n+1) / c n:ℝ):EReal))
    set L' := liminf ra atTop
    by_cases hbot : L' = ⊥
    . 
      rw[hbot]
      exact bot_le
    rw[le_liminf_iff]
    intro  l' hl'
    by_cases hlb : l' = ⊥ 
    . simp[hlb]
    set l := l'.toReal
    have hl : l = l' := coe_toReal (ne_top_of_lt hl') hlb
    simp_rw[← hl,EReal.coe_lt_coe_iff,eventually_atTop]
    -- wipe out cases that l ≤ 0
    by_cases hl0 : l ≤ 0
    . 
      use m; peel hpos with n hn hpos
      apply lt_of_le_of_lt hl0
      apply rpow_pos_of_pos hpos
    choose r' hrl hrL using exists_between hl'
    set r := r'.toReal 
    have hrfin :  r' = r := by rw[coe_toReal (ne_top_of_lt hrL) (ne_bot_of_gt hrl)]
    rw[hrfin] at hrl hrL
    rw[← hl,EReal.coe_lt_coe_iff] at hrl
    set q := r / l
    have hq1 : q > 1 := by
      simp[q];rwa[one_lt_div₀ (by grind)]
    have hrp : r > 0 := by grind
    replace hrl : r = q * l := by grind
    have hra := eventually_lt_of_lt_liminf hrL
    rw[eventually_atTop] at hra
    choose N' hra using hra
    set N := max N' (max m 1)
    set A := c N * (r ^ (-N))
    simp at hl0
    have hac : ∀ n ≥ (N + 1), c n > A * r^n := by
      simp [ra] at hra
      intro n hn
      induction' n,hn using Int.le_induction with k hk hind
      . 
        simp[A]
        rw[zpow_add_one₀ (by grind)]
        field_simp
        specialize hra N (by omega)
        rwa[← lt_div_iff₀' (hpos N (by grind))]
      specialize hra k (by omega)
      rw[lt_div_iff₀' (hpos k (by grind))] at hra
      apply gt_trans hra
      rw[zpow_add_one₀ (by grind),← mul_assoc]
      apply mul_lt_mul_of_pos_right hind
      rw[hrl];positivity
    have hA : A >0 := by simp[A];apply mul_pos (hpos N (by omega)); positivity
    simp_rw[hrl,mul_zpow,← mul_assoc] at hac
    have  hqinv : q⁻¹ < 1:= by rw[inv_lt_one_iff₀];tauto
    have hqinv0 : q⁻¹ > 0 := by simp;grind
    have hNq := exists_pow_lt_of_lt_one hA hqinv
    choose Nq hNq using hNq
    replace hNq : ∀ n ≥ Nq, A * q ^ n > 1 := by
      intro n hn
      induction' n,hn using Nat.le_induction with k hk hind
      . simp; rw[← mul_inv_lt_iff₀ (by apply pow_pos; grind)]
        simp; rwa[← inv_pow]
      rw[pow_succ,← mul_assoc]
      apply one_lt_mul <;> grind
    use max Nq (N+1)
    intro n hn
    lift n to ℕ using by omega
    simp
    have hnp : n > 0 := by
      omega
    rw[lt_rpow_inv_iff_of_pos 
      (by positivity) 
      (by apply le_of_lt (hpos n (by omega))) 
      (by simp[hnp])
    ]
    simp
    specialize hac n (by omega)
    simp at hac
    specialize hNq n (by omega)
    apply lt_trans' hac
    apply lt_mul_left 
    apply pow_pos hl0
    assumption
  set L' := limsup (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) .atTop
  by_cases hL : L' = ⊤; · rw [hL]; exact le_top
  have hL'pos : 0 ≤ L' := by
    apply le_limsup_of_frequently_le'
    rw [frequently_atTop]
    intro N; use max N m, by omega
    have hpos1 := hpos (max N m) (by omega)
    have hpos2 := hpos ((max N m)+1) (by omega)
    positivity
  have why : L' ≠ ⊥ := by contrapose! hL'pos;simp[hL'pos]
  set L := L'.toReal
  have hL' : L' = L := (coe_toReal hL why).symm
  have hLpos : 0 ≤ L := by rw [hL'] at hL'pos; norm_cast at hL'pos
  apply le_of_forall_gt_imp_ge_of_dense
  intro y hy
  by_cases hy' : y = ⊤; · simp [hy']; exact le_top
  have : y = y.toReal := by symm; apply coe_toReal hy'; contrapose! hy; simp [hy]
  rw [this, hL', EReal.coe_lt_coe_iff] at hy
  set ε := y.toReal - L
  have hε : 0 < ε := by grind
  replace this : y = (L+ε:ℝ) := by convert this; simp [ε]
  rw [this]
  have hε' : L' < (L+ε:ℝ) := by rw [hL', EReal.coe_lt_coe_iff]; linarith
  have := eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
  rw [eventually_atTop] at this; choose N' hN using this
  set N := max N' (max m 1)
  have (n:ℤ) (hn: n ≥ N) : c (n+1) / c n ≤ (L + ε) := by
    have : n ≥ N' := by omega
    have npos : 0 < n := by omega
    specialize hN n this; norm_cast at hN; order
  set A := c N * (L+ε)^(-N)
  have hA : 0 < A := by specialize hpos N (by omega); positivity
  have why2 (n:ℤ) (hn: n ≥ N) : c n ≤ A * (L+ε)^n := by
    unfold A;rw[mul_assoc, ← zpow_add₀ (by grind)]
    induction' n, hn using Int.le_induction with k hk hind
    . simp
    specialize this k (by omega)
    rw[div_le_iff₀ (by apply hpos; omega)] at this
    apply le_trans this
    rwa[← add_assoc,zpow_add_one₀ (by grind),← mul_assoc,mul_comm, mul_le_mul_iff_left₀  (by grind)]
  have why2_root (n:ℤ) (hn: n ≥ N) : (((c n)^(1/(n:ℝ)):ℝ):EReal) ≤ (A^(1/(n:ℝ)) * (L+ε):ℝ) := by
    rw [EReal.coe_le_coe_iff]
    have hn' : n > 0 := by omega
    calc
      _ ≤ (A * (L+ε)^n)^(1/(n:ℝ)) := by
        apply_rules [rpow_le_rpow, le_of_lt (hpos n _)]; omega; positivity
      _ = A^(1/(n:ℝ)) * ((L+ε)^n)^(1/(n:ℝ)) := mul_rpow (by positivity) (by positivity)
      _ = _ := by
        congr
        rw [←rpow_intCast, ←rpow_mul (by positivity)]
        convert rpow_one _
        field_simp
  calc
    _ ≤ atTop.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)) * (L+ε):ℝ):EReal)) := by
      apply limsup_le_limsup <;> try isBoundedDefault
      unfold EventuallyLE; rw [eventually_atTop]
      use N
    _ ≤ (atTop.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)):ℝ):EReal))) * (atTop.limsup (fun n:ℤ ↦ ((L+ε:ℝ):EReal))) := by
      convert EReal.limsup_mul_le _ _ _ _ with n
      . rfl
      . apply Frequently.of_forall; intros; positivity
      . apply Eventually.of_forall; simp; positivity
      . simp [-coe_add]
      simp [-coe_add]; grind
    _ = (L+ε:ℝ) := by
      simp; convert one_mul _
      apply Tendsto.limsup_eq
      convert Tendsto.comp (f := fun n:ℤ ↦ (A ^ (n:ℝ)⁻¹)) (g := fun x:ℝ ↦ (x:EReal)) (y := nhds 1) _ _
      . apply continuous_coe_real_ereal.tendsto'; norm_num
      convert Tendsto.comp (f := fun n:ℤ ↦ (n:ℝ)⁻¹) (g := fun x:ℝ ↦ A^x) (y := nhds 0) _ _
      . apply (continuous_const_rpow (by positivity)).tendsto'; simp
      exact tendsto_inv_atTop_zero.comp tendsto_intCast_atTop_atTop
noncomputable abbrev Series.zeta_2 := (fun n:ℕ ↦ 1/(n+1:ℝ)^2 :Series)

lemma Series.zeta_2_ratio_converges : Tendsto (fun n ↦ |zeta_2.seq (n + 1)| / |zeta_2.seq n|) atTop (nhds 1) := by
  suffices h: atTop.Tendsto (fun (n:ℤ ) ↦ (1 - (1 / (n+2:ℝ)))^2) (nhds 1) from by
    apply h.congr'
    unfold EventuallyEq
    rw[eventually_atTop]
    use (0:ℤ); intro n hn; 
    simp[show 0 ≤ n+1 by omega]
    lift n to ℕ using hn
    simp;field_simp;
    rw[show (n:ℝ) + 2 - 1 = n+1 by linarith]
    norm_cast;ring
  nth_rw 3 [show (1:ℝ) = (1-0) ^ 2 by simp]
  apply Tendsto.pow
  apply Tendsto.const_sub
  rw[Metric.tendsto_atTop];intro ε hε 
  choose N hN hNε using exists_nat_pos_inv_lt hε 
  use N; intro n hn
  lift n to ℕ using by omega
  simp at hn
  simp;apply lt_trans' hNε  
  field_simp;norm_cast;omega
/-- Theorem 7.5.1 (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive' : ∃ s:Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) ∧ s.absConverges := by
    set s := zeta_2 
    use s;split_ands
    . -- tends to 1
      set c := fun n ↦ |s.seq n|
      change atTop.Tendsto (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ)) (nhds 1)
      suffices h: atTop.Tendsto (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) (nhds 1) from by
        have hinf := h.liminf_eq
        have hsup := h.limsup_eq
        have hpos : ∀ n ≥ s.m, c n > 0 := by
          simp[c,s];intro n hn
          lift n to ℕ using hn
          simp;norm_cast
        obtain ⟨hinfle, _, hlesup⟩ := ratio_ineq s.m hpos 
        rw[hinf] at hinfle
        rw[hsup] at hlesup
        have hereal := tendsto_of_le_liminf_of_limsup_le hinfle hlesup
        erw[tendsto_coe] at hereal
        assumption
      erw[tendsto_coe]
      exact zeta_2_ratio_converges

    -- abs_converges
    unfold absConverges 
    have heq : s.abs = s := by
      ext n<;>simp[s]
      split_ifs with hn <;> simp
    rw[heq]
    exact zeta_2_converges

/-- Corollary 7.5.3 (Ratio test)-/
theorem Series.ratio_test_pos {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.limsup (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) < 1) : s.absConverges := by
    apply Series.root_test_pos (lt_of_le_of_lt _ h)
    convert (ratio_ineq s.m _).2.2
    convert hnon using 1 with n
    simp

/-- Corollary 7.5.3 (Ratio test)-/
theorem Series.ratio_test_neg {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.liminf (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) > 1) : s.diverges := by
    apply Series.root_test_neg (lt_of_lt_of_le h _)
    convert (ratio_ineq s.m _).1.trans (ratio_ineq s.m _).2.1 with n; rfl
    all_goals convert hnon using 1 with n; simp

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive: ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.diverges := by
    use (fun (n:ℕ) ↦ (1:ℝ):Series)
    split_ands
    . 
      intro n hn;simp at hn
      simp[hn]
    . 
      simp;rw[Metric.tendsto_atTop]
      intro ε hε 
      use 0;intro n hn
      simp[hn,show 0 ≤ n+1 by omega,hε ]
    apply diverges_of_nodecay
    by_contra;simp[Metric.tendsto_atTop] at this
    specialize this (0.5) (by linarith)
    choose N hconv using this
    specialize hconv (max N 0) (by simp)
    have : 0 ≤ max N 0 := by omega
    simp[this] at hconv;linarith

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive' : ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.absConverges := by
    use zeta_2;split_ands
    . 
      intro n hn
      simp at hn
      lift n to ℕ using hn
      simp;norm_cast
    . 
      exact zeta_2_ratio_converges
    unfold absConverges 
    have heq : zeta_2.abs = zeta_2 := by
      ext n<;>simp
      split_ifs with hn <;> simp
    rw[heq]
    exact zeta_2_converges

/-- Proposition 7.5.4 -/
theorem Series.root_self_converges : atTop.Tendsto (fun (n:ℕ) ↦ (n:ℝ)^(1 / (n:ℝ))) (nhds 1) := by
  set c := fun (n:ℤ) ↦ (n:ℝ)
  suffices h : atTop.Tendsto (fun (n:ℤ) ↦ c n^ (1/(n:ℝ ))) (nhds 1) from by
    apply h.comp tendsto_natCast_atTop_atTop
  suffices h : atTop.Tendsto (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) (nhds 1) from by
    have hinf := h.liminf_eq
    have hsup := h.limsup_eq
    have hpos : ∀ n ≥ 1, c n > 0 := by
      simp[c];intro n hn
      lift n to ℕ using by omega
      simp;norm_cast at hn
    obtain ⟨hinfle, _, hlesup⟩ := ratio_ineq 1 hpos 
    rw[hinf] at hinfle
    rw[hsup] at hlesup
    have hereal := tendsto_of_le_liminf_of_limsup_le hinfle hlesup
    erw[tendsto_coe] at hereal
    assumption
  erw[tendsto_coe]
  simp[c];
  suffices h : atTop.Tendsto (fun (n:ℤ) ↦ (1 + (n:ℝ )⁻¹)) (nhds 1) from by
    apply h.congr'
    unfold EventuallyEq
    rw[eventually_atTop]
    use 1;intro x  hx 
    simp;field_simp
  nth_rw 2 [show (1:ℝ) = 1 + 0 by simp]
  apply Tendsto.const_add
  rw[Metric.tendsto_atTop];intro ε hε 
  choose N hN hNε using exists_nat_pos_inv_lt hε 
  use N; intro n hn
  lift n to ℕ using by omega
  simp at hn
  simp;apply lt_of_le_of_lt _ hNε 
  rw[inv_le_inv₀]
  <;> simp <;> omega

/-- Exercise 7.5.2 -/
theorem Series.poly_mul_geom_converges {x:ℝ} (hx: |x|<1) (q:ℝ) : (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series).converges
  ∧ atTop.Tendsto (fun n:ℕ ↦ (n:ℝ)^q * x^n) (nhds 0) := by
    set s := (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series)
    suffices hs: s.converges from by
      refine ⟨hs, ?_ ⟩
      have := decay_of_converges hs
      rw[Metric.tendsto_atTop] at this ⊢ 
      peel this with ε hε htends
      choose N htends using htends
      use N.toNat; intro n hn
      specialize htends n (by omega)
      simp[s] at htends
      simpa
    rw[converges_from _ 1];simp
    set s' := s.from (s.m + 1)
    by_cases hseq0 : ∃ n ≥ s'.m, s'.seq n = 0
    . simp[s',s] at hseq0
      choose n hn hseq0 using hseq0
      specialize hseq0 hn (by omega)
      lift n to ℕ using by omega
      simp at hseq0
      rw[rpow_eq_zero_iff_of_nonneg (by simp)] at hseq0
      have :(n:ℝ) ≠ 0 := by simp;omega
      have hx0 : x = 0 := by grind
      use 0; unfold convergesTo
      rw[tendsto_congr']; apply tendsto_const_nhds
      unfold EventuallyEq; rw[eventually_atTop]
      use 1; intro n' hn'
      induction' n',hn' using Int.le_induction with k hk hind
      . simp[s',s,Series.partial,hx0]
      rw[partial_succ',hind]
      simp[s',s,hx0]
      intro _ _;right;omega
    apply converges_of_absConverges
    push_neg at hseq0
    apply ratio_test_pos hseq0
    set x' := |x|
    suffices this : (atTop.Tendsto (fun n ↦ ((|s'.seq (n+1)| / |s'.seq n|:ℝ):EReal)) (nhds x') ) from by
      have := this.limsup_eq
      rw[this]
      norm_cast
    rw[tendsto_coe]
    suffices heveq : (fun n ↦ ((|s'.seq (n+1)| / |s'.seq n|:ℝ))) =ᶠ[atTop] (fun n ↦ (1+(n:ℝ)⁻¹ )^q * x') from by
      rw[tendsto_congr' heveq]
      nth_rw 2[show x' = (1 + 0)^q * x' by simp]
      apply Filter.Tendsto.mul_const
      apply Filter.Tendsto.rpow _ (tendsto_const_nhds) (by simp)
      apply Filter.Tendsto.const_add
      rw[Metric.tendsto_atTop]
      intro ε hε
      choose N hN hNε using exists_nat_pos_inv_lt hε 
      use N; intro n hn;lift n to ℕ using by omega
      simp;apply lt_of_le_of_lt _ hNε 
      rw[inv_le_inv₀  (by simp;omega) (by simp;omega)]
      simp_all
    unfold EventuallyEq 
    rw[eventually_atTop]
    use 1; intro n hn 
    have hn0 : n ≥ 0 := by omega
    have hn01 : 0 ≤ n+1 := by omega
    have hcoe1: (n+1).toNat = n+(1:ℝ) := by
      norm_cast;omega
    have hcoe2: (n.toNat) = (n:ℝ) := by
      norm_cast;omega
    simp[s',s,hn01,hn,hn0,hcoe1,hcoe2]
    have hpos1:  ((n:ℝ) +1) ^ q > 0 := by
      apply rpow_pos_of_pos
      norm_cast;omega
    have hpos2:  (n:ℝ)  ^ q > 0 := by
      apply rpow_pos_of_pos
      norm_cast
    rw[abs_of_pos hpos1]
    rw[abs_of_pos hpos2]
    repeat rw[← zpow_natCast]
    simp[hn01,hn0]
    field_simp
    have hx0 : |x| ≠ 0 := by
      contrapose hseq0
      simp;use 1;simp[s',s]
      simpa using hseq0
    rw[mul_div_assoc,← zpow_sub₀ hx0,← mul_rpow (by simp[hn0]) (by apply _root_.div_nonneg<;> norm_cast)]
    rw[← mul_div_assoc,mul_div_right_comm,_root_.div_self (by simp;omega)];simp
    simp[x']

end Chapter7
