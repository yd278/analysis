import Mathlib.Tactic
import Analysis.Section_7_4

/-!
# Analysis I, Section 7.5

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- The root and ratio tests

-/

namespace Chapter7

/-- Theorem 7.5.1 (Root test).  A technical condition `hbound` is needed to ensure the limsup is finite. -/
theorem Series.root_test_pos {s : Series}
  (hbound : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop fun n ↦ |s.seq n| ^ (1 / (n:ℝ)) )
  (h : Filter.limsup (fun n ↦ |s.seq n|^(1/(n:ℝ))) Filter.atTop < 1) : s.absConverges := by
    -- This proof is written to follow the structure of the original text.
    set α := Filter.limsup (fun n ↦ |s.seq n|^(1/(n:ℝ))) Filter.atTop
    have hpos : 0 ≤ α := by
      apply Filter.le_limsup_of_frequently_le _ hbound
      apply Filter.Frequently.of_forall
      intros; positivity
    set ε := (1-α)/2
    have hε : 0 < ε := by simp [ε]; linarith
    have hε' : α < α+ε := by linarith
    have hα : α + ε < 1 := by simp [ε]; linarith
    have hα' : 0 < α + ε := by linarith
    have := Filter.eventually_lt_of_limsup_lt hε' hbound
    rw [Filter.eventually_atTop] at this
    obtain ⟨ N', hN ⟩ := this
    set N := max N' (max s.m 1)
    have (n:ℤ) (hn: n ≥ N) : |s.seq n| ≤ (α + ε)^n := by
      have : n ≥ N' := by omega
      have npos : 0 < n := by omega
      specialize hN n this
      replace hN := le_of_lt hN
      calc
        _ = (|s.seq n|^(1/(n:ℝ)))^n := by
          rw [←Real.rpow_intCast, ←Real.rpow_mul (by positivity)]
          convert (Real.rpow_one _).symm
          field_simp
        _ ≤ _ := by
          convert pow_le_pow_left₀ (by positivity) hN n.toNat
          all_goals convert zpow_natCast _ _; omega
    set k := (N - s.m).toNat
    have hNk : N = s.m + k := by omega
    have hgeom : (fun n ↦ (α+ε) ^ n : Series).converges := by
      simp [converges_geom_iff, abs_of_pos hα', hα]
    replace hgeom := (converges_from _ N.toNat).mp hgeom
    have : (s.from N).absConverges := by
      apply (converges_of_le _ _ hgeom).1
      . simp; omega
      intro n hn
      simp [Series.from] at hn
      have hn' : n ≥ 0 := by omega
      simp [hn.1, hn.2, hn']
      convert this n hn.2
      convert (zpow_natCast _ _).symm
      omega
    unfold absConverges at this ⊢
    rw [converges_from _ k]
    convert this
    simp
    constructor
    . omega
    ext n
    by_cases hnm : n ≥ s.m
    all_goals simp [hnm]
    by_cases hn: n ≥ N
    all_goals simp [hn]; intros; omega


/-- Theorem 7.5.1 (Root test) -/
theorem Series.root_test_neg {s : Series}
  (hbound : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop fun n ↦ |s.seq n| ^ (1 / (n:ℝ)) )
  (h : Filter.limsup (fun n ↦ |s.seq n|^(1/(n:ℝ))) Filter.atTop > 1) : s.diverges := by
    -- This proof is written to follow the structure of the original text.
    sorry

/-- Theorem 7.5.1 (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive: ∃ s:Series,
  Filter.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) Filter.atTop (nhds 1) ∧ s.diverges := by
    sorry

/-- Theorem 7.5.1 (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive' : ∃ s:Series,
  Filter.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) Filter.atTop (nhds 1) ∧ s.absConverges := by
    sorry

/-- Lemma 7.5.2 / Exercise 7.5.1 -/
theorem Series.ratio_ineq {c:ℤ → ℝ} (m:ℤ) (hpos: ∀ n ≥ m, c n > 0) :
  Filter.liminf (fun n ↦ c (n+1) / c n) Filter.atTop ≤
    Filter.liminf (fun n ↦ (c n)^(1/(n:ℝ))) Filter.atTop
  ∧ Filter.liminf (fun n ↦ (c n)^(1/(n:ℝ))) Filter.atTop ≤
    Filter.limsup (fun n ↦ (c n)^(1/(n:ℝ))) Filter.atTop
  ∧ Filter.limsup (fun n ↦ (c n)^(1/(n:ℝ))) Filter.atTop ≤
    Filter.limsup (fun n ↦ c (n+1) / c n) Filter.atTop
    := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, ?_, ?_ ⟩
  . sorry
  . sorry -- TODO
  sorry -- TODO


/-- Corollary 7.5.3 (Ratio test)-/
theorem Series.ratio_test_pos {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : Filter.limsup (fun n ↦ |s.seq n+1| / |s.seq n|) Filter.atTop < 1) : s.absConverges := by
    -- This proof is written to follow the structure of the original text.
    sorry

/-- Corollary 7.5.3 (Ratio test)-/
theorem Series.ratio_test_neg {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : Filter.liminf (fun n ↦ |s.seq n+1| / |s.seq n|) Filter.atTop > 1) : s.diverges := by
    -- This proof is written to follow the structure of the original text.
    sorry

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive: ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  Filter.Tendsto (fun n ↦ |s.seq n+1| / |s.seq n|) Filter.atTop (nhds 1) ∧ s.diverges := by
    sorry

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive' : ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  Filter.Tendsto (fun n ↦ |s.seq n+1| / |s.seq n|) Filter.atTop (nhds 1) ∧ s.absConverges := by
    sorry

/-- Proposition 7.5.4 -/
theorem Series.root_self_converges : (fun (n:ℕ) ↦ (n:ℝ)^(1 / n : ℝ) : Series).convergesTo 1 := by
  -- This proof is written to follow the structure of the original text.
  sorry

/-- Exercise 7.5.2 -/
theorem Series.poly_mul_geom_converges {x:ℝ} (hx: |x|<1) (q:ℝ) : (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series).converges ∧ Filter.Tendsto (fun n:ℕ ↦ (n:ℝ)^q * x^n) Filter.atTop (nhds 0) := by
  sorry


end Chapter7
