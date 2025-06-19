import Mathlib.Tactic
import Analysis.Section_7_4

/-!
# Analysis I, Section 7.5

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- The root and ratio tests

-/

namespace Chapter7

/-- Theorem 7.5.1 (Root test) -/
theorem Series.root_test_pos {s : Series}
  (h : Filter.limsup (fun n ↦ |s.seq n|^(1/(n:ℝ))) Filter.atTop < 1) : s.absConverges := by
    -- This proof is written to follow the structure of the original text.
    sorry

/-- Theorem 7.5.1 (Root test) -/
theorem Series.root_test_neg {s : Series}
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
