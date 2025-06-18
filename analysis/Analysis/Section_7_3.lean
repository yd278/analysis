import Mathlib.Tactic
import Mathlib.Algebra.Field.Power
import Analysis.Section_6_1
import Analysis.Section_6_epilogue
import Analysis.Section_7_2

/-!
# Analysis I, Section 7.3

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

-
-/

namespace Chapter7

abbrev Series.nonneg (s : Series) : Prop := ∀ n, s.seq n ≥ 0

abbrev Series.partial_of_nonneg {s : Series} (h : s.nonneg) : Monotone s.partial := by sorry

/-- Proposition 7.3.1 -/
theorem Series.converges_of_nonneg_iff {s : Series} (h : s.nonneg) : s.converges ↔ ∃ M, ∀ N, s.partial N ≤ M := by
  -- This broadly follows the argument in the text, though for one direction I choose to use Mathlib routines rather than Chapter6 results.
  constructor
  . intro hconv
    set S : Chapter6.Sequence := ⟨ s.m, s.partial, by intro n hn; simp [Series.partial, hn] ⟩
    have : S.isBounded := by
      apply S.bounded_of_convergent
      rw [Chapter6.Sequence.converges_iff_Tendsto']
      convert hconv
    obtain ⟨ M, hpos, hM ⟩ := this
    use M; intro N; specialize hM N
    exact (le_abs_self _).trans hM
  intro hbound
  rcases tendsto_of_monotone (partial_of_nonneg h) with hinfin | hfin
  . obtain ⟨ M, hM ⟩ := hbound
    obtain ⟨ N, hN ⟩ := Filter.Eventually.exists (Filter.Tendsto.eventually_gt_atTop  hinfin M)
    specialize hM N
    linarith
  exact hfin

/-- Corollary 7.3.2 (Comparison test) / Exercise 7.3.1 -/
theorem Series.converges_of_le {s t : Series} (hm : s.m = t.m) (hcomp : ∀ n ≥ s.m, |s.seq n| ≤ t.seq n) (hconv : t.converges) : s.absConverges ∧ |s.sum| ≤ s.abs.sum ∧ s.abs.sum ≤ t.sum := by sorry

theorem Series.diverges_of_ge {s t : Series} (hm : s.m = t.m) (hcomp : ∀ n ≥ s.m, |s.seq n| ≤ t.seq n) (hdiv: ¬ s.absConverges) : t.diverges := by sorry

/-- Lemma 7.3.3 (Geometric series) / Exercise 7.3.2 -/
theorem Series.converges_geom (x : ℝ) (hx : |x| < 1) : (fun n ↦ x ^ n : Series).convergesTo (1 / (1 - x)) := by sorry

theorem Series.absConverges_geom (x : ℝ) (hx : |x| < 1) : (fun n ↦ x ^ n : Series).absConverges := by sorry

theorem Series.diverges_geom (x : ℝ) (hx : |x| ≥ 1) : (fun n ↦ x ^ n : Series).diverges := by sorry

/-- Proposition 7.3.4 (Cauchy criterion) -/
theorem Series.cauchy_criterion {s:Series} (hm: s.m = 1) (hs:s.nonneg) (hmono: ∀ n ≥ 1, s.seq (n+1) ≤ s.seq n) : s.converges ↔ (fun k ↦ 2^k * s.seq (2^k): Series).converges := by
  -- This proof is written to follow the structure of the original text.
  set t := (fun k ↦ 2^k * s.seq (2^k):Series)
  have ht: t.nonneg := by
    intro n
    by_cases h: n ≥ 0
    all_goals simp [t,h]
    exact hs _
  have htm : t.m = 0 := by simp [t]
  rw [converges_of_nonneg_iff hs, converges_of_nonneg_iff ht]
  set S := s.partial
  set T := t.partial
  have Lemma_7_3_6 (K:ℕ) : S (2^(K+1) - 1) ≤ T K ∧ T K ≤ 2 * S (2^K) := by
    sorry -- TODO
  constructor
  . intro h
    obtain ⟨ M, hM ⟩ := h
    use 2*M
    intro N; rcases lt_or_ge N 0 with hN | hN
    . simp [T, Series.partial, htm, hN]
      convert hM 0
      simp [S, Series.partial, hm]
    rw [Int.eq_natCast_toNat.mpr hN]
    apply (Lemma_7_3_6 N.toNat).2.trans
    gcongr
    exact hM _
  intro h
  obtain ⟨ M, hM ⟩ := h
  use M
  intro K'
  rcases lt_or_ge K' 1 with hK' | hK'
  . simp [S, Series.partial, hm, hK']
    convert hM (-1)
  set K := (K'-1).toNat
  have hK : K' = K + 1 := by
    rw [Int.toNat_of_nonneg (by linarith)]
    abel
  calc
    _ ≤ S (2 ^ (K+1) - 1) := by
      apply partial_of_nonneg hs
      rw [hK]
      generalize K = n
      induction' n with n hn
      . simp
      simp [pow_succ] at hn ⊢
      linarith
    _ ≤ T K := (Lemma_7_3_6 K).1
    _ ≤ M := hM K

/-- Corollary 7.3.7 -/
theorem Series.converges_qseries (q : ℝ) (hq : q > 1) : (fun n:ℕ ↦ 1 / (n:ℝ) ^ q : Series).converges := by
  -- This proof is written to follow the structure of the original text.
  sorry -- TODO

theorem Series.diverges_qseries (q : ℝ) (hpos: q > 0) (hq : q ≤ 1) : (fun n:ℕ ↦ 1 / (n:ℝ) ^ q : Series).diverges := by
  -- This proof is written to follow the structure of the original text.
  sorry -- TODO

/-- Exercise 7.3.3 -/
theorem Series.nonneg_sum_zero {a:ℕ → ℝ} (ha: (a:Series).nonneg) (hconv: (a:Series).converges) : (a:Series).sum = 0 ↔ ∀ n, a n = 0 := by sorry


end Chapter7
