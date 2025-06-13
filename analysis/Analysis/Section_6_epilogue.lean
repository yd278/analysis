import Mathlib.Tactic
import Analysis.Section_6_6

/-!
# Analysis I, Chapter 6 epilogue

In this (technical) epilogue, we show that various operations and properties we have defined for "Chapter 6" sequences `Chapter6.Sequence` are equivalent to Mathlib operations.  Note however that Mathlib's operations are defined in far greater generality than the setting of real-valued sequences, in particular using the language of filters.

-/

/-- Identification with the Cauchy sequence support in `Mathlib.Algebra.Order.CauSeq.Basic` -/
theorem Chapter6.Sequence.Cauchy_iff_CauSeq (a: ℕ → ℝ) : (a:Sequence).isCauchy ↔ IsCauSeq _root_.abs a := by
  simp_rw [isCauchy_of_coe, Real.dist_eq, IsCauSeq]
  constructor
  . intro h ε hε
    specialize h (ε/2) (half_pos hε)
    obtain ⟨ N, h ⟩ := h
    use N
    intro n hn
    specialize h n hn N (le_refl _)
    linarith
  intro h ε hε
  specialize h (ε/2) (half_pos hε)
  obtain ⟨ N, h ⟩ := h
  use N
  intro n hn m hm
  calc
    _ ≤ |a n - a N| + |a m - a N| := by rw [abs_sub_comm (a m) (a N)]; exact abs_sub_le _ _ _
    _ ≤ ε/2 + ε/2 := by apply le_of_lt; gcongr; exact h n hn; exact h m hm
    _ = _ := by linarith

/-- Identification with the Cauchy sequence support in `Mathlib.Topology.UniformSpace.Cauchy` -/
theorem Chapter6.Sequence.Cauchy_iff_CauchySeq (a: ℕ → ℝ) : (a:Sequence).isCauchy ↔ CauchySeq a := by
  rw [Cauchy_iff_CauSeq]
  convert isCauSeq_iff_cauchySeq

/-- Identifiction with `Filter.Tendsto` -/
theorem Chapter6.Sequence.tendsto_iff_Tendsto (a: ℕ → ℝ) (L:ℝ) : (a:Sequence).tendsTo L ↔ Filter.Tendsto a Filter.atTop (nhds L) := by
  rw [Metric.tendsto_atTop, tendsTo_iff]
  constructor
  . intro h ε hε
    specialize h (ε/2) (half_pos hε)
    obtain ⟨ N, hN ⟩ := h
    use N.toNat
    intro n hn
    specialize hN n (Int.toNat_le.mp hn)
    simp at hN
    rw [Real.dist_eq]
    linarith
  intro h ε hε
  specialize h ε hε
  obtain ⟨ N, hN ⟩ := h
  use N
  intro n hn
  have hpos : n ≥ 0 := LE.le.trans (by positivity) hn
  rw [ge_iff_le, ←Int.le_toNat hpos] at hn
  specialize hN n.toNat hn
  simp [hpos, ←Real.dist_eq]
  exact le_of_lt hN

theorem Chapter6.Sequence.converges_iff_Tendsto (a: ℕ → ℝ) : (a:Sequence).convergent ↔ ∃ L, Filter.Tendsto a Filter.atTop (nhds L) := by
  simp_rw [←tendsto_iff_Tendsto]

/-- A technicality: `CauSeq.IsComplete ℝ` was established for `_root_.abs` but not for `norm`. -/
instance inst_real_complete : CauSeq.IsComplete ℝ norm := by
  convert Real.instIsCompleteAbs

theorem Chapter6.Sequence.lim_eq_CauSeq_lim (a:ℕ → ℝ) (ha: (a:Sequence).isCauchy) :
    Chapter6.lim (a:Sequence) = CauSeq.lim  ⟨ a, (Cauchy_iff_CauSeq a).mp ha⟩ := by
  have h1 := CauSeq.tendsto_limit ⟨ a, (Cauchy_iff_CauSeq a).mp ha⟩
  have h2 := lim_def ((a:Sequence).Cauchy_iff_convergent.mp ha)
  rw [←tendsto_iff_Tendsto] at h1
  by_contra! h
  replace h := (a:Sequence).tendsTo_unique h
  tauto
