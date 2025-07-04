import Mathlib.Tactic
import Mathlib.Topology.Instances.Irrational
import Analysis.Section_11_6

/-!
# Analysis I, Section 11.8

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Definition of α-length
- The piecewise constant Riemann-Stieltjes integral
- The full Riemann-Stieltjes integral

Technical notes:
- In Lean it is more convenient to make definitions such as α-length and the Riemann-Stieltjes
  integral totally defined, thus assigning "junk" values to the cases where the definition is
  not intended to be applied. For the definition of α-length, the definition is intended to be
  applied in contexts where left and right limits exist, and the function is extended by
  constants to the left and right of its intended domain of definition; for instance, if a
  function `f` is defined on `Icc 0 1`, then it is intended that `f x = f 1` for all `x ≥ 1`
  and `f x = f 0` for all `x ≤ 0`; in particular, at a right endpoint, the value of a function
  is intended to agree with its right limit, and similarly for the left endpoint, although we
  do not enforce this in our definition of α-length. (For functions defined on open intervals,
  the extension is immaterial.)
- The notion of α-length and piecewise constant Riemann-Stieltjes integral is intended for
  situations where left and right limits exist, such as for monotone functions or continuous
  functions, though technically they make sense without these hypotheses. The full Riemann-Stieltjes
  integral is intended for functions that are of bounded variation, though we shall restrict
  attention to the special case of monotone increasing functions for the most part.
-/

namespace Chapter11

open BoundedInterval Chapter9

/-- Left and right limits. A junk value is assigned if the limit does not exist. -/
noncomputable abbrev right_lim (f: ℝ → ℝ) (x₀:ℝ) : ℝ :=
  lim (Filter.map f (nhdsWithin x₀ (Set.Ioi x₀)))

noncomputable abbrev left_lim (f: ℝ → ℝ) (x₀:ℝ) : ℝ :=
  lim (Filter.map f (nhdsWithin x₀ (Set.Iio x₀)))

theorem right_lim_def {f: ℝ → ℝ} {x₀ L:ℝ} (h: Convergesto (Set.Ioi x₀) f L x₀) :
  right_lim f x₀ = L := by
  apply lim_eq
  rwa [Convergesto.iff, ←nhdsWithin.eq_1, Filter.Tendsto.eq_1] at h

theorem left_lim_def {f: ℝ → ℝ} {x₀ L:ℝ} (h: Convergesto (Set.Iio x₀) f L x₀) :
  left_lim f x₀ = L := by
  apply lim_eq
  rwa [Convergesto.iff, ←nhdsWithin.eq_1, Filter.Tendsto.eq_1] at h

noncomputable abbrev jump (f: ℝ → ℝ) (x₀:ℝ) : ℝ :=
  right_lim f x₀ - left_lim f x₀

/-- Right limits exist for continuous functions -/
theorem right_lim_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : ∃ ε>0, Set.Ico x₀ (x₀+ε) ⊆ X) (hf: ContinuousWithinAt f X x₀) :
  right_lim f x₀ = f x₀ := by
  obtain ⟨ ε, hε, hX ⟩ := h
  apply right_lim_def
  rw [ContinuousWithinAt.eq_1] at hf
  replace hf : Filter.Tendsto f (nhdsWithin x₀ (Set.Ioo x₀ (x₀ + ε))) (nhds (f x₀)) := by
    apply tendsto_nhdsWithin_mono_left _ hf
    exact Set.Ioo_subset_Ico_self.trans hX
  rw [Convergesto.iff, ←nhdsWithin.eq_1]
  convert hf using 1
  have h1 : Set.Ioo x₀ (x₀ + ε) ∈ nhdsWithin x₀ (Set.Ioi x₀) := by
    convert inter_mem_nhdsWithin (t := Set.Ioo (x₀-ε) (x₀+ε)) _ _
    . ext x; simp; intros; linarith
    exact Ioo_mem_nhds (by linarith) (by linarith)
  rw [←nhdsWithin_inter_of_mem h1]
  congr 1
  simp [Set.Ioo_subset_Ioi_self]

/-- Left limits exist for continuous functions -/
theorem left_lim_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : ∃ ε>0, Set.Ioc (x₀-ε) x₀ ⊆ X) (hf: ContinuousWithinAt f X x₀) :
  left_lim f x₀ = f x₀ := by
  obtain ⟨ ε, hε, hX ⟩ := h
  apply left_lim_def
  rw [ContinuousWithinAt.eq_1] at hf
  replace hf : Filter.Tendsto f (nhdsWithin x₀ (Set.Ioo (x₀ - ε) x₀)) (nhds (f x₀)) := by
    apply tendsto_nhdsWithin_mono_left _ hf
    exact Set.Ioo_subset_Ioc_self.trans hX
  rw [Convergesto.iff, ←nhdsWithin.eq_1]
  convert hf using 1
  have h1 : Set.Ioo (x₀-ε) x₀ ∈ nhdsWithin x₀ (Set.Iio x₀) := by
    convert inter_mem_nhdsWithin (t := Set.Ioo (x₀-ε) (x₀+ε)) _ _
    . ext x; simp; constructor
      . rintro ⟨ h1, h2 ⟩; simp [h1, h2]; linarith
      rintro ⟨ h1, h2, h3 ⟩; exact ⟨ h2, h1 ⟩
    exact Ioo_mem_nhds (by linarith) (by linarith)
  rw [←nhdsWithin_inter_of_mem h1]
  congr 1
  simp [Set.Ioo_subset_Iio_self]

/-- No jump for continuous functions -/
theorem jump_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : X ∈ nhds x₀) (hf: ContinuousWithinAt f X x₀) :
  jump f x₀ = 0 := by
  rw [mem_nhds_iff_exists_Ioo_subset] at h
  obtain ⟨ l, u, hx₀, hX ⟩ := h
  simp at hx₀
  have hl : ∃ ε>0, Set.Ioc (x₀-ε) x₀ ⊆ X := by
    refine ⟨ x₀-l, by linarith, ?_ ⟩
    apply Set.Subset.trans _ hX
    intro x hx; simp at hx ⊢; exact ⟨ hx.1, by linarith ⟩
  have hu : ∃ ε>0, Set.Ico x₀ (x₀+ε) ⊆ X := by
    refine ⟨ u-x₀, by linarith, ?_ ⟩
    apply Set.Subset.trans _ hX
    intro x hx; simp at hx ⊢; exact ⟨ by linarith, hx.2 ⟩
  simp [jump, left_lim_of_continuous hl hf, right_lim_of_continuous hu hf]

/-- Right limits exist for monotone functions -/
theorem right_lim_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  Convergesto (Set.Ioi x₀) f (sInf (f '' Set.Ioi x₀)) x₀ := by
  rw [Convergesto.iff, ←nhdsWithin.eq_1]
  apply MonotoneOn.tendsto_nhdsGT
  . exact Monotone.monotoneOn hf _
  rw [bddBelow_def]
  use f x₀
  intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy
  apply hf; linarith

theorem right_lim_of_monotone' {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  right_lim f x₀ = sInf (f '' Set.Ioi x₀) := by
  apply right_lim_def
  apply right_lim_of_monotone x₀ hf

/-- Left limits exist for monotone functions -/
theorem left_lim_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  Convergesto (Set.Iio x₀) f (sSup (f '' Set.Iio x₀)) x₀ := by
  rw [Convergesto.iff, ←nhdsWithin.eq_1]
  apply MonotoneOn.tendsto_nhdsLT
  . exact Monotone.monotoneOn hf _
  rw [bddAbove_def]
  use f x₀
  intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy
  apply hf; linarith

theorem left_lim_of_monotone' {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  left_lim f x₀ = sSup (f '' Set.Iio x₀) := by
  apply left_lim_def
  apply left_lim_of_monotone x₀ hf

theorem jump_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  0 ≤ jump f x₀  := by
  simp [jump, left_lim_of_monotone' x₀ hf, right_lim_of_monotone' x₀ hf]
  apply csSup_le
  . simp
  intro a ha
  apply le_csInf
  . simp
  intro b hb
  simp at ha hb
  obtain ⟨ x, hx, rfl ⟩ := ha
  obtain ⟨ y, hy, rfl ⟩ := hb
  apply hf; linarith

theorem right_lim_le_left_lim_of_monotone {f:ℝ → ℝ} {a b:ℝ} (hab: a < b)
  (hf: Monotone f) :
  right_lim f a ≤ left_lim f b := by
  rw [left_lim_of_monotone' b hf, right_lim_of_monotone' a hf]
  calc
    _ ≤ f ((a+b)/2) := by
      apply ConditionallyCompleteLattice.csInf_le _ _ _ _
      . rw [bddBelow_def]
        use f a
        intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy
        apply hf; linarith
      simp; use (a+b)/2; simp; linarith
    _ ≤ _ := by
      apply ConditionallyCompleteLattice.le_csSup _ _ _ _
      . rw [bddAbove_def]
        use f b
        intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy
        apply hf; linarith
      simp; use (a+b)/2; simp; linarith

/-- Definition 11.8.1 -/
noncomputable abbrev α_length (α: ℝ → ℝ) (I: BoundedInterval) : ℝ := match I with
| Icc a b => if a ≤ b then (right_lim α b) - (left_lim α a) else 0
| Ico a b => if a ≤ b then (left_lim α b) - (left_lim α a) else 0
| Ioc a b => if a ≤ b then (right_lim α b) - (right_lim α a) else 0
| Ioo a b => if a < b then (left_lim α b) - (right_lim α a) else 0

notation3:max α"["I"]ₗ" => α_length α I

theorem α_length_of_empty {α: ℝ → ℝ} {I: BoundedInterval} (hI: (I:Set ℝ) = ∅) : α[I]ₗ = 0 :=
  match I with
  | Icc a b => by
      simp [Set.Icc_eq_empty_iff] at hI ⊢
      intros; linarith
  | Ico a b => by
      simp [Set.Ico_eq_empty_iff] at hI ⊢
      intros; have : a = b := by linarith
      simp [this]
  | Ioc a b => by
      simp [Set.Ioc_eq_empty_iff] at hI ⊢
      intros; have : a = b := by linarith
      simp [this]
  | Ioo a b => by
      simp [Set.Ioo_eq_empty_iff] at hI ⊢
      intros; linarith












end Chapter11
