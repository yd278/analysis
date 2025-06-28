import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_11_2

/-!
# Analysis I, Section 11.3

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.


-/

namespace Chapter11
open BoundedInterval Chapter9

/-- Definition 11.3.1 (Majorization of functions) -/
abbrev MajorizesOn (g f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∀ x ∈ (I:Set ℝ), f x ≤ g x

abbrev MinorizesOn (g f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∀ x ∈ (I:Set ℝ), g x ≤ f x

/-- Definition 11.3.2 (Uppper and lower Riemann integrals )-/
noncomputable abbrev upper_integral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ :=
  sInf ((fun g ↦ PiecewiseConstantOn.integ g I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})

noncomputable abbrev lower_integral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ :=
  sSup ((fun g ↦ PiecewiseConstantOn.integ g I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})

/-- Lemma 11.3.3 -/
lemma integral_bounds {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) :
  -M * |I|ₗ ≤ lower_integral f I ∧
  lower_integral f I ≤ upper_integral f I ∧
  upper_integral f I ≤ M * |I|ₗ := by
  -- This proof is modified slightly from the original text.
  set A := ((fun g ↦ PiecewiseConstantOn.integ g I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})
  set B := ((fun g ↦ PiecewiseConstantOn.integ g I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})
  have h1 : M * |I|ₗ ∈ A := by
    simp [A]
    refine ⟨ fun _ ↦ M , ⟨ ⟨ ?_, ?_, ⟩, ?_ ⟩ ⟩
    . intro x hx
      specialize h x hx
      simp [abs_le'] at h
      simp [h.1]
    . apply PiecewiseConstantOn.of_const (ConstantOn.of_const (c := M) _)
      simp
    exact PiecewiseConstantOn.integ_const M I
  have h2 : -M * |I|ₗ ∈ B := by
    simp [B]
    refine ⟨ fun _ ↦ -M , ⟨ ⟨ ?_, ?_, ⟩, ?_ ⟩ ⟩
    . intro x hx
      specialize h x hx
      simp [abs_le'] at h
      simp; linarith
    . apply PiecewiseConstantOn.of_const (ConstantOn.of_const (c := -M) _)
      simp
    convert PiecewiseConstantOn.integ_const (-M) I using 1
    simp
  have h3 {a b:ℝ} (ha: a ∈ A) (hb: b ∈ B) : b ≤ a := by
    simp [A,B] at ha hb
    obtain ⟨ g, ⟨ ⟨ hmaj, hgp⟩, hgi ⟩ ⟩ := ha
    obtain ⟨ h, ⟨ ⟨ hmin, hhp⟩, hhi ⟩ ⟩ := hb
    rw [←hgi, ←hhi]
    apply PiecewiseConstantOn.integ_mono _ hhp hgp
    intro x hx
    apply (ge_iff_le.mp (hmin x hx)).trans (hmaj x hx)
  have hA: BddBelow A := by
    rw [bddBelow_def]
    use -M * |I|ₗ
    intro a ha; exact h3 ha h2
  have hB: BddAbove B := by
    rw [bddAbove_def]
    use M * |I|ₗ
    intro b hb; exact h3 h1 hb
  refine ⟨ ?_, ?_, ?_ ⟩
  . apply ConditionallyCompleteLattice.le_csSup _ _ hB h2
  . apply ConditionallyCompleteLattice.csSup_le _ _ (Set.nonempty_of_mem h2) _
    rw [mem_upperBounds]
    intro b hb
    apply ConditionallyCompleteLattice.le_csInf _ _ (Set.nonempty_of_mem h1) _
    rw [mem_lowerBounds]
    intro a ha
    exact h3 ha hb
  apply ConditionallyCompleteLattice.csInf_le _ _ hA h1

/-- Definition 11.3.4 (Riemann integral)
As we permit junk values, the simplest definition for the Riemann integral is the upper integral.-/
noncomputable abbrev integ (f:ℝ → ℝ) (I: BoundedInterval) : ℝ :=
upper_integral f I

noncomputable abbrev integrable (f:ℝ → ℝ) (I: BoundedInterval) : Prop :=
  BddOn f I ∧ lower_integral f I = upper_integral f I

/-- Lemma 11.3.7 / Exercise 11.3.3 -/
theorem integ_of_piecewise_const {f:ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I) :
  integrable f I ∧ integ f I = PiecewiseConstantOn.integ f I := by
  sorry

/-- Remark 11.3.8 -/
theorem integ_on_subsingleton {f:ℝ → ℝ} {I: BoundedInterval} (hI: |I|ₗ = 0) :
  integrable f I ∧ integ f I = 0 := by
  convert integ_of_piecewise_const _
  . sorry -- TODO
  sorry -- TODO


end Chapter11
