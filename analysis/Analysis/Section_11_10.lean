import Mathlib.Tactic
import Analysis.Section_11_9


/-!
# Analysis I, Section 11.9

I have attempted to make the translation as faithful a paraphrasing as possible of the
original text. When there is a choice between a more idiomatic Lean solution and a
more faithful translation, I have generally chosen the latter. In particular, there will
be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I
have consciously avoided doing so.

Main constructions and results of this section:
- Integration by parts

-/

namespace Chapter11

open BoundedInterval

/-- Proposition 11.10.1 (Integration by parts formula) / Exercise 11.10.1 -/
theorem integ_of_mul_deriv {a b:ℝ} (hab: a ≤ b) {F G: ℝ → ℝ}
  (hF: DifferentiableOn ℝ F (Icc a b)) (hG : DifferentiableOn ℝ G (Icc a b))
  (hF': IntegrableOn (derivWithin F (Icc a b)) (Icc a b))
  (hG': IntegrableOn (derivWithin G (Icc a b)) (Icc a b)) :
  integ (F * derivWithin G (Icc a b)) (Icc a b) = F b * G b - F a * G a -
    integ (G * derivWithin F (Icc a b)) (Icc a b) := by
    sorry

/-- Theorem 11.10.2.  Need to add continuity of α due to our conventions on α-length -/
theorem RS_integ_eq_integ_of_mul_deriv
  {a b:ℝ} {α f:ℝ → ℝ} (hα: Monotone α)
  (hα_diff: DifferentiableOn ℝ α (Icc a b)) (hαcont: Continuous α)
  (hα': IntegrableOn (derivWithin α (Icc a b)) (Icc a b))
  (hf: PiecewiseConstantOn f (Icc a b)) :
  IntegrableOn (f * derivWithin α (Icc a b)) (Icc a b) ∧
  integ (f * derivWithin α (Icc a b)) (Icc a b) = RS_integ f (Icc a b) α := by
  -- This proof is adapted from the structure of the original text.
  have hf_integ: IntegrableOn f (Icc a b) :=
    (integ_of_piecewise_const hf).1
  have hfα'_integ: IntegrableOn (f * derivWithin α (Icc a b)) (Icc a b) :=
    integ_of_mul hf_integ hα'
  refine ⟨ hfα'_integ, ?_ ⟩
  rw [(RS_integ_of_piecewise_const hf hα).2]
  obtain ⟨ P, hP ⟩ := hf
  rw [PiecewiseConstantOn.RS_integ_def hP α, integ_split hfα'_integ P]
  unfold PiecewiseConstantWith.RS_integ
  apply Finset.sum_congr rfl
  intro J hJ
  calc
    _ = integ ((constant_value_on f (J:Set ℝ)) • derivWithin α (Icc a b)) J := by
      apply integ_congr
      intro x hx
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; congr
      apply ConstantOn.eq _ hx
      exact hP J hJ
    _ = constant_value_on f (J:Set ℝ) * integ (derivWithin α (Icc a b)) J := by
      convert (integ_of_smul _ _).2
      apply integ_mono' (P.contains _ hJ) hα'
    _ = _ := by
      congr
      have hJsub (hJab : J.a ≤ J.b) : J ⊆ Ioo (J.a - 1) (J.b + 1) := by
        apply (subset_Icc J).trans
        simp [subset_iff, Set.Icc_subset_Ioo_iff hJab]
      rcases le_iff_eq_or_lt.mp (length_nonneg J) with hJab | hJab
      . rw [(integ_on_subsingleton hJab.symm).2]
        simp [le_iff_lt_or_eq] at hJab
        rcases hJab with hJab | hJab
        . rw [α_length_of_empty _ (empty_of_lt hJab)]
        rw [α_length_of_cts (show J.a-1 < J.a by linarith) (by linarith) (show J.b < J.b+1 by linarith) (hJsub (by linarith)) (Continuous.continuousOn hαcont) ]
        simp [show J.a = J.b by linarith]
      simp [length] at hJab
      rw [α_length_of_cts (show J.a-1 < J.a by linarith) (le_of_lt hJab) (show J.b < J.b+1 by linarith) (hJsub (le_of_lt hJab)) (Continuous.continuousOn hαcont) ]
      . have : Icc J.a J.b ⊆ Icc a b := by
          have := (Ioo_subset J).trans (P.contains _ hJ)
          simp [subset_iff] at this
          replace := closure_mono this
          simp [closure_Ioo (show J.a ≠ J.b by linarith)] at this
          simp [subset_iff, this]
        calc
          _ = integ (derivWithin α (Icc a b)) (Icc J.a J.b) :=
            integ_eq (subset_Icc J) rfl rfl (integ_mono' this hα')
          _ = _ := by
            convert integ_eq_antideriv_sub (le_of_lt hJab) (integ_mono' this hα') _
            apply AntiderivOn.mono (I := Icc a b) ⟨ hα_diff, _ ⟩ this
            intro x hx
            exact DifferentiableWithinAt.hasDerivWithinAt (hα_diff x hx)



end Chapter11
