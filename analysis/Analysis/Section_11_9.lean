import Mathlib.Tactic
import Mathlib.Topology.Instances.Irrational
import Analysis.Section_9_4
import Analysis.Section_9_8
import Analysis.Section_10_1
import Analysis.Section_11_6
import Analysis.Section_11_8

/-!
# Analysis I, Section 11.9

I have attempted to make the translation as faithful a paraphrasing as possible of the
original text. When there is a choice between a more idiomatic Lean solution and a
more faithful translation, I have generally chosen the latter. In particular, there will
be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I
have consciously avoided doing so.

Main constructions and results of this section:
-
-/

namespace Chapter11
open Chapter9 BoundedInterval

/-- Theorem 11.9.1 (First Fundamental Theorem of Calculus)-/
theorem cts_of_integ {a b:ℝ} {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b)) :
  ContinuousOn (fun x => integ f (Icc a x)) (Set.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  set F : ℝ → ℝ := fun x => integ f (Icc a x)
  obtain ⟨ M, hM ⟩ := hf.1
  have {x y:ℝ} (hxy: x < y) (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) : |F y - F x| ≤ M * (y - x) := by
    simp at hx hy
    have := (integ_of_join (join_Icc_Ioc hy.1 hy.2) hf).1
    replace := (integ_of_join (join_Icc_Ioc hx.1 (le_of_lt hxy)) this).2
    simp [F, this.2, abs_le']
    constructor
    . convert integ_mono (g := fun _ ↦ M) this.1 (integ_of_const _ _).1 _
      . simp [integ_of_const, le_of_lt hxy]
      intro z hz
      specialize hM z ?_
      . simp at hz ⊢
        exact ⟨ by linarith, by linarith ⟩
      rw [abs_le'] at hM; simp [hM]
    rw [neg_le]
    convert integ_mono (f := fun _ ↦ -M) (integ_of_const _ _).1 this.1 _
    . simp [integ_of_const, le_of_lt hxy]
    intro z hz
    specialize hM z ?_
    . simp at hz ⊢
      exact ⟨ by linarith, by linarith ⟩
    rw [abs_le'] at hM; simp; linarith
  replace {x y:ℝ} (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) :
    |F y - F x| ≤ M * |x-y| := by
    rcases lt_trichotomy x y with h | h | h
    . simp [abs_of_neg (show x-y < 0 by linarith), this h hx hy]
    . simp [h]
    . simp [abs_of_pos (show 0 < x-y by linarith), abs_sub_comm, this h hy hx]
  replace : UniformContinuousOn F (Set.Icc a b) := by
    simp [Metric.uniformContinuousOn_iff, Real.dist_eq, -Set.mem_Icc]
    intro ε hε
    use (ε/(max M 1)), (by positivity)
    intro x hx y hy hxy
    calc
      _ = |F y - F x| := by rw [abs_sub_comm]
      _ ≤ M * |x-y| := this hx hy
      _ ≤ (max M 1) * |x-y| := by gcongr; exact le_max_left _ _
      _ < (max M 1) * (ε / (max M 1)) := by gcongr
      _ = _ := by field_simp
  exact ContinuousOn.ofUniformContinuousOn F this

theorem deriv_of_integ {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b))
  {x₀:ℝ} (hx₀ : x₀ ∈ Set.Icc a b) (hcts: ContinuousWithinAt f (Icc a b) x₀) :
  HasDerivWithinAt (fun x => integ f (Icc a x)) (f x₀) (Set.Icc a b) x₀ := by
  -- This proof is written to follow the structure of the original text.
  rw [HasDerivWithinAt.iff_approx_linear]
  intro ε hε
  simp [(ContinuousWithinAt.tfae _ f hx₀).out 0 2] at hcts
  specialize hcts ε hε
  obtain ⟨ δ, hδ, hconv ⟩ := hcts
  use δ, hδ
  intro y hy hyδ
  rcases lt_trichotomy x₀ y with hx₀y | hx₀y | hx₀y
  . have := (integ_of_join (join_Icc_Ioc hy.1 hy.2) hf).1
    replace := (integ_of_join (join_Icc_Ioc hx₀.1 (le_of_lt hx₀y)) this).2
    simp [this.2, abs_le', abs_of_pos (show 0 < y - x₀ by linarith)]
    have h1 := integ_mono (g := fun _ ↦ f x₀ + ε) this.1 (integ_of_const _ _).1 ?_
    have h2 := integ_mono (f := fun _ ↦ f x₀ - ε) (integ_of_const _ _).1 this.1 ?_
    simp [integ_of_const, le_of_lt hx₀y, BoundedInterval.a, BoundedInterval.b] at h1 h2
    constructor
    . convert h1 using 1; ring
    . simp [←sub_nonneg] at h2 ⊢
      convert h2 using 1; ring
    . intro z hz
      simp at hz hy hx₀
      simp_rw [abs_lt] at hyδ hconv
      specialize hconv z (by linarith) (by linarith) ⟨ by linarith, by linarith ⟩
      simp; linarith
    intro z hz
    simp at hz hy hx₀
    simp_rw [abs_lt] at hyδ hconv
    specialize hconv z (by linarith) (by linarith) ⟨ by linarith, by linarith ⟩
    simp; linarith
  . simp [hx₀y]
  sorry

/-- Example 11.9.2 -/
theorem IntegrableOn.of_f_9_8_5 : IntegrableOn f_9_8_5 (Icc 0 1) := by
  apply integ_of_monotone
  apply StrictMonoOn.monotoneOn
  exact StrictMonoOn.mono StrictMonoOn.of_f_9_8_5 (by simp)

noncomputable abbrev F_11_9_2 := fun x ↦ integ f_9_8_5 (Icc 0 x)

theorem ContinuousOn.of_F_11_9_2 : ContinuousOn F_11_9_2 (Set.Icc 0 1) := by
  apply cts_of_integ
  exact IntegrableOn.of_f_9_8_5

theorem DifferentiableOn.of_F_11_9_2 {x:ℝ} (hx: ¬ ∃ r:ℚ, x = r) (hx': x ∈ Set.Icc 0 1) :
  DifferentiableWithinAt ℝ F_11_9_2 (Set.Icc 0 1) x := by
  have := deriv_of_integ (show 0 < 1 by norm_num) IntegrableOn.of_f_9_8_5 hx'
     (ContinuousAt.continuousWithinAt (ContinuousAt.of_f_9_8_5 hx))
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt] at this
  use (ContinuousLinearMap.smulRight (1:ℝ →L[ℝ] ℝ) (f_9_8_5 x))

/-- Definition 11.9.3.  We drop the requirement that x be a limit point as this makes
    the Lean arguments slightly cleaner -/
abbrev AntiderivOn (F f: ℝ → ℝ) (I: BoundedInterval) :=
  DifferentiableOn ℝ F I ∧ ∀ x ∈ I, HasDerivWithinAt F (f x) I x

/-- Theorem 11.9.4 (Second Fundamental Theorem of Calculus) -/
theorem integ_eq_antederiv_sub {a b:ℝ} (h:a ≤ b) {f F: ℝ → ℝ}
  (hf: IntegrableOn f (Icc a b)) (hF: AntiderivOn F f (Icc a b)) :
  integ f (Icc a b) = F b - F a := by

  -- This proof is written to follow the structure of the original text.
  rcases lt_or_eq_of_le h with h | h
  . have hF_cts : ContinuousOn F (Set.Icc a b) := by
      intro x hx
      apply ContinuousWithinAt.of_differentiableWithinAt
      exact hF.1 x hx
    -- for technical reasons we need to extend F by constant outside of Icc a b
    let F' : ℝ → ℝ := fun x ↦
      if x ∈ Set.Icc a b then F x else
        if x < a then F a else F b

    have hF'_cts : ContinuousOn F' (Ioo (a-1) (b+1)) := by
      sorry

    have hupper (P: Partition (Icc a b)) : upper_riemann_sum f P ≥ F b - F a := by
      have := Partition.sum_of_α_length P F'
      calc
        _ ≥ ∑ J ∈ P.intervals, F'[J]ₗ := by
          apply Finset.sum_le_sum
          intro J hJ
          by_cases hJ_empty : (J:Set ℝ) = ∅
          . simp [α_length_of_empty _ hJ_empty, length_of_empty hJ_empty]
          rcases le_or_gt J.b J.a with hJab | hJab
          . push_neg at hJ_empty
            obtain ⟨ x, hx ⟩ := hJ_empty
            cases J with
            | Ioo a' b' => simp at hx; linarith
            | Ioc a' b' => simp at hx; linarith
            | Ico a' b' => simp at hx; linarith
            | Icc a' b' =>
              simp at hx
              have : a' = b' := by linarith
              simp [this]
              have hnhds: (Ioo (a-1) (b+1):Set ℝ) ∈ nhds b' := by
                replace hJ := P.contains _ hJ
                simp [subset_iff] at hJ
                rw [Set.Icc_subset_Icc_iff (by linarith)] at hJ
                apply Ioo_mem_nhds <;> linarith
              rw [α_length_of_pt, jump_of_continuous hnhds (hF'_cts _ (mem_of_mem_nhds hnhds))]
          sorry
        _ = F'[Icc a b]ₗ := Partition.sum_of_α_length P F'
        _ = F' b - F' a := by
          apply α_length_of_cts (by linarith) _ (by linarith) _ hF'_cts
          simp [h]
          intro x hx; simp [mem_iff] at hx ⊢; exact ⟨ by linarith, by linarith ⟩
        _ = _ := by
          simp [F', le_of_lt h]
    have hlower (P: Partition (Icc a b)) : lower_riemann_sum f P ≤ F b - F a := by
      sorry
    replace hupper : upper_integral f (Icc a b) ≥ F b - F a := by
      rw [upper_integ_eq_inf_upper_sum hf.1]
      apply le_csInf
      . simp [Set.range_nonempty]
      simp
      intro P; specialize hupper P; linarith
    replace hlower : lower_integral f (Icc a b) ≤ F b - F a := by
      rw [lower_integ_eq_sup_lower_sum hf.1]
      apply csSup_le
      . simp [Set.range_nonempty]
      simp
      intro P; specialize hlower P; linarith
    replace hf := hf.2
    linarith
  simp [h]
  apply (integ_on_subsingleton _).2
  simp [length]





end Chapter11

-- note to self: remember to move Exercise 11.6.5 to Exercise 11.9.5
