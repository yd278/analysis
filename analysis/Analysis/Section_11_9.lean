import Mathlib.Tactic
import Mathlib.Topology.Instances.Irrational
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
theorem cts_of_integ {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b)) :
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
    sorry
  exact ContinuousOn.ofUniformContinuousOn F this

theorem deriv_of_integ {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b))
  {x₀:ℝ} (hx₀ : x₀ ∈ Set.Icc a b) (hcts: ContinuousWithinAt f (Icc a b) x₀) :
  HasDerivWithinAt (fun x => integ f (Icc a x)) (f x₀) (Set.Icc a b) x₀ := by
  sorry


end Chapter11

-- note to self: remember to move Exercise 11.6.5 to Exercise 11.9.5
