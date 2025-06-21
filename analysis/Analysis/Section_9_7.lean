import Mathlib.Tactic
import Analysis.Section_9_3
import Analysis.Section_9_4


/-!
# Analysis I, Section 9.7

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The intermediate value theorem
-/

namespace Chapter9

/-- Theorem 9.7.1 (Intermediate value theorem) -/
theorem intermediate_value {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (Set.Icc a b)) {y:ℝ} (hy: y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f a) (f b)) :
  ∃ c ∈ Set.Icc a b, f c = y := by
  -- This proof is written to follow the structure of the original text.
  rcases hy with hy_left | hy_right
  . by_cases hya : y = f a
    . use a; simp [hya, hab]
    by_cases hyb : y = f b
    . use b; simp [hyb, hab]
    simp at hy_left
    replace hya : f a < y := by contrapose! hya; linarith
    replace hyb : y < f b := by contrapose! hyb; linarith
    set E := {x | x ∈ Set.Icc a b ∧ f x < y}
    have hE : E ⊆ Set.Icc a b := by
      rintro x ⟨hx₁, hx₂⟩; exact ⟨x, hx₁⟩
    have hE_bdd : BddAbove E := BddAbove.mono hE bddAbove_Icc
    have hE_nonempty : E.Nonempty := by
      use a; split; simp [hya, hab]
    set c := sSup E
    have hc : c ∈ Set.Icc a b := by
      simp at hc
      constructor
      . sorry -- TODO
      sorry -- TODO
    use c, hc
    have hfc_upper : f c ≤ y := by
      sorry -- TODO
    have hfc_lower : y ≤ f c := by
      sorry -- TODO
    linarith
  sorry

open Classical in
noncomputable abbrev f_9_7_1 : ℝ → ℝ := fun x ↦ if x ≤ 0 then -1 else 1

example : 0 ∈ Set.Icc (f_9_7_1 (-1)) (f_9_7_1 1) ∧ ¬ ∃ x ∈ Set.Icc (-1) 1, f_9_7_1 x = 0 := by
  sorry

/-- Remark 9.7.2 -/
abbrev f_9_7_2 : ℝ → ℝ := fun x ↦ x^3 - x

example : f_9_7_2 (-2) = -6 := by sorry
example : f_9_7_2 2 = 6 := by sorry
example : f_9_7_2 (-1) = 0 := by sorry
example : f_9_7_2 0 = 0 := by sorry
example : f_9_7_2 1 = 0 := by sorry

/-- Remark 9.7.3 -/
example : ∃ x:ℝ, 0 ≤ x ∧ x ≤ 2 ∧ x^2 = 2 := by sorry

/-- Corollary 9.7.4 (Images of continuous functions) / Exercise 9.7.1 -/
theorem continuous_image_Icc {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (Set.Icc a b)) {y:ℝ} (hy: sInf (f '' Set.Icc a b) ≤ y ∧ y ≤ sSup (f '' Set.Icc a b)) : ∃ c ∈ Set.Icc a b, f c = y := by
  sorry

theorem continuous_image_Icc' {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (Set.Icc a b)) : f '' Set.Icc a b = Set.Icc (sInf (f '' Set.Icc a b)) (sSup (f '' Set.Icc a b)) := by
  sorry

/-- Exercise 9.7.2 -/
theorem exists_fixed_pt {f:ℝ → ℝ} (hf: ContinuousOn f (Set.Icc 0 1)) (hmap: f '' Set.Icc 0 1 ⊆ Set.Icc 0 1) : ∃ x ∈ Set.Icc 0 1, f x = x := by
  sorry

end Chapter9
