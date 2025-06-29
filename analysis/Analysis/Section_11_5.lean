import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_11_4

/-!
# Analysis I, Section 11.5

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Basic properties of the Riemann integral

-/

namespace Chapter11




/-- Exercise 11.5.2 -/
theorem integ_zero {a b:ℝ} (hab: a ≤ b) (f: ℝ → ℝ) (hf: ContinuousOn f (Icc a b))
  (hnonneg: MajorizesOn f (fun _ ↦ 0) (Icc a b)) (hinteg : integ f (Icc a b) = 0) :
  ∀ x ∈ Icc a b, f x = 0 := by
    sorry

end Chapter11
