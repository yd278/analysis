import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_11_3

/-!
# Analysis I, Section 11.4

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Basic properties of the Riemann integral

-/

namespace Chapter11

/-- Theorem 11.4.1(a) / Exercise 11.4.1 -/
theorem integ_of_add {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f + g) I ∧ integ (f + g) I = integ f I + integ g I := by
  sorry

/-- Theorem 11.4.1(b) / Exercise 11.4.1 -/
theorem integ_of_smul {I: BoundedInterval} {c:ℝ} {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (c • f) I ∧ integ (c • f) I = c * integ f I := by
  sorry

/-- Theorem 11.4.1(c) / Exercise 11.4.1 -/
theorem integ_of_sub {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f - g) I ∧ integ (f - g) I = integ f I - integ g I := by
  sorry

/-- Theorem 11.4.1(d) / Exercise 11.4.1 -/
theorem integ_of_nonneg {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) (hf_nonneg: ∀ x ∈ I, 0 ≤ f x) :
  0 ≤ integ f I := by
  sorry

/-- Theorem 11.4.1(e) / Exercise 11.4.1 -/
theorem integ_mono {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I)
  (h: ∀ x ∈ I, f x ≤ g x) :
  integ f I ≤ integ g I := by
  sorry

/-- Theorem 11.4.1(f) / Exercise 11.4.1 -/
theorem integ_of_const (c:ℝ) (I: BoundedInterval) :
  integ (fun _ ↦ c) I = c * |I|ₗ := by
  sorry

/-- Theorem 11.4.1(f) / Exercise 11.4.1 -/
theorem integ_of_const' {I: BoundedInterval} {f:ℝ → ℝ} (hf: ConstantOn f I) :
  integ f I = (constant_value_on f I) * |I|ₗ := by
  sorry


open Classical in
/-- Theorem 11.4.1 (g)  / Exercise 11.4.1 -/
theorem IntegrableOn.of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  IntegrableOn (fun x ↦ if x ∈ I then f x else 0) J := by
  sorry

open Classical in
/-- Theorem 11.4.1 (g)  / Exercise 11.4.1 -/
theorem integ_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  integ (fun x ↦ if x ∈ I then f x else 0) J = integ f I := by
  sorry

/-- Theorem 11.4.1 (h) (Laws of integration) / Exercise 11.4.1 -/
theorem integ_of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f K) :
  IntegrableOn f I ∧ IntegrableOn f J ∧ integ f K = integ f I + integ f J := by
  sorry




end Chapter11
