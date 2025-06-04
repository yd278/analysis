import Mathlib.Tactic
import Analysis.Section_5_3


/-!
# Analysis I, Section 5.4

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Ordering on the real line
-/

namespace Chapter5


/-- Definition 5.4.1 (sequences bounded away from zero with sign).  Sequences are indexed to start from zero as this is more convenient for Mathlib purposes. -/
abbrev bounded_away_pos (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c

/-- Definition 5.4.1 (sequences bounded away from zero with sign).-/
abbrev bounded_away_neg (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem bounded_away_pos_def (a:ℕ → ℚ) : bounded_away_pos a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c := by rfl

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem bounded_away_neg_def (a:ℕ → ℚ) : bounded_away_neg a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c := by rfl

/-- Examples 5.4.2 -/
example : bounded_away_pos (fun n ↦ 1 + 10^(-(n:ℤ)-1)) := by sorry

/-- Examples 5.4.2 -/
example : bounded_away_neg (fun n ↦ - - 10^(-(n:ℤ)-1)) := by sorry

/-- Examples 5.4.2 -/
example : ¬ bounded_away_pos (fun n ↦ (-1)^n) := by sorry

example : ¬ bounded_away_neg (fun n ↦ (-1)^n) := by sorry

example : bounded_away_zero (fun n ↦ (-1)^n) := by sorry

theorem bounded_away_zero_of_pos {a:ℕ → ℚ} (ha: bounded_away_pos a) : bounded_away_zero a := by sorry

theorem bounded_away_zero_of_neg {a:ℕ → ℚ} (ha: bounded_away_neg a) : bounded_away_zero a := by sorry

theorem not_bounded_away_pos_neg {a:ℕ → ℚ} : ¬ (bounded_away_pos a ∧ bounded_away_neg a) := by sorry

abbrev Real.isPos (x:Real) : Prop := ∃ a:ℕ → ℚ, bounded_away_pos a ∧ (a:Sequence).isCauchy ∧ x = LIM a

abbrev Real.isNeg (x:Real) : Prop := ∃ a:ℕ → ℚ, bounded_away_neg a ∧ (a:Sequence).isCauchy ∧ x = LIM a

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.trichotomous (x:Real) : x = 0 ∨ x.isPos ∨ x.isNeg := by sorry

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_pos (x:Real) : ¬ (x = 0 ∧ x.isPos) := by sorry

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_neg (x:Real) : ¬ (x = 0 ∧ x.isNeg) := by sorry

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_pos_neg (x:Real) : ¬ (x.isPos ∧ x.isNeg) := by sorry

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
@[simp]
theorem Real.neg_iff_pos_of_neg (x:Real) : x.isNeg ↔ (-x).isPos := by sorry

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1-/
theorem Real.pos_add {x y:Real} (hx: x.isPos) (hy: y.isPos) : (x+y).isPos := by sorry

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_mul {x y:Real} (hx: x.isPos) (hy: y.isPos) : (x*y).isPos := by sorry

theorem Real.pos_of_coe (q:ℚ) : (q:Real).isPos ↔ q > 0 := by sorry


theorem Real.neg_of_coe (q:ℚ) : (q:Real).isNeg ↔ q < 0 := by sorry

open Classical in
/-- Need to use classical logic here because isPos and isNeg are not decidable -/
noncomputable abbrev Real.abs (x:Real) : Real := if x.isPos then x else (if x.isNeg then -x else 0)

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_pos (x:Real) (hx: x.isPos) : Real.abs x = x := by
  simp [Real.abs, hx]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_neg (x:Real) (hx: x.isNeg) : Real.abs x = -x := by
  have : ¬ x.isPos := by have := Real.not_pos_neg x; simp only [hx, and_true] at this; assumption
  simp [Real.abs, hx, this]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_zero : Real.abs 0 = 0 := by
  have hpos: ¬ (0:Real).isPos := by have := Real.not_zero_pos 0; simp only [true_and] at this; assumption
  have hneg: ¬ (0:Real).isNeg := by have := Real.not_zero_neg 0; simp only [true_and] at this; assumption
  simp [Real.abs, hpos, hneg]


