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

theorem Real.nonzero_of_pos {x:Real} (hx: x.isPos) : x ≠ 0 := by
    have := not_zero_pos x
    simp [hx] at this ⊢
    assumption

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_neg (x:Real) : ¬ (x = 0 ∧ x.isNeg) := by sorry

theorem Real.nonzero_of_neg {x:Real} (hx: x.isNeg) : x ≠ 0 := by
    have := not_zero_neg x
    simp [hx] at this ⊢
    assumption

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

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).isNeg

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)

theorem Real.lt_iff (x y:Real) : x < y ↔ (x-y).isNeg := by rfl
theorem Real.le_iff (x y:Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).isPos := by sorry
theorem Real.ge_iff (x y:Real) : x ≥ y ↔ (x > y) ∨ (x = y) := by sorry

theorem Real.lt_of_coe (q q':ℚ): q < q' ↔ (q:Real) < (q':Real) := by sorry

theorem Real.gt_of_coe (q q':ℚ): q > q' ↔ (q:Real) > (q':Real) := Real.lt_of_coe _ _

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.trichotomous' (x y z:Real) : x > y ∨ x < y ∨ x = y := by sorry

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_lt (x y:Real) : ¬ (x > y ∧ x < y):= by sorry

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_eq (x y:Real) : ¬ (x > y ∧ x = y):= by sorry

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_lt_and_eq (x y:Real) : ¬ (x < y ∧ x = y):= by sorry

/-- Proposition 5.4.7(b) (order is anti-symmetric) / Exercise 5.4.2 -/
theorem Real.antisymm (x y:Real) : x < y ↔ (y - x).isPos := by sorry

/-- Proposition 5.4.7(c) (order is transitive) / Exercise 5.4.2 -/
theorem Real.lt_trans {x y z:Real} (hxy: x < y) (hyz: y < z) : x < z := by sorry

/-- Proposition 5.4.7(d) (addition preserves order) / Exercise 5.4.2 -/
theorem Real.add_lt_add_right {x y:Real} (z:Real) (hxy: x < y) : x + z < y + z := by sorry

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z:Real} (hxy: x < y) (hz: z.isPos) : x * z < y * z := by
  rw [antisymm] at hxy ⊢
  convert pos_mul hxy hz using 1
  ring

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_le_mul_left {x y z:Real} (hxy: x ≤ y) (hz: z.isPos) : z * x ≤ z * y := by sorry

theorem Real.mul_pos_neg {x y:Real} (hx: x.isPos) (hy: y.isNeg) : (x * y).isNeg := by
  sorry

/-- (Not from textbook) Real has the structure of a linear ordering.  The order is not computable, and so classical logic is required to impose decidability.-/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_le := sorry
  le_antisymm := sorry
  le_total := sorry
  toDecidableLE := by
    classical
    exact Classical.decRel _

/-- Proposition 5.4.8 -/
theorem Real.inv_of_pos {x:Real} (hx: x.isPos) : x⁻¹.isPos := by
  have hnon: x ≠ 0 := nonzero_of_pos hx
  have hident := inv_mul_self hnon
  have hinv_non: x⁻¹ ≠ 0 := by contrapose! hident; simp [hident]
  have hnonneg : ¬ x⁻¹.isNeg := by
    intro h
    have := mul_pos_neg hx h
    have id : -(1:Real) = (-1:ℚ) := by simp
    simp only [hident, neg_iff_pos_of_neg, id, pos_of_coe] at this
    linarith
  have trich := Real.trichotomous x⁻¹
  simp [hinv_non, hnonneg] at trich
  assumption

theorem Real.inv_of_gt {x y:Real} (hx: x.isPos) (hy: y.isPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  have hxnon: x ≠ 0 := nonzero_of_pos hx
  have hynon: y ≠ 0 := nonzero_of_pos hy
  have hxinv : x⁻¹.isPos := inv_of_pos hx
  have hyinv : y⁻¹.isPos := inv_of_pos hy
  by_contra! this
  have : (1:Real) > 1 := calc
    1 = x * x⁻¹ := (inv_mul_self hxnon).symm
    _ > y * x⁻¹ := mul_lt_mul_right hxy hxinv
    _ ≥ y * y⁻¹ := mul_le_mul_left this hy
    _ = _ := inv_mul_self hynon
  simp at this

/-- (Not from textbook) Real has the structure of a strict ordered ring. -/
instance Real.instIsStrictOrderedRing : IsStrictOrderedRing Real where
  add_le_add_left := by sorry
  add_le_add_right := by sorry
  mul_lt_mul_of_pos_left := by sorry
  mul_lt_mul_of_pos_right := by sorry
  le_of_add_le_add_left := by sorry
  zero_le_one := by sorry

/-- Proposition 5.4.9 (The non-negative reals are closed)-/
theorem Real.LIM_of_nonneg {a: ℕ → ℚ} (ha: ∀ n, a n ≥ 0) (hcauchy: (a:Sequence).isCauchy) : LIM a ≥ 0 := by
  sorry --TODO

/-- Corollary 5.4.10 -/
theorem Real.LIM_mono {a b:ℕ → ℚ} (ha: (a:Sequence).isCauchy) (hb: (b:Sequence).isCauchy) (hmono: ∀ n, a n ≤ b n) : LIM a ≤ LIM b := by
  sorry --TODO

/-- Remark 5.4.11 --/
theorem Real.LIM_mono_fail : ∃ (a b:ℕ → ℚ), (a:Sequence).isCauchy ∧ (b:Sequence).isCauchy ∧ ¬ (∀ n, a n > b n) ∧ ¬ LIM a > LIM b := by
  use (fun n ↦ 1 + 1/(n:ℚ))
  use (fun n ↦ 1 - 1/(n:ℚ))
  sorry

end Chapter5
