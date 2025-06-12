import Mathlib.Tactic
import Analysis.Section_6_1
import Analysis.Section_6_2

/-!
# Analysis I, Section 6.3

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Suprema and infima of sequences

-/

namespace Chapter6

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.sup (a:Sequence) : EReal := sSup { x | ∃ n ≥ a.m, x = a n }

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.inf (a:Sequence) : EReal := sInf { x | ∃ n ≥ a.m, x = a n }

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).sup = 1 := by sorry

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).inf = 1 := by sorry

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).sup = 1 := by sorry

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).inf = 0 := by sorry

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).sup = ⊤ := by sorry

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).inf = 1 := by sorry

abbrev Sequence.bddAboveBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≤ M

abbrev Sequence.bddAbove (a:Sequence) : Prop := ∃ M, a.bddAboveBy M

abbrev Sequence.bddBelowBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≥ M

abbrev Sequence.bddBelow (a:Sequence) : Prop := ∃ M, a.bddAboveBy M

theorem Sequence.bounded_iff (a:Sequence) : a.isBounded ↔ a.bddAbove \and a.bddBelow := by sorry

theorem Sequence.sup_of_bounded {a:Sequence} (h: a.isBounded) : a.sup.isFinite := by sorry

theorem Sequence.inf_of_bounded {a:Sequence} (h: a.isBounded) : a.inf.isFinite := by sorry

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.le_sup {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≤ a.sup := by sorry

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.sup_le_upper {a:Sequence} {M:EReal} (h: a.bddAboveBy M) : a.sup ≤ M := by sorry

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.exists_between_lt_sup {a:Sequence} {x: EReal} {y:EReal} (h: y < a.sup ) : ∃ n ≥ a.m, y < a n ∧ a n ≤ a.sup := by sorry

/-- Remark 6.3.7 -/
theorem Sequence.ge_inf {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≥ a.inf := by sorry

/-- Remark 6.3.7 -/
theorem Sequence.inf_ge_lower {a:Sequence} {M:EReal} (h: a.bddBelowBy M) : a.inf ≥ M := by sorry

/-- Remark 6.3.7 -/
theorem Sequence.exists_between_gt_inf {a:Sequence} {x: EReal} {y:EReal} (h: y > a.inf ) : ∃ n ≥ a.m, y > a n ∧ a n ≥ a.inf := by sorry

abbrev Sequence.isMonotone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≥ a n

abbrev Sequence.isAntitone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≤ a n

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.convergent_of_monotone {a:Sequence} (hbound: a.bddAbove) (hmono: a.isMonotone) : a.isConvergent := by sorry

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.lim_of_monotone {a:Sequence} (hbound: a.bddAbove) (hmono: a.isMonotone) : lim a = a.sup := by sorry

theorem Sequence.convergent_of_antitone {a:Sequence} (hbound: a.bddBelow) (hmono: a.isAntitone) : a.isConvergent := by sorry

theorem Sequence.lim_of_antitone {a:Sequence} (hbound: a.bddBelow) (hmono: a.isAntitone) : lim a = a.inf := by sorry

theorem Sequence.convergent_iff_bounded_of_monotone {a:Sequence} (ha: a.isMonotone) : a.isConvergent ↔ a.isBounded := by sorry

theorem Sequence.bounded_iff_convergent_of_antitone {a:Sequence} (ha: a.isAntitone) : a.isConvergent ↔ a.isBounded := by sorry

/-- Example 6.3.9 -/
abbrev Example_6_3_9 (n:ℕ) := ⌊π*10^n⌋ / (10:ℝ)^n

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).isMonotone := by sorry

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).bddAboveBy 4 := by sorry

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).isConvergent := by sorry

/-- Example 6.3.9 -/
example : lim (Example_6_3_9:Sequence) ≤ 4 := by sorry

/-- Proposition 6.3.1-/
theorem lim_of_exp {x:ℝ} (hpos: 0 < x) (hbound: x < 1) : ((fun (n:ℕ) ↦ x^n):Sequence).isConvergent ∧ lim ((fun (n:ℕ) ↦ x^n):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  sorry

/-- Exercise 6.3.4 -/
theorem lim_of_exp {x:ℝ} (hbound: x > 1) : ¬((fun (n:ℕ) ↦ x^n):Sequence).isConvergent := by sorry

end Chapter6
