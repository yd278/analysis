import Mathlib.Tactic
import Analysis.Section_6_3

/-!
# Analysis I, Section 6.3

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Lim sup and lim inf of sequences

-/

abbrev Real.adherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) := ∃ n ≥ a.m, ε.close (a n) x

abbrev Real.continually_adherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) := ∀ N ≥ a.m, ε.adherent (a.from N) x

namespace Chapter6

abbrev Sequence.limit_point (a:Sequence) (x:ℝ) : Prop := ∀ ε > (0:ℝ), ε.continually_adherent a x

theorem Sequence.limit_point_def (a:Sequence) (x:ℝ) :
  a.limit_point x ↔ ∀ ε > 0, ∀ N ≥ a.m, ∃ n ≥ N, |a n - x| ≤ ε := by
    sorry

noncomputable abbrev Example_6_4_3 : Sequence := (fun (n:ℕ) ↦ 1 - (10:ℝ)^(-(n:ℤ)-1))

/-- Example 6.4.3 -/
example : (0.1:ℝ).adherent Example_6_4_3 0.8 := by sorry

/-- Example 6.4.3 -/
example : ¬ (0.1:ℝ).continually_adherent Example_6_4_3 0.8 := by sorry

/-- Example 6.4.3 -/
example : (0.1:ℝ).continually_adherent Example_6_4_3 1 := by sorry

/-- Example 6.4.3 -/
example : Example_6_4_3.limit_point 1 := by sorry

noncomputable abbrev Example_6_4_4 : Sequence := (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

/-- Example 6.4.4 -/
example : (0.1:ℝ).adherent Example_6_4_4 1 := by sorry

/-- Example 6.4.4 -/
example : (0.1:ℝ).continually_adherent Example_6_4_4 1 := by sorry

/-- Example 6.4.4 -/
example : Example_6_4_4.limit_point 1 := by sorry

/-- Example 6.4.4 -/
example : Example_6_4_4.limit_point (-1) := by sorry

/-- Example 6.4.4 -/
example : ¬ Example_6_4_4.limit_point 0 := by sorry

/-- Proposition 6.4.5 / Exercise 6.4.1 -/
theorem Sequence.limit_point_of_limit {a:Sequence} {x:ℝ} (h: a.tendsTo x) : a.limit_point x := by
  sorry

/-- A technical issue uncovered by the formalization: the upper and lower sequences of a real sequence take values in the extended reals rather than the reals, so the definitions need to be adjusted accordingly. -/
noncomputable abbrev Sequence.upperseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).sup

noncomputable abbrev Sequence.limsup (a:Sequence) : EReal := sInf { x | ∃ N ≥ a.m, x = a.upperseq N }

noncomputable abbrev Sequence.lowerseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).inf

noncomputable abbrev Sequence.liminf (a:Sequence) : EReal := sSup { x | ∃ N ≥ a.m, x = a.lowerseq N }

noncomputable abbrev Example_6_4_7 : Sequence := (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

example (n:ℕ) : Example_6_4_7.upperseq n = if Even n then 1 + (10:ℝ)^(-(n:ℤ)-1) else 1 + (10:ℝ)^(-(n:ℤ)-2) := by sorry

example : Example_6_4_7.limsup = 1 := by sorry

example (n:ℕ) : Example_6_4_7.lowerseq n = if Even n then -(1 + (10:ℝ)^(-(n:ℤ)-2)) else -(1 + (10:ℝ)^(-(n:ℤ)-1)) := by sorry

example : Example_6_4_7.liminf = -1 := by sorry

example : Example_6_4_7.sup = (1.1:ℝ) := by sorry

example : Example_6_4_7.inf = (-1.01:ℝ) := by sorry





end Chapter6
