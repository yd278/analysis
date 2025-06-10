import Mathlib.Tactic

/-!
# Analysis I, Section 6.1

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

-

-/


/- Definition 6.1.1 (Distance).  Here we use the Mathlib distance. -/
#check Real.dist_eq

abbrev Real.close (ε x y : ℝ) : Prop := dist x y ≤ ε

/-- Definition 6.1.2 (ε-close). This is similar to the previous notion of ε-closeness, but where all quantities are real instead of rational. -/
theorem Real.close_def (ε x y : ℝ) : ε.close x y ↔ dist x y ≤ ε := by rfl

namespace Chapter6

/-- Definition 6.1.3 (Sequence). This is similar to the Chapter 5 sequence, except that now the sequence is real-valued.
@[ext]
structure Sequence where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n, n < m → seq n = 0
