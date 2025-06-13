import Mathlib.Tactic

/-!
# Analysis I, Section 7.1

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Technical note: it is convenient in Lean to extend finite sequences (usually by zero) to be functions on the entire integers.

Main constructions and results of this section:

-

-/

open BigOperators

-- We use `Finset.Icc` to describe finite intervals in the integers.  `Finset.mem_Icc` is the standard Mathlib tool for checking membership in such intervals.
#check Finset.mem_Icc

/-- Definition 7.1.1 -/
theorem Finset.sum_of_empty {n m:ℤ} (h: n < m) (a: ℤ → ℝ) : ∑ i ∈ (Finset.Icc m n), a i = 0 := by
  rw [Finset.sum_eq_zero]
  intro x hx
  rw [Finset.mem_Icc] at hx
  linarith

/-- Definition 7.1.1.  This is similar to Mathlib's `Finset.sum_Icc_succ_top` except that the latter involves summation over the natural numbers rather than integers. -/
theorem Finset.sum_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) : ∑ i ∈ (Finset.Icc m (n+1)), a i = ∑ i ∈ (Finset.Icc m n), a i + a (n+1) := by
  rw [add_comm _ (a (n+1))]
  convert Finset.sum_insert _
  . ext i; simp; omega
  . infer_instance
  simp

