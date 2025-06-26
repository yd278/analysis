import Mathlib.Tactic

/-!
# Analysis I, Section 11.1

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

-

-/

namespace Chapter11

inductive BoundedInterval where
  | Ioo (a b:ℝ) : BoundedInterval
  | Icc (a b:ℝ) : BoundedInterval
  | Ioc (a b:ℝ) : BoundedInterval
  | Ico (a b:ℝ) : BoundedInterval

instance BoundedInterval.inst_coeSet : Coe BoundedInterval (Set ℝ) where
  coe (I: BoundedInterval) := match I with
    | Ioo a b => Set.Ioo a b
    | Icc a b => Set.Icc a b
    | Ioc a b => Set.Ioc a b
    | Ico a b => Set.Ico a b

-- Definition 11.1.1
#check Set.ordConnected_def

/-- Examples 11.1.3 -/
example : (Set.Icc 1 2 : Set ℝ).OrdConnected := by sorry

example : (Set.Ioo 1 2 : Set ℝ).OrdConnected := by sorry

example : ¬ (Set.Icc 1 2 ∪ Set.Icc 3 4 : Set ℝ).OrdConnected := by sorry

example : (∅:Set ℝ).OrdConnected := by sorry

example (x:ℝ) : ({x}: Set ℝ).OrdConnected := by sorry

/-- Lemma 11.1.4 / Exercise 11.1.1 -/
theorem BoundedInterval.ordConnected_iff (X:Set ℝ) : Bornology.IsBounded X ∧ X.OrdConnected ↔ ∃ I: BoundedInterval, X = I := by
  sorry

/-- Corollary 11.1.6 / Exercise 11.1.2 -/
theorem BoundedInterval.inter (I J: BoundedInterval) : ∃ K : BoundedInterval, (I:Set ℝ) ∩ (J:Set ℝ) = (K:Set ℝ) := by
  sorry

noncomputable instance BoundedInterval.instInter : Inter BoundedInterval where
  inter I J := (inter I J).choose

theorem BoundedInterval.inter_eq (I J: BoundedInterval) : (I:Set ℝ) ∩ (J:Set ℝ) = (I ∩ J : BoundedInterval) :=
  (BoundedInterval.inter I J).choose_spec







end Chapter11
