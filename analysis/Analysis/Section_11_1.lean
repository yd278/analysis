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

/-- There is a technical issue in that this coercion is not injective: the empty set is represented by multiple bounded intervals.  This causes some of the statements in this section to be a little uglier than necessary.-/
instance BoundedInterval.inst_coeSet : Coe BoundedInterval (Set ℝ) where
  coe (I: BoundedInterval) := match I with
    | Ioo a b => Set.Ioo a b
    | Icc a b => Set.Icc a b
    | Ioc a b => Set.Ioc a b
    | Ico a b => Set.Ico a b

instance BoundedInterval.instEmpty : EmptyCollection BoundedInterval where
  emptyCollection := Ioo 0 0

/-- This is to make Finsets of BoundedIntervals work properly -/
noncomputable instance BoundedInterval.decidableEq : DecidableEq BoundedInterval := by
  classical
  exact instDecidableEqOfLawfulBEq

@[simp]
theorem BoundedInterval.mem_Ioo (a b x:ℝ) : x ∈ (BoundedInterval.Ioo a b : Set ℝ) ↔ a < x ∧ x < b := by
  rfl

@[simp]
theorem BoundedInterval.mem_Icc (a b x:ℝ) : x ∈ (BoundedInterval.Icc a b : Set ℝ) ↔ a ≤ x ∧ x ≤ b := by
  rfl

@[simp]
theorem BoundedInterval.mem_Ioc (a b x:ℝ) : x ∈ (BoundedInterval.Ioc a b : Set ℝ) ↔ a < x ∧ x ≤ b := by
  rfl

@[simp]
theorem BoundedInterval.mem_Ico (a b x:ℝ) : x ∈ (BoundedInterval.Ico a b : Set ℝ) ↔ a ≤ x ∧ x < b := by
  rfl

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

@[simp]
theorem BoundedInterval.inter_eq (I J: BoundedInterval) : (I ∩ J : BoundedInterval) = (I:Set ℝ) ∩ (J:Set ℝ)  :=
  (BoundedInterval.inter I J).choose_spec.symm

example :
  (BoundedInterval.Ioo 2 4 ∩ BoundedInterval.Icc 4 6) = (BoundedInterval.Icc 4 4 : Set ℝ) := by
  sorry

instance BoundedInterval.instSubset : HasSubset BoundedInterval where
  Subset I J := (I:Set ℝ) ⊆ (J:Set ℝ)

theorem BoundedInterval.subset_iff (I J: BoundedInterval) :
  I ⊆ J ↔ (I:Set ℝ) ⊆ (J:Set ℝ) := by rfl

abbrev BoundedInterval.length (I: BoundedInterval) : ℝ := match I with
  | BoundedInterval.Ioo a b => max (b - a) 0
  | BoundedInterval.Icc a b => max (b - a) 0
  | BoundedInterval.Ioc a b => max (b - a) 0
  | BoundedInterval.Ico a b => max (b - a) 0

example : (BoundedInterval.Icc 3 5).length = 2 := by
  sorry

example : (BoundedInterval.Ioo 3 5).length = 2 := by
  sorry

example : (BoundedInterval.Icc 5 5).length = 0 := by
  sorry

theorem BoundedInterval.length_of_empty {I: BoundedInterval} (hI: (I:Set ℝ) = ∅) : I.length = 0 := by
  sorry

@[ext]
structure Partition (I: BoundedInterval) where
  intervals : Finset BoundedInterval
  exists_unique (x:ℝ) : x ∈ (I:Set ℝ) → ∃! J, J ∈ intervals ∧ x ∈ (J:Set ℝ)

example : ∃ P:Partition (BoundedInterval.Icc 1 8),
  P.intervals = {BoundedInterval.Icc 1 1, BoundedInterval.Ioo 1 3, BoundedInterval.Ico 3 5,
                 BoundedInterval.Icc 5 5, BoundedInterval.Ioc 5 8, ∅} := by
  sorry

example : ∃ P:Partition (BoundedInterval.Icc 1 8),
  P.intervals = {BoundedInterval.Icc 1 1, BoundedInterval.Ioo 1 3, BoundedInterval.Ico 3 5,
                 BoundedInterval.Icc 5 5, BoundedInterval.Ioc 5 8} := by
  sorry

example : ¬ ∃ P:Partition (BoundedInterval.Icc 1 5),
  P.intervals = {BoundedInterval.Icc 1 4, BoundedInterval.Icc 3 5} := by
  sorry

example : ¬ ∃ P:Partition (BoundedInterval.Ioo 1 5),
  P.intervals = {BoundedInterval.Ioo 1 3, BoundedInterval.Ioo 3 5} := by
  sorry

example : ¬ ∃ P:Partition (BoundedInterval.Ioo 1 5),
  P.intervals = {BoundedInterval.Ioo 0 3, BoundedInterval.Ico 3 5} := by
  sorry

/-- Theorem 11.1.13 (Length is finitely additive) -/
theorem Partition.sum_of_length  (I: BoundedInterval) (P: Partition I) :
  ∑ J ∈ P.intervals, J.length = I.length := by
  -- This proof is written to follow the structure of the original text.
  sorry -- TODO

/-- Definition 11.1.14 (Finer and coarser partitions) -/
instance Partition.instLE (I: BoundedInterval) : LE (Partition I) where
  le P P' := ∀ J ∈ P'.intervals, ∃ K ∈ P.intervals, J ⊆ K

instance Partition.instPreOrder (I: BoundedInterval) : Preorder (Partition I) where
  le_refl P := by
    sorry
  le_trans P P' P'' hP hP' := by
    sorry

instance Partition.instBot (I: BoundedInterval) : Bot (Partition I) where
  bot := {
    intervals := {I}
    exists_unique := by
      intro x hx
      apply ExistsUnique.intro I
      . simp [hx]
      simp
    }

instance Partition.instOrderBot (I: BoundedInterval) : OrderBot (Partition I) where
  bot_le := by
    sorry

/-- Example 11.1.15 -/
example : ∃ P P' : Partition (BoundedInterval.Icc 1 4),
  P.intervals = {BoundedInterval.Ico 1 2, BoundedInterval.Icc 2 2, BoundedInterval.Ioo 2 3,
                 BoundedInterval.Icc 3 4} ∧
  P'.intervals = {BoundedInterval.Icc 1 2, BoundedInterval.Ioc 2 4} ∧
  P' ≤ P := by
  sorry

/-- Definition 11.1.16 (Common refinement)-/
noncomputable instance Partition.instMax (I: BoundedInterval) : Max (Partition I) where
  max P P' := {
    intervals := Finset.image₂ (fun J K ↦ J ∩ K) P.intervals P'.intervals
    exists_unique := by
      intro x hx
      obtain ⟨ J, ⟨ hJ1, hJ2⟩, hxJ ⟩ := P.exists_unique x hx
      obtain ⟨ K, ⟨ hK1, hK2⟩, hxK ⟩ := P'.exists_unique x hx
      simp [hx] at hxJ hxK
      apply ExistsUnique.intro (J ∩ K)
      . simp
        exact ⟨ ⟨ J, hJ1, K, hK1, rfl ⟩, ⟨ hJ2, hK2 ⟩ ⟩
      simp
      rintro L J' hJ' K' hK' rfl hx'
      simp at hx'
      specialize hxJ J' hJ' hx'.1
      specialize hxK K' hK' hx'.2
      simp [hxJ, hxK]
    }


/-- Example 11.1.17 -/
example : ∃ P P' : Partition (BoundedInterval.Icc 1 4),
  P.intervals = {BoundedInterval.Ico 1 3, BoundedInterval.Icc 3 4} ∧
  P'.intervals = {BoundedInterval.Icc 1 2, BoundedInterval.Ioc 2 4} ∧
  (P' ⊔ P).intervals = {BoundedInterval.Icc 1 2, BoundedInterval.Ioo 2 3, BoundedInterval.Icc 3 4, ∅} := by
  sorry

/-- Lemma 11.1.8 / Exercise 11.1.4 -/
theorem BoundedInterval.le_max (I: BoundedInterval) (P P': Partition I) :
  P ≤ P ⊔ P' ∧ P' ≤ P ⊔ P' := by
  sorry

end Chapter11
