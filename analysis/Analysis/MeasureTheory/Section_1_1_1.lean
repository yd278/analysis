import Analysis.MeasureTheory.Notation

/-!
# Introduction to Measure Theory, Section 1.1.1: Elementary measure

A companion to Section 1.1.1 of the book "An introduction to Measure Theory".

-/

/- Definition 1.1.1.  (Intervals) We use the same formalization of intervals used in
Chapter 11 of "Analysis I".  Following the usual Lean preference to admit `junk` values,
we allow for the possibility that `b < a`. -/
inductive BoundedInterval where
  | Ioo (a b:ℝ) : BoundedInterval
  | Icc (a b:ℝ) : BoundedInterval
  | Ioc (a b:ℝ) : BoundedInterval
  | Ico (a b:ℝ) : BoundedInterval

open BoundedInterval

@[coe]
def BoundedInterval.toSet (I: BoundedInterval) : Set ℝ := match I with
  | Ioo a b => .Ioo a b
  | Icc a b => .Icc a b
  | Ioc a b => .Ioc a b
  | Ico a b => .Ico a b

instance BoundedInterval.inst_coeSet : Coe BoundedInterval (Set ℝ) where
  coe := toSet

instance BoundedInterval.instEmpty : EmptyCollection BoundedInterval where
  emptyCollection := Ioo 0 0

@[simp]
theorem BoundedInterval.coe_empty : ((∅ : BoundedInterval):Set ℝ) = ∅ := by
  simp [toSet]

open Classical in
/-- This is to make Finsets of BoundedIntervals work properly -/
noncomputable instance BoundedInterval.decidableEq : DecidableEq BoundedInterval := instDecidableEqOfLawfulBEq

@[simp]
theorem BoundedInterval.set_Ioo (a b:ℝ) : (Ioo a b : Set ℝ) = .Ioo a b := by rfl

@[simp]
theorem BoundedInterval.set_Icc (a b:ℝ) : (Icc a b : Set ℝ) = .Icc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ioc (a b:ℝ) : (Ioc a b : Set ℝ) = .Ioc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ico (a b:ℝ) : (Ico a b : Set ℝ) = .Ico a b := by rfl

/-- Some helpful general lemmas about BoundedInterval -/
theorem Bornology.IsBounded.of_boundedInterval (I: BoundedInterval) : Bornology.IsBounded (I:Set ℝ) := by
  sorry

theorem BoundedInterval.ordConnected_iff (X:Set ℝ) : Bornology.IsBounded X ∧ X.OrdConnected ↔ ∃ I: BoundedInterval, X = I := by
  sorry

theorem BoundedInterval.inter (I J: BoundedInterval) : ∃ K : BoundedInterval, (I:Set ℝ) ∩ (J:Set ℝ) = (K:Set ℝ) := by
  sorry

noncomputable instance BoundedInterval.instInter : Inter BoundedInterval where
  inter I J := (inter I J).choose

@[simp]
theorem BoundedInterval.inter_eq (I J: BoundedInterval) : (I ∩ J : BoundedInterval) = (I:Set ℝ) ∩ (J:Set ℝ)  :=
  (inter I J).choose_spec.symm

instance BoundedInterval.instMembership : Membership ℝ BoundedInterval where
  mem I x := x ∈ (I:Set ℝ)

theorem BoundedInterval.mem_iff (I: BoundedInterval) (x:ℝ) :
  x ∈ I ↔ x ∈ (I:Set ℝ) := by rfl

instance BoundedInterval.instSubset : HasSubset BoundedInterval where
  Subset I J := ∀ x, x ∈ I → x ∈ J

theorem BoundedInterval.subset_iff (I J: BoundedInterval) :
  I ⊆ J ↔ (I:Set ℝ) ⊆ (J:Set ℝ) := by rfl

abbrev BoundedInterval.a (I: BoundedInterval) : ℝ := match I with
  | Ioo a _ => a
  | Icc a _ => a
  | Ioc a _ => a
  | Ico a _ => a

abbrev BoundedInterval.b (I: BoundedInterval) : ℝ := match I with
  | Ioo _ b => b
  | Icc _ b => b
  | Ioc _ b => b
  | Ico _ b => b

/-- Definition 1.1.1 (boxes) -/
abbrev BoundedInterval.length (I: BoundedInterval) : ℝ := max (I.b - I.a) 0

/-- Using ||ₗ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ₗ" : term => `(BoundedInterval.length $a)

@[ext]
structure Box (d:ℕ) where
  side : Fin d → BoundedInterval

@[coe]
abbrev Box.toSet {d:ℕ} (B: Box d) : Set (EuclideanSpace' d) :=
  Set.univ.pi (fun i ↦ ↑(B.side i))

instance Box.inst_coeSet {d:ℕ} : Coe (Box d) (Set (EuclideanSpace' d)) where
  coe := toSet

/-- Definition 1.1.1 (boxes)-/
abbrev Box.volume {d:ℕ} (B: Box d) : ℝ := ∏ i, |B.side i|ₗ

/-- Using ||ᵥ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ᵥ" : term => `(Box.volume $a)

abbrev IsElementary {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := ∃ S : Finset (Box d), E = ⋃ B ∈ S, ↑B

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.union {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E ∪ F) := by
  sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.inter {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E ∩ F) := by
  sorry


/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.sdiff {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E \ F) := by
  sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.symmDiff {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (symmDiff E F) := by
  sorry

open Pointwise

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.translate {d:ℕ} {E: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (x: EuclideanSpace' d) : IsElementary (E + {x}) := by
  sorry

