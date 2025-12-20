import Mathlib.Order.BooleanAlgebra.Defs

import Analysis.MeasureTheory.Section_1_3_5

/-!
# Introduction to Measure Theory, Section 1.4.1: Boolean algebras

A companion to (the introduction to) Section 1.4.1 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.4.1 -/
class ConcreteBooleanAlgebra (X:Type*) where
  measurable : Set X → Prop
  empty_mem : measurable (∅ : Set X)
  compl_mem : ∀ E, measurable E → measurable Eᶜ
  union_mem : ∀ E F, measurable E → measurable F → measurable (E ∪ F)

instance ConcreteBooleanAlgebra.instLE (X:Type*) : LE (ConcreteBooleanAlgebra X) :=
  ⟨fun B1 B2 => ∀ E, B1.measurable E → B2.measurable E⟩

instance ConcreteBooleanAlgebra.instPartialOrder (X:Type*) : PartialOrder (ConcreteBooleanAlgebra X) :=
  {
    le_refl := sorry
    le_trans := sorry
    le_antisymm := sorry
  }

def ConcreteBooleanAlgebra.measurableSets {X:Type*} (B: ConcreteBooleanAlgebra X) : Set (Set X) :=
  { E | B.measurable E }

/-- Example 1.4.3 -/
instance ConcreteBooleanAlgebra.instOrderTop {X:Type*} : OrderTop (ConcreteBooleanAlgebra X) :=
  {
    top := {
      measurable := fun _ => True
      empty_mem := trivial
      compl_mem := fun _ _ => trivial
      union_mem := fun _ _ _ _ => trivial
    }
    le_top := sorry
  }

/-- Example 1.4.3 -/
instance ConcreteBooleanAlgebra.instOrderBot {X:Type*} : OrderBot (ConcreteBooleanAlgebra X) :=
  {
    bot := {
      measurable := fun E => E = ∅ ∨ E = Set.univ
      empty_mem := by grind
      compl_mem := fun E hE => by grind
      union_mem := fun E F hE hF => by grind
    }
    bot_le := sorry
  }

/-- Exercise 1.4.1 (Elementary algebra) -/
def EuclideanSpace'.elementary_boolean_algebra (d:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  {
    measurable := fun E => IsElementary E ∨ IsElementary Eᶜ
    empty_mem := by sorry
    compl_mem := by sorry
    union_mem := by sorry
  }

/-- Example 1.4.4 (Jordan algebra) -/
def JordanMeasurable.boolean_algebra (d:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  {
    measurable := fun E => JordanMeasurable E ∨ JordanMeasurable Eᶜ
    empty_mem := by sorry
    compl_mem := by sorry
    union_mem := by sorry
  }

def JordanMeasurable.gt_elementary_boolean_algebra (d:ℕ) :
  JordanMeasurable.boolean_algebra d ≥ EuclideanSpace'.elementary_boolean_algebra d :=
  by sorry

/-- Example 1.4.5 (Lebesgue algebra) -/
def LebesgueMeasurable.boolean_algebra (d:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  {
    measurable := fun E => LebesgueMeasurable E
    empty_mem := by sorry
    compl_mem := by sorry
    union_mem := by sorry
  }

def LebesgueMeasurable.gt_jordan_boolean_algebra (d:ℕ) :
  LebesgueMeasurable.boolean_algebra d ≥ JordanMeasurable.boolean_algebra d :=
  by sorry

/-- Example 1.4.6 (Null algebra) -/
def IsNull.boolean_algebra (d:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  {
    measurable := fun E => IsNull E ∨ IsNull Eᶜ
    empty_mem := by sorry
    compl_mem := by sorry
    union_mem := by sorry
  }

def IsNull.lt_lebesgue_boolean_algebra (d:ℕ) :
  IsNull.boolean_algebra d ≤ LebesgueMeasurable.boolean_algebra d :=
  by sorry

/-- Exercise 1.4.2 (Restriction) -/
def ConcreteBooleanAlgebra.restrict {X:Type*} (B: ConcreteBooleanAlgebra X) (A:Set X) : ConcreteBooleanAlgebra A :=
  {
    measurable := fun E => ∃ E' : Set X, B.measurable E ∧ E = E' ∩ A
    empty_mem := by sorry
    compl_mem := by sorry
    union_mem := by sorry
  }

def ConcreteBooleanAlgebra.restrict_iff {X:Type*} {B: ConcreteBooleanAlgebra X} {A:Set X} (h: B.measurable A) (E: Set A) :
  (B.restrict A).measurable E ↔ B.measurable A :=
  by sorry

/-- Remark 1.4.2: ConcreteBooleanAlgebras are BooleanAlgebras -/
def ConcreteBooleanAlgebra.toBooleanAlgebra {X:Type*} (B: ConcreteBooleanAlgebra X) : BooleanAlgebra (B.measurableSets) :=
{
   sup := sorry
   le_sup_left := sorry
   le_sup_right := sorry
   sup_le := sorry
   inf := sorry
   inf_le_left := sorry
   inf_le_right := sorry
   le_inf := sorry
   le_sup_inf := sorry
   compl := sorry
   top := sorry
   bot := sorry
   inf_compl_le_bot := sorry
   top_le_sup_compl := sorry
   le_top := sorry
   bot_le := sorry
}

def IsPartition {I X:Type*} (parts: I → Set X) : Prop := (Set.PairwiseDisjoint Set.univ parts) ∧ (⋃ i, parts i = Set.univ)

/-- Example 1.4.7 (Atomic algebra) -/
def IsPartition.to_ConcreteBooleanAlgebra {I X: Type*} {atoms: I → Set X} (h_part: IsPartition atoms) : ConcreteBooleanAlgebra X :=
  {
    measurable := fun E => ∃ J: Set I, E = ⋃ i ∈ J, atoms i
    empty_mem := by sorry
    compl_mem := by sorry
    union_mem := by sorry
  }

def IsPartition.discrete (X:Type*) : IsPartition (fun x:X ↦ {x}) := by sorry

def ConcreteBooleanAlgebra.top_atomic (X:Type*) : (IsPartition.discrete X).to_ConcreteBooleanAlgebra = ⊤ := by sorry

def IsPartition.trivial (X:Type*) : IsPartition (fun (x:Unit) ↦ (Set.univ: Set X)) := by sorry

def ConcreteBooleanAlgebra.bot_atomic (X:Type*) : (IsPartition.trivial X).to_ConcreteBooleanAlgebra = ⊥ := by sorry

def IsPartition.finer_than {I J X:Type*} {parts_I: I → Set X} {parts_J: J → Set X}
  (_: IsPartition parts_I) (_: IsPartition parts_J) : Prop :=
  ∀ i:I, ∃ j:J, parts_I i ⊆ parts_J j

def IsPartition.mono {I J X:Type*} {parts_I: I → Set X} {parts_J: J → Set X}
  (hI: IsPartition parts_I) (hJ: IsPartition parts_J)
  (h_finer: hI.finer_than hJ) :
  hI.to_ConcreteBooleanAlgebra ≤ hJ.to_ConcreteBooleanAlgebra :=
  by sorry

def IsPartition.remove_empty {I X:Type*} {parts: I → Set X} (h_part: IsPartition parts) : IsPartition (fun (i:{i:I // parts i ≠ ∅}) ↦ parts i.val) :=
  by sorry

def IsPartition.remove_empty_to_ConcreteBooleanAlgebra {I X:Type*} {parts: I → Set X} (h_part: IsPartition parts) :
  h_part.to_ConcreteBooleanAlgebra =
  h_part.remove_empty.to_ConcreteBooleanAlgebra :=
  by sorry
