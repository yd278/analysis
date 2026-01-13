import Analysis.MeasureTheory.Section_1_4_2

/-!
# Introduction to Measure Theory, Section 1.4.3: Countably additive measures and measure spaces

A companion to (the introduction to) Section 1.4.3 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.4.19 (Finitely additive measure) -/
class FinitelyAdditiveMeasure {X:Type*} (B: ConcreteBooleanAlgebra X) where
  measure : Set X → EReal
  measure_pos : ∀ A : Set X, B.measurable A → 0 ≤ measure A
  measure_empty : measure ∅ = 0
  measure_finite_additive : ∀ E F : Set X, B.measurable E → B.measurable F → Disjoint E F →
    measure (E ∪ F) = measure E + measure F

/-- Example 1.4.21 -/
noncomputable def FinitelyAdditiveMeasure.lebesgue (d:ℕ) : FinitelyAdditiveMeasure (LebesgueMeasurable.boolean_algebra d) :=
  {
    measure A := Lebesgue_measure A
    measure_pos := by sorry
    measure_empty := by sorry
    measure_finite_additive := by sorry
  }

/-- Example 1.4.21 -/
def FinitelyAdditiveMeasure.restrict_alg {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {B':ConcreteBooleanAlgebra X} (hBB': B' ≤ B) : FinitelyAdditiveMeasure B' :=
  {
    measure := μ.measure
    measure_pos := by sorry
    measure_empty := by sorry
    measure_finite_additive := by sorry
  }

/-- Example 1.4.21 -/
noncomputable def FinitelyAdditiveMeasure.jordan (d:ℕ) : FinitelyAdditiveMeasure (JordanMeasurable.boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg (LebesgueMeasurable.gt_jordan_boolean_algebra d)

/-- Example 1.4.21 -/
noncomputable def FinitelyAdditiveMeasure.null (d:ℕ) : FinitelyAdditiveMeasure (IsNull.boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg (IsNull.lt_lebesgue_boolean_algebra d)

/-- Example 1.4.21 -/
noncomputable def FinitelyAdditiveMeasure.elem (d:ℕ) : FinitelyAdditiveMeasure (EuclideanSpace'.elementary_boolean_algebra d) :=
(FinitelyAdditiveMeasure.lebesgue d).restrict_alg (by sorry)

open Classical in
/-- Example 1.4.22 (Dirac measure) -/
noncomputable def FinitelyAdditiveMeasure.dirac {X:Type*} (x₀:X) (B: ConcreteBooleanAlgebra X) : FinitelyAdditiveMeasure B :=
  {
    measure := fun A => if x₀ ∈ A then 1 else 0
    measure_pos := by sorry
    measure_empty := by sorry
    measure_finite_additive := by sorry
  }

/-- Example 1.4.23 (Zero measure) -/
instance FinitelyAdditiveMeasure.instZero {X:Type*} (B: ConcreteBooleanAlgebra X) : Zero (FinitelyAdditiveMeasure B) :=
  {
    zero := {
      measure := fun A => 0
      measure_pos := by sorry
      measure_empty := by sorry
      measure_finite_additive := by sorry
    }
  }

/-- Example 1.4.24 (linear combinations of measures) -/
instance FinitelyAdditiveMeasure.instAdd {X:Type*} {B: ConcreteBooleanAlgebra X} : Add (FinitelyAdditiveMeasure B) :=
  {
    add := fun μ ν =>
      {
        measure := fun A => μ.measure A + ν.measure A
        measure_pos := by sorry
        measure_empty := by sorry
        measure_finite_additive := by sorry
      }
  }

noncomputable instance FinitelyAdditiveMeasure.instSmul {X:Type*} {B: ConcreteBooleanAlgebra X} : SMul ENNReal (FinitelyAdditiveMeasure B) :=
{
    smul := fun c μ =>
        {
        measure := fun A => c * μ.measure A
        measure_pos := by sorry
        measure_empty := by sorry
        measure_finite_additive := by sorry
        }
}

instance FinitelyAdditiveMeasure.instAddCommMonoid {X:Type*} {B: ConcreteBooleanAlgebra X} : AddCommMonoid (FinitelyAdditiveMeasure B) :=
{
  add_assoc := by sorry,
  zero_add := by sorry,
  add_zero := by sorry,
  add_comm := by sorry
  nsmul := nsmulRec
}

noncomputable instance FinitelyAdditiveMeasure.instDistribMulAction {X:Type*} {B: ConcreteBooleanAlgebra X} : DistribMulAction ENNReal (FinitelyAdditiveMeasure B) :=
{
  smul_zero := by sorry,
  smul_add := by sorry,
  one_smul := by sorry,
  mul_smul := by sorry
}

/-- Example 1.4.25 (Restriction of a measure) -/
def FinitelyAdditiveMeasure.restrict {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) (A:Set X) (hA:B.measurable A) : FinitelyAdditiveMeasure (B.restrict A) :=
  {
    measure := fun E => μ.measure E
    measure_pos := by sorry
    measure_empty := by sorry
    measure_finite_additive := by sorry
  }
