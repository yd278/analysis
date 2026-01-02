import Analysis.MeasureTheory.Section_1_4_1
/-!
# Introduction to Measure Theory, Section 1.4.2: $\sigma$-algebras and measurable spaces

A companion to (the introduction to) Section 1.4.2 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.4.12 (Sigma algebra) -/
class ConcreteSigmaAlgebra (X:Type*) extends ConcreteBooleanAlgebra X where
  countable_union_mem : ∀ E : ℕ → Set X, (∀ n, measurable (E n)) → measurable (⋃ n, E n)

def ConcreteSigmaAlgebra.toMeasurableSpace {X: Type*} (B: ConcreteSigmaAlgebra X) : MeasurableSpace X :=
  by sorry

def MeasurableSpace.toConcreteSigmaAlgebra {X: Type*} (M: MeasurableSpace X) : ConcreteSigmaAlgebra X :=
  by sorry

def ConcreteBooleanAlgebra.isSigmaAlgebra {X: Type*} (B: ConcreteBooleanAlgebra X) : Prop := ∀ E : ℕ → Set X, (∀ n, measurable (E n)) → measurable (⋃ n, E n)

def ConcreteBooleanAlgebra.isSigmaAlgebra.toSigmaAlgebra {X: Type*} {B: ConcreteBooleanAlgebra X} (h: B.isSigmaAlgebra) : ConcreteSigmaAlgebra X :=
  { countable_union_mem := h }

/-- Exercise 1.4.10 -/
def ConcreteBooleanAlgebra.isAtomic.isSigmaAlgebra {X: Type*} {B: ConcreteBooleanAlgebra X} (h: B.isAtomic) : B.isSigmaAlgebra :=
  by sorry

/-- Exercise 1.4.11 -/
theorem LebesgueMeasurable.boolean_algebra.isSigmaAlgebra (d:ℕ) : (LebesgueMeasurable.boolean_algebra d).isSigmaAlgebra :=
  by sorry

def LebesgueMeasurable.sigmaAlgebra (d:ℕ) : ConcreteSigmaAlgebra (EuclideanSpace' d) :=
  (LebesgueMeasurable.boolean_algebra.isSigmaAlgebra d).toSigmaAlgebra

theorem IsNull.boolean_algebra.isSigmaAlgebra (d:ℕ) : (IsNull.boolean_algebra d).isSigmaAlgebra :=
  by sorry

def IsNull.sigmaAlgebra (d:ℕ) : ConcreteSigmaAlgebra (EuclideanSpace' d) :=
  (IsNull.boolean_algebra.isSigmaAlgebra d).toSigmaAlgebra

theorem JordanMeasurable.boolean_algebra.not_isSigmaAlgebra (d:ℕ) : ¬ (JordanMeasurable.boolean_algebra d).isSigmaAlgebra :=
  by sorry

/-- Exercise 1.4.12 -/
theorem ConcreteSigmaAlgebra.restrict_is_sigma {X:Type*} (B: ConcreteSigmaAlgebra X) (A:Set X): (B.restrict A).isSigmaAlgebra := by sorry

def ConcreteSigmaAlgebra.restrict {X:Type*} (B: ConcreteSigmaAlgebra X) (A:Set X) : ConcreteSigmaAlgebra A := (B.restrict_is_sigma A).toSigmaAlgebra


