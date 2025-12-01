import Analysis.MeasureTheory.Section_1_3_4

/-!
# Introduction to Measure Theory, Section 1.3.5: Littlewood's three principles

A companion to (the introduction to) Section 1.3.5 of the book "An introduction to Measure Theory".

-/

/-- Theorem 1.3.20(i) Approximation of $L^1$ functions by simple functions -/
theorem ComplexAbsolutelyIntegrable.approx_by_simple {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), ComplexSimpleFunction g ∧ ComplexAbsolutelyIntegrable g ∧
    PreL1.norm (f - g) ≤ ε := by sorry

theorem RealAbsolutelyIntegrable.approx_by_simple {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℝ), RealSimpleFunction g ∧ RealAbsolutelyIntegrable g ∧
    PreL1.norm (f - g) ≤ ε := by sorry

def ComplexStepFunction {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop :=
  ∃ (S: Finset (Box d)) (c: S → ℂ), f = ∑ B, (c B • Complex.indicator (B.val.toSet))

def RealStepFunction {d:ℕ} (f: EuclideanSpace' d → ℝ) : Prop :=
  ∃ (S: Finset (Box d)) (c: S → ℝ), f = ∑ B, (c B • (B.val.toSet).indicator')

/-- Theorem 1.3.20(ii) Approximation of $L^1$ functions by step functions -/
theorem ComplexAbsolutelyIntegrable.approx_by_step {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), ComplexStepFunction g ∧ ComplexAbsolutelyIntegrable g ∧
    PreL1.norm (f - g) ≤ ε := by sorry

theorem RealAbsolutelyIntegrable.approx_by_step {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → ℝ), RealStepFunction g ∧ RealAbsolutelyIntegrable g ∧
        PreL1.norm (f - g) ≤ ε := by sorry

def CompactlySupported {X Y:Type*} [TopologicalSpace X] [Zero Y] (f: X → Y) : Prop :=
  ∃ (K: Set X), IsCompact K ∧ ∀ x, x ∉ K → f x = 0

/-- Theorem 1.3.20(iii) Approximation of $L^1$ functions by continuous compactly supported functions -/
theorem ComplexAbsolutelyIntegrable.approx_by_continuous_compact {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), Continuous g ∧ CompactlySupported g ∧
    PreL1.norm (f - g) ≤ ε := by sorry

theorem RealAbsolutelyIntegrable.approx_by_continuous_compact {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → ℝ), Continuous g ∧ CompactlySupported g ∧
        PreL1.norm (f - g) ≤ ε := by sorry

def UniformlyConvergesTo {X Y:Type*} [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) : Prop := ∀ ε>0, ∃ N, ∀ n ≥ N, ∀ x, dist (f n x) (g x) ≤ ε

def UniformlyConvergesToOn {X Y:Type*} [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) (S: Set X): Prop := UniformlyConvergesTo (fun n (x:S) ↦ f n x.val) (fun x ↦ g x.val)

/-- Definition 1.3.21 (Locally uniform convergence) -/
def LocallyUniformlyConvergesTo {X Y:Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) : Prop :=
  ∀ (K: Set X), Bornology.IsBounded K → UniformlyConvergesToOn f g K

/-- Remark 1.3.22 -/
theorem LocallyUniformlyConvergesTo.iff {d:ℕ} {Y:Type*} [PseudoMetricSpace Y] (f: ℕ → EuclideanSpace' d → Y) (g: EuclideanSpace' d → Y) :
  LocallyUniformlyConvergesTo f g ↔
  ∀ x₀, ∃ U: Set (EuclideanSpace' d), x₀ ∈ U ∧ IsOpen U → UniformlyConvergesToOn f g U := by sorry

def LocallyUniformlyConvergesToOn {X Y:Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) (S: Set X): Prop :=
  LocallyUniformlyConvergesTo (fun n (x:S) ↦ f n x.val) (fun x ↦ g x.val)

/-- Example 1.3.23 -/
example : LocallyUniformlyConvergesTo (fun n (x:EuclideanSpace' 1) ↦ x.toReal / n) (fun x ↦ 0) := by sorry

example : ¬ UniformlyConvergesTo (fun n (x:EuclideanSpace' 1) ↦ x.toReal / n) (fun x ↦ 0) := by sorry

/-- Example 1.3.24 -/
example : LocallyUniformlyConvergesTo (fun N (x:EuclideanSpace' 1) ↦ ∑ n ∈ Finset.range N, x.toReal^n / n.factorial) (fun x ↦ x.toReal.exp) := by sorry

example : PointwiseConvergesTo (fun N (x:EuclideanSpace' 1) ↦ ∑ n ∈ Finset.range N, x.toReal^n / n.factorial) (fun x ↦ x.toReal.exp) := by sorry

example : ¬ UniformlyConvergesTo (fun N (x:EuclideanSpace' 1) ↦ ∑ n ∈ Finset.range N, x.toReal^n / n.factorial) (fun x ↦ x.toReal.exp) := by sorry

/-- Example 1.3.25 -/
example : PointwiseConvergesTo (fun n (x:EuclideanSpace' 1) ↦ if x.toReal > 0 then 1 / (n * x.toReal) else 0) (fun x ↦ 0) := by sorry

example : ¬ LocallyUniformlyConvergesTo (fun n (x:EuclideanSpace' 1) ↦ if x.toReal > 0 then 1 / (n * x.toReal) else 0) (fun x ↦ 0) := by sorry

/-- Theorem 1.3.26 (Egorov's theorem)-/
theorem PointwiseAeConvergesTo.locallyUniformlyConverges_outside_small {d:ℕ} {f : ℕ → EuclideanSpace' d → ℂ} {g : EuclideanSpace' d → ℂ}
  (hf: ∀ n, ComplexMeasurable (f n))
  (hfg: PointwiseAeConvergesTo f g)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (E: Set (EuclideanSpace' d)), MeasurableSet E ∧
    Lebesgue_measure E ≤ ε ∧
    LocallyUniformlyConvergesToOn f g Eᶜ := by sorry


