import Analysis.MeasureTheory.Section_1_3_1

/-!
# Introduction to Measure Theory, Section 1.3.2: Measurable functions

A companion to (the introduction to) Section 1.3.2 of the book "An introduction to Measure Theory".

-/

def Unsigned {X Y:Type*} [LE Y] [Zero Y] (f:X → Y) : Prop := ∀ x, f x ≥ 0

def PointwiseConvergesTo {X Y:Type*} [TopologicalSpace Y] (f: ℕ → X → Y) (g: X → Y) : Prop := ∀ x, Filter.atTop.Tendsto (fun n ↦ f n x) (nhds (g x))

/-- Definiiton 1.3.8 (Unsigned measurable function) -/
def UnsignedMeasurable {d:ℕ} (f: EuclideanSpace' d → EReal) : Prop := Unsigned f ∧ ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (PointwiseConvergesTo g f)

def EReal.BoundedFunction {X:Type*} (f:X → EReal) : Prop := ∃ M:NNReal, ∀ x, (f x).abs ≤ M

def FiniteMeasureSupport {d:ℕ} {Y:Type*} [Zero Y] (f: EuclideanSpace' d → Y) : Prop := Lebesgue_measure (Support f) < ⊤

def PointwiseAeConvergesTo {d:ℕ} {Y:Type*} [TopologicalSpace Y] (f: ℕ → (EuclideanSpace' d → Y)) (g: EuclideanSpace' d → Y) : Prop := AlmostAlways (fun x ↦ Filter.atTop.Tendsto (fun n ↦ f n x) (nhds (g x)))

/-!
## Helper lemmas for Lemma 1.3.9

The proof follows the book's implication chain. We establish explicit edges and
let `tfae_finish` compute the transitive closure.

**Explicit edges declared:**
- (i) ⟺ (ii): by definition of UnsignedMeasurable
- (ii) ⟹ (iii): pointwise everywhere implies pointwise a.e.
- (iv) ⟹ (ii): monotone sequences in [0,∞] converge to their supremum
- (iii) ⟹ (v): via limsup representation (main technical work)
- (v) ⟺ (vi): countable unions/intersections
- (vi) ⟺ (vii): complementation
- (v) ⟺ (viii): complementation
- (v)-(viii) ⟹ (ix): intervals are intersections of half-intervals
- (ix) ⟹ (x): open sets are countable unions of intervals
- (x) ⟺ (xi): complementation
- (x) ⟹ (viii): preimage of closed set Iic
- (v)-(xi) ⟹ (iv): construction of approximating sequence

**Derived transitively (by tfae_finish):**
- (ix) ⟹ (v) or (vi): via (ix) → (x) → (viii) → (v) → (vi)
- (x) ⟹ (v)-(ix): via (x) → (viii) → (v) → (vi)/(vii)/(ix)
-/

namespace UnsignedMeasurable.TFAE_helpers

variable {d : ℕ} {f : EuclideanSpace' d → EReal}

-- Statement abbreviations for clarity (using indices as in the book)
private abbrev stmt_i (f : EuclideanSpace' d → EReal) := UnsignedMeasurable f
private abbrev stmt_ii (f : EuclideanSpace' d → EReal) :=
  ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (∀ x, Filter.atTop.Tendsto (fun n ↦ g n x) (nhds (f x)))
private abbrev stmt_iii (f : EuclideanSpace' d → EReal) :=
  ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (PointwiseAeConvergesTo g f)
private abbrev stmt_iv (f : EuclideanSpace' d → EReal) :=
  ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n) ∧ EReal.BoundedFunction (g n) ∧ FiniteMeasureSupport (g n)) ∧ (∀ x, Monotone (fun n ↦ g n x)) ∧ (∀ x, f x = iSup (fun n ↦ g n x))
private abbrev stmt_v (f : EuclideanSpace' d → EReal) := ∀ t, MeasurableSet {x | f x > t}
private abbrev stmt_vi (f : EuclideanSpace' d → EReal) := ∀ t, MeasurableSet {x | f x ≥ t}
private abbrev stmt_vii (f : EuclideanSpace' d → EReal) := ∀ t, MeasurableSet {x | f x < t}
private abbrev stmt_viii (f : EuclideanSpace' d → EReal) := ∀ t, MeasurableSet {x | f x ≤ t}
private abbrev stmt_ix (f : EuclideanSpace' d → EReal) := ∀ I:BoundedInterval, MeasurableSet (f⁻¹' (Real.toEReal '' I.toSet))
private abbrev stmt_x (f : EuclideanSpace' d → EReal) := ∀ U: Set EReal, IsOpen U → MeasurableSet (f⁻¹' U)
private abbrev stmt_xi (f : EuclideanSpace' d → EReal) := ∀ K: Set EReal, IsClosed K → MeasurableSet (f⁻¹' K)

/-! ### (i) ⟺ (ii): By definition of UnsignedMeasurable -/

private lemma i_iff_ii (hf : Unsigned f) : stmt_i f ↔ stmt_ii f := by
  simp only [UnsignedMeasurable]
  constructor
  · intro ⟨_, g, hg_simple, hg_conv⟩
    exact ⟨g, hg_simple, hg_conv⟩
  · intro ⟨g, hg_simple, hg_conv⟩
    exact ⟨hf, g, hg_simple, hg_conv⟩

/-! ### (ii) ⟹ (iii): Pointwise everywhere implies pointwise a.e. -/

private lemma ii_imp_iii : stmt_ii f → stmt_iii f := by
  intro ⟨g, hg_simple, hg_conv⟩
  refine ⟨g, hg_simple, ?_⟩
  -- AlmostAlways P means IsNull {x | ¬P x}
  -- Since pointwise convergence holds everywhere, {x | ¬Tendsto} = ∅
  simp only [PointwiseAeConvergesTo, AlmostAlways]
  have h_empty : {x | ¬Filter.atTop.Tendsto (fun n ↦ g n x) (nhds (f x))} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact hg_conv x
  rw [h_empty]
  exact Lebesgue_outer_measure.of_empty d

/-! ### (iv) ⟹ (ii): Monotone sequences in [0,∞] converge to their supremum -/

private lemma iv_imp_ii : stmt_iv f → stmt_ii f := by
  intro ⟨g, hg_props, hg_mono, hg_sup⟩
  refine ⟨g, fun n => (hg_props n).1, ?_⟩
  intro x
  rw [hg_sup x]
  -- For monotone sequences in EReal, g n x → iSup (g · x)
  sorry -- TODO: EReal.tendsto_atTop_iSup for monotone sequences

/-! ### (iii) ⟹ (v): Via limsup representation -/

-- This is the main technical work of the proof
private lemma iii_imp_v : stmt_iii f → stmt_v f := by
  intro ⟨g, hg_simple, hg_ae_conv⟩
  intro t
  -- The key insight: f(x) = lim f_n(x) = lim sup f_n(x) a.e.
  -- So {f > λ} = ⋃_{M≥1} ⋂_{N≥1} ⋃_{n≥N} {f_n > λ + 1/M} outside a null set
  sorry

/-! ### (v) ⟹ (vi): {f ≥ λ} = ⋂_{n≥1} {f > λ - 1/n} -/

private lemma v_imp_vi : stmt_v f → stmt_vi f := by
  intro hv t
  -- {f ≥ t} = ⋂_{n≥1} {f > t - 1/(n+1)}
  have h_eq : {x | f x ≥ t} = ⋂ (n : ℕ), {x | f x > t - (1 / (n + 1 : ℕ))} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hfx n
      sorry -- f x ≥ t implies f x > t - 1/(n+1)
    · intro hfx
      sorry -- limit argument
  rw [h_eq]
  exact MeasurableSet.iInter (fun n => hv _)

/-! ### (vi) ⟹ (v): {f > λ} = ⋃_{q ∈ ℚ, q > λ} {f ≥ q} -/

private lemma vi_imp_v : stmt_vi f → stmt_v f := by
  intro hvi t
  sorry -- countable union over rationals

/-! ### (v) ⟹ (viii): {f ≤ t} = {f > t}ᶜ -/

private lemma v_imp_viii : stmt_v f → stmt_viii f := by
  intro hv t
  have h_eq : {x | f x ≤ t} = {x | f x > t}ᶜ := by ext x; simp [not_lt]
  rw [h_eq]
  exact MeasurableSet.compl (hv t)

/-! ### (vi) ⟹ (vii): {f < t} = {f ≥ t}ᶜ -/

private lemma vi_imp_vii : stmt_vi f → stmt_vii f := by
  intro hvi t
  have h_eq : {x | f x < t} = {x | f x ≥ t}ᶜ := by ext x; simp [not_le]
  rw [h_eq]
  exact MeasurableSet.compl (hvi t)

/-! ### (vii) ⟹ (vi): {f ≥ t} = {f < t}ᶜ -/

private lemma vii_imp_vi : stmt_vii f → stmt_vi f := by
  intro hvii t
  have h_eq : {x | f x ≥ t} = {x | f x < t}ᶜ := by ext x; simp [not_lt]
  rw [h_eq]
  exact MeasurableSet.compl (hvii t)

/-! ### (viii) ⟹ (v): {f > t} = {f ≤ t}ᶜ -/

private lemma viii_imp_v : stmt_viii f → stmt_v f := by
  intro hviii t
  have h_eq : {x | f x > t} = {x | f x ≤ t}ᶜ := by ext x; simp [not_le]
  rw [h_eq]
  exact MeasurableSet.compl (hviii t)

/-! ### (v)-(viii) ⟹ (ix): Intervals are intersections of half-intervals -/

private lemma v_to_viii_imp_ix (hv : stmt_v f) (hvi : stmt_vi f) (hvii : stmt_vii f) (hviii : stmt_viii f) :
    stmt_ix f := by
  intro I
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Ioo a b) = {x | f x > a} ∩ {x | f x < b} := by sorry
    rw [h_eq]
    exact MeasurableSet.inter (hv _) (hvii _)
  | Icc a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Icc a b) = {x | f x ≥ a} ∩ {x | f x ≤ b} := by sorry
    rw [h_eq]
    exact MeasurableSet.inter (hvi _) (hviii _)
  | Ioc a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Ioc a b) = {x | f x > a} ∩ {x | f x ≤ b} := by sorry
    rw [h_eq]
    exact MeasurableSet.inter (hv _) (hviii _)
  | Ico a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Ico a b) = {x | f x ≥ a} ∩ {x | f x < b} := by sorry
    rw [h_eq]
    exact MeasurableSet.inter (hvi _) (hvii _)

/-! ### (ix) ⟹ (x): Open sets are countable unions of intervals -/

private lemma ix_imp_x : stmt_ix f → stmt_x f := by
  intro hix U hU
  sorry -- Every open set in EReal is countable union of intervals

/-! ### (x) ⟺ (xi): Complementation -/

private lemma x_iff_xi : stmt_x f ↔ stmt_xi f := by
  constructor
  · intro hx K hK
    have h_eq : f⁻¹' K = (f⁻¹' Kᶜ)ᶜ := by simp
    rw [h_eq]
    exact MeasurableSet.compl (hx _ hK.isOpen_compl)
  · intro hxi U hU
    have h_eq : f⁻¹' U = (f⁻¹' Uᶜ)ᶜ := by simp
    rw [h_eq]
    exact MeasurableSet.compl (hxi _ hU.isClosed_compl)

/-! ### (x) ⟹ (viii): Preimage of closed set Iic t -/

private lemma x_imp_viii : stmt_x f → stmt_viii f := by
  intro hx t
  have hxi := x_iff_xi.mp hx
  have h_closed : IsClosed (Set.Iic t) := isClosed_Iic
  have h_eq : {x | f x ≤ t} = f⁻¹' (Set.Iic t) := rfl
  rw [h_eq]
  exact hxi _ h_closed

/-! ### (v)-(xi) ⟹ (iv): Construction of approximating sequence -/

private lemma v_to_xi_imp_iv (hf : Unsigned f) (hv : stmt_v f) (hvi : stmt_vi f)
    (hvii : stmt_vii f) (hviii : stmt_viii f) (hix : stmt_ix f)
    (hx : stmt_x f) (hxi : stmt_xi f) :
    stmt_iv f := by
  -- Construct f_n(x) = largest k·2^{-n} ≤ min(f(x), n) when |x| ≤ n, else 0
  sorry

end UnsignedMeasurable.TFAE_helpers

/-- Lemma 1.3.9 (Equivalent notions of measurability).  Some slight changes to the statement have been made to make the claims cleaner to state -/
theorem UnsignedMeasurable.TFAE {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: Unsigned f):
    [
      UnsignedMeasurable f,
      ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (∀ x, Filter.atTop.Tendsto (fun n ↦ g n x) (nhds (f x))),
      ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (PointwiseAeConvergesTo g f),
      ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n) ∧  EReal.BoundedFunction (g n) ∧ FiniteMeasureSupport (g n)) ∧ (∀ x, Monotone (fun n ↦ g n x)) ∧ (∀ x, f x = iSup (fun n ↦ g n x)),
      ∀ t, MeasurableSet {x | f x > t},
      ∀ t, MeasurableSet {x | f x ≥ t},
      ∀ t, MeasurableSet {x | f x < t},
      ∀ t, MeasurableSet {x | f x ≤ t},
      ∀ I:BoundedInterval, MeasurableSet (f⁻¹' (Real.toEReal '' I.toSet)),
      ∀ U: Set EReal, IsOpen U → MeasurableSet (f⁻¹' U),
      ∀ K: Set EReal, IsClosed K → MeasurableSet (f⁻¹' K)
    ].TFAE := by
  open UnsignedMeasurable.TFAE_helpers in
  -- Establish the implication graph
  tfae_have 1 ↔ 2 := i_iff_ii hf
  tfae_have 2 → 3 := ii_imp_iii
  tfae_have 4 → 2 := iv_imp_ii
  tfae_have 3 → 5 := iii_imp_v
  tfae_have 5 → 6 := v_imp_vi
  tfae_have 6 → 5 := vi_imp_v
  tfae_have 5 → 8 := v_imp_viii
  tfae_have 6 → 7 := vi_imp_vii
  tfae_have 7 → 6 := vii_imp_vi
  tfae_have 8 → 5 := viii_imp_v
  tfae_have 5 → 9 := fun h => v_to_viii_imp_ix h (v_imp_vi h) (vi_imp_vii (v_imp_vi h)) (v_imp_viii h)
  tfae_have 9 → 10 := ix_imp_x
  tfae_have 10 ↔ 11 := x_iff_xi
  tfae_have 10 → 8 := x_imp_viii
  tfae_have 5 → 4 := fun hv => v_to_xi_imp_iv hf hv (v_imp_vi hv) (vi_imp_vii (v_imp_vi hv))
    (v_imp_viii hv) (v_to_viii_imp_ix hv (v_imp_vi hv) (vi_imp_vii (v_imp_vi hv)) (v_imp_viii hv))
    (ix_imp_x (v_to_viii_imp_ix hv (v_imp_vi hv) (vi_imp_vii (v_imp_vi hv)) (v_imp_viii hv)))
    (x_iff_xi.mp (ix_imp_x (v_to_viii_imp_ix hv (v_imp_vi hv) (vi_imp_vii (v_imp_vi hv)) (v_imp_viii hv))))
  tfae_finish

/-- Exercise 1.3.3(i) -/
theorem Continuous.UnsignedMeasurable {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: Continuous f) (hnonneg: Unsigned f): UnsignedMeasurable f := by sorry

/-- Exercise 1.3.3(ii) -/
theorem UnsignedSimpleFunction.unsignedMeasurable {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f): UnsignedMeasurable f := by sorry

/-- Exercise 1.3.3(iii) -/
theorem UnsignedMeasurable.sup {d:ℕ} {f: ℕ → EuclideanSpace' d → EReal} (hf: ∀ n, UnsignedMeasurable (f n)) : UnsignedMeasurable (fun x ↦ iSup (fun n ↦ f n x)) := by sorry

/-- Exercise 1.3.3(iii) -/
theorem UnsignedMeasurable.inf {d:ℕ} {f: ℕ → EuclideanSpace' d → EReal} (hf: ∀ n, UnsignedMeasurable (f n)) : UnsignedMeasurable (fun x ↦ iInf (fun n ↦ f n x)) := by sorry

/-- Exercise 1.3.3(iii) -/
theorem UnsignedMeasurable.limsup {d:ℕ} {f: ℕ → EuclideanSpace' d → EReal} (hf: ∀ n, UnsignedMeasurable (f n)) : UnsignedMeasurable (fun x ↦ Filter.atTop.limsup (fun n ↦ f n x) ) := by sorry

/-- Exercise 1.3.3(iii) -/
theorem UnsignedMeasurable.liminf {d:ℕ} {f: ℕ → EuclideanSpace' d → EReal} (hf: ∀ n, UnsignedMeasurable (f n)) : UnsignedMeasurable (fun x ↦ Filter.atTop.liminf (fun n ↦ f n x) ) := by sorry

/-- Exercise 1.3.3(iv) -/
theorem UnsignedMeasurable.aeEqual {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (heq: AlmostEverywhereEqual f g) : UnsignedMeasurable g := by sorry

/-- Exercise 1.3.3(v) -/
theorem UnsignedMeasurable.aeLimit {d:ℕ} {f: EuclideanSpace' d → EReal} (g: ℕ → EuclideanSpace' d → EReal) (hf: ∀ n, UnsignedMeasurable (g n)) (heq: PointwiseAeConvergesTo g f) : UnsignedMeasurable f := by sorry

/-- Exercise 1.3.3(vi) -/
theorem UnsignedMeasurable.comp_cts {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) {φ: EReal → EReal} (hφ: Continuous φ)  : UnsignedMeasurable (φ ∘ f) := by sorry

/-- Exercise 1.3.3(vii) -/
theorem UnsignedMeasurable.add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g) : UnsignedMeasurable (f + g) := by sorry

def UniformConvergesTo {X:Type*} (f: ℕ → X → EReal) (g: X → EReal) : Prop := ∀ ε:NNReal, ε > 0 → ∃ N:ℕ, ∀ n ≥ N, ∀ x, f n x > g x - ε ∧ f n x < g x + ε

/-- Exercise 1.3.4 -/
theorem UnsignedMeasurable.bounded_iff {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: Unsigned f) : UnsignedMeasurable f ∧ EReal.BoundedFunction f ↔ ∃ g : ℕ → EuclideanSpace' d → EReal, (∀ n, UnsignedSimpleFunction (g n) ∧ EReal.BoundedFunction (g n)) ∧ UniformConvergesTo g f := by sorry

/-- Exercise 1.3.5 -/
theorem UnsignedSimpleFunction.iff {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: Unsigned f) : UnsignedSimpleFunction f ↔ UnsignedMeasurable f ∧ Finite (f '' Set.univ) := by sorry

/-- Exercise 1.3.6 -/
theorem UnsignedMeasurable.measurable_graph {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) : LebesgueMeasurable { p | ∃ x, ∃ t:ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } := by sorry

/-- Remark 1.3.10 -/
example : ∃ (f: EuclideanSpace' 1 → EReal) (hf: UnsignedMeasurable f) (E: Set (EuclideanSpace' 1)) (hE: LebesgueMeasurable E), ¬ LebesgueMeasurable (f⁻¹' ((Real.toEReal ∘ EuclideanSpace'.equiv_Real) '' E)) := by sorry

/-- Definition 1.3.11 (Complex measurability)-/
def ComplexMeasurable {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop := ∃ (g: ℕ → EuclideanSpace' d → ℂ), (∀ n, ComplexSimpleFunction (g n)) ∧ (PointwiseConvergesTo g f)

def RealMeasurable {d:ℕ} (f: EuclideanSpace' d → ℝ) : Prop := ∃ (g: ℕ → EuclideanSpace' d → ℝ), (∀ n, RealSimpleFunction (g n)) ∧ (PointwiseConvergesTo g f)

theorem RealMeasurable.iff {d:ℕ} {f: EuclideanSpace' d → ℝ} : RealMeasurable f ↔ ComplexMeasurable (Real.complex_fun f) := by sorry

theorem ComplexMeasurable.iff {d:ℕ} {f: EuclideanSpace' d → ℂ} : ComplexMeasurable f ↔ RealMeasurable (Complex.re_fun f) ∧ RealMeasurable (Complex.im_fun f) := by sorry

/-- Exercise 1.3.7 -/
theorem RealMeasurable.TFAE {d:ℕ} {f: EuclideanSpace' d → ℝ}:
    [
      RealMeasurable f,
      ∃ (g: ℕ → EuclideanSpace' d → ℝ), (∀ n, RealSimpleFunction (g n)) ∧ (PointwiseAeConvergesTo g f),
      UnsignedMeasurable (EReal.pos_fun f) ∧ UnsignedMeasurable (EReal.neg_fun f),
      ∀ U: Set ℝ, IsOpen U → MeasurableSet (f⁻¹' U),
      ∀ K: Set ℝ, IsClosed K → MeasurableSet (f⁻¹' K)
    ].TFAE
  := by sorry

theorem ComplexMeasurable.TFAE {d:ℕ} {f: EuclideanSpace' d → ℂ}:
    [
      ComplexMeasurable f,
      ∃ (g: ℕ → EuclideanSpace' d → ℂ), (∀ n, ComplexSimpleFunction (g n)) ∧ (PointwiseAeConvergesTo g f),
      RealMeasurable (Complex.re_fun f) ∧ RealMeasurable (Complex.im_fun f),
      UnsignedMeasurable (EReal.pos_fun (Complex.re_fun f)) ∧ UnsignedMeasurable (EReal.neg_fun (Complex.im_fun f)) ∧ UnsignedMeasurable (EReal.pos_fun (Complex.im_fun f)) ∧ UnsignedMeasurable (EReal.neg_fun (Complex.re_fun f)),
      ∀ U: Set ℂ, IsOpen U → MeasurableSet (f⁻¹' U),
      ∀ K: Set ℂ, IsClosed K → MeasurableSet (f⁻¹' K)
    ].TFAE
  := by sorry

/-- Exercise 1.3.8(i) -/
theorem Continuous.RealMeasurable {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: Continuous f) : RealMeasurable f := by sorry

theorem Continuous.ComplexMeasurable {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: Continuous f) : ComplexMeasurable f := by sorry

/-- Exercise 1.3.8(ii) -/
theorem UnsignedSimpleFunction.iff' {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: Unsigned f) : UnsignedSimpleFunction f ↔ UnsignedMeasurable f ∧ Finite (f '' Set.univ) := by sorry

/-- Exercise 1.3.8(iii) -/
theorem RealMeasurable.aeEqual {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) (heq: AlmostEverywhereEqual f g) : RealMeasurable g := by sorry

theorem ComplexMeasurable.aeEqual {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexMeasurable f) (heq: AlmostEverywhereEqual f g) : ComplexMeasurable g := by sorry

/-- Exercise 1.3.8(iv) -/
theorem RealMeasurable.aeLimit {d:ℕ} {f: EuclideanSpace' d → ℝ} (g: ℕ → EuclideanSpace' d → ℝ) (hf: ∀ n, RealMeasurable (g n)) (heq: PointwiseAeConvergesTo g f) : RealMeasurable f := by sorry

theorem ComplexMeasurable.aeLimit {d:ℕ} {f: EuclideanSpace' d → ℂ} (g: ℕ → EuclideanSpace' d → ℂ) (hf: ∀ n, ComplexMeasurable (g n)) (heq: PointwiseAeConvergesTo g f) : ComplexMeasurable f := by sorry

/-- Exercise 1.3.8(v) -/
theorem RealMeasurable.comp_cts {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) {φ: ℝ → ℝ} (hφ: Continuous φ)  : RealMeasurable (φ ∘ f) := by sorry

theorem ComplexMeasurable.comp_cts {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexMeasurable f) {φ: ℂ → ℂ} (hφ: Continuous φ)  : ComplexMeasurable (φ ∘ f) := by sorry

/-- Exercise 1.3.8(vi) -/
theorem RealMeasurable.add {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) (hg: RealMeasurable g) : RealMeasurable (f + g) := by sorry

theorem ComplexMeasurable.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexMeasurable f) (hg: ComplexMeasurable g) : ComplexMeasurable (f + g) := by sorry

/-- Exercise 1.3.8(vi) -/
theorem RealMeasurable.sub {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) (hg: RealMeasurable g) : RealMeasurable (f - g) := by sorry

theorem ComplexMeasurable.sub {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexMeasurable f) (hg: ComplexMeasurable g) : ComplexMeasurable (f - g) := by sorry

/-- Exercise 1.3.8(vi) -/
theorem RealMeasurable.mul {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) (hg: RealMeasurable g) : RealMeasurable (f * g) := by sorry

theorem ComplexMeasurable.mul {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexMeasurable f) (hg: ComplexMeasurable g) : ComplexMeasurable (f * g) := by sorry


open Classical in
/-- Exercise 1.3.9 -/
theorem RealMeasurable.riemann_integrable {f: ℝ → ℝ} {I: BoundedInterval} (hf: RiemannIntegrableOn f I) : RealMeasurable ((fun x ↦ if x ∈ I.toSet then f x else 0) ∘ EuclideanSpace'.equiv_Real) := by sorry
