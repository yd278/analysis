import Analysis.MeasureTheory.Section_1_2_3

/-!
# Introduction to Measure Theory, Section 1.3.1: Integration of simple functions

A companion to (the introduction to) Section 1.3.1 of the book "An introduction to Measure Theory".

-/

-- some tools to convert between EReal-valued, ℝ-valued, and ℂ-valued functions

def EReal.abs_fun {X Y:Type*} [RCLike Y] (f: X → Y) : X → EReal := fun x ↦ ‖f x‖.toEReal
def Complex.re_fun {X:Type*} (f: X → ℂ) : X → ℝ := fun x ↦ Complex.re (f x)
def Complex.im_fun {X:Type*} (f: X → ℂ) : X → ℝ := fun x ↦ Complex.im (f x)
def Complex.conj_fun {X:Type*} (f: X → ℂ) : X → ℂ := fun x ↦ starRingEnd ℂ (f x)
def EReal.pos_fun {X:Type*} (f: X → ℝ) : X → EReal := fun x ↦ (max (f x) 0).toEReal
def EReal.neg_fun {X:Type*} (f: X → ℝ) : X → EReal := fun x ↦ (max (-f x) 0).toEReal
def Real.complex_fun {X:Type*} (f: X → ℝ) : X → ℂ := fun x ↦ Complex.ofReal (f x)
def Real.EReal_fun {X:Type*} (f: X → ℝ) : X → EReal := fun x ↦ Real.toEReal (f x)

noncomputable def EReal.indicator {X:Type*} (A: Set X) : X → EReal := Real.EReal_fun A.indicator'
noncomputable def Complex.indicator {X:Type*} (A: Set X) : X → ℂ := Real.complex_fun A.indicator'

/-- Definition 1.3.2 -/
def UnsignedSimpleFunction {d:ℕ} (f: EuclideanSpace' d → EReal) : Prop := ∃ (k:ℕ) (c: Fin k → EReal) (E: Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i) ∧ c i ≥ 0) ∧ f = ∑ i, (c i) • (EReal.indicator (E i))

def RealSimpleFunction {d:ℕ} (f: EuclideanSpace' d → ℝ) : Prop := ∃ (k:ℕ) (c: Fin k → ℝ) (E: Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i)) ∧ f = ∑ i, (c i) • (E i).indicator'

def ComplexSimpleFunction {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop := ∃ (k:ℕ) (c: Fin k → ℂ) (E: Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i)) ∧ f = ∑ i, (c i) • (Complex.indicator (E i))

-- TODO: coercions between these concepts, and vector space structure on real and complex simple functions (and cone structure on unsigned simple functions).


@[coe]
abbrev RealSimpleFunction.toComplex {d:ℕ} (f: EuclideanSpace' d → ℝ) (df: RealSimpleFunction f) : ComplexSimpleFunction (Real.complex_fun f) := by sorry

instance RealSimpleFunction.coe_complex {d:ℕ} (f: EuclideanSpace' d → ℝ) : Coe (RealSimpleFunction f) (ComplexSimpleFunction (Real.complex_fun f)) := {
  coe := RealSimpleFunction.toComplex f
}


lemma UnsignedSimpleFunction.add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g) : UnsignedSimpleFunction (f + g) := by
  obtain ⟨k₁, c₁, E₁, ⟨hmes₁, heq₁⟩⟩ := hf
  obtain ⟨k₂, c₂, E₂, ⟨hmes₂, heq₂⟩⟩ := hg
  use k₁ + k₂, fun i => if h : i < k₁ then c₁ ⟨i, h⟩ else c₂ ⟨i - k₁, by omega⟩,
       fun i => if h : i < k₁ then E₁ ⟨i, h⟩ else E₂ ⟨i - k₁, by omega⟩
  constructor
  · intro i
    split_ifs with h
    · exact hmes₁ ⟨i, h⟩
    · exact hmes₂ ⟨i - k₁, by omega⟩
  · ext x
    rw [heq₁, heq₂]
    simp [Fin.sum_univ_add]

private lemma EReal.indicator_nonneg' {X:Type*} (A: Set X) (x : X) : 0 ≤ EReal.indicator A x := by
  simp only [EReal.indicator, Real.EReal_fun]
  exact EReal.coe_nonneg.mpr (Set.indicator_nonneg (fun _ _ => zero_le_one) x)

lemma UnsignedSimpleFunction.smul {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) {a: EReal} (ha: a ≥ 0) : UnsignedSimpleFunction (a • f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => a * (c i), E
  constructor
  · intro i
    exact ⟨hmes i |>.1, mul_nonneg ha (hmes i |>.2)⟩
  · rw [heq]
    ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [EReal.mul_finset_sum_of_nonneg k a (fun i => (c i) * EReal.indicator (E i) x)
        (fun i => mul_nonneg (hmes i |>.2) (EReal.indicator_nonneg' (E i) x))]
    congr 1
    ext i
    rw [mul_assoc]

lemma RealSimpleFunction.add {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) (hg: RealSimpleFunction g) : RealSimpleFunction (f + g) := by
  obtain ⟨k₁, c₁, E₁, ⟨hmes₁, heq₁⟩⟩ := hf
  obtain ⟨k₂, c₂, E₂, ⟨hmes₂, heq₂⟩⟩ := hg
  use k₁ + k₂, fun i => if h : i < k₁ then c₁ ⟨i, h⟩ else c₂ ⟨i - k₁, by omega⟩,
       fun i => if h : i < k₁ then E₁ ⟨i, h⟩ else E₂ ⟨i - k₁, by omega⟩
  constructor
  · intro i
    split_ifs with h
    · exact hmes₁ ⟨i, h⟩
    · exact hmes₂ ⟨i - k₁, by omega⟩
  · ext x
    rw [heq₁, heq₂]
    simp [Fin.sum_univ_add]

lemma ComplexSimpleFunction.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) (hg: ComplexSimpleFunction g) : ComplexSimpleFunction (f + g) := by
  obtain ⟨k₁, c₁, E₁, ⟨hmes₁, heq₁⟩⟩ := hf
  obtain ⟨k₂, c₂, E₂, ⟨hmes₂, heq₂⟩⟩ := hg
  use k₁ + k₂, fun i => if h : i < k₁ then c₁ ⟨i, h⟩ else c₂ ⟨i - k₁, by omega⟩,
       fun i => if h : i < k₁ then E₁ ⟨i, h⟩ else E₂ ⟨i - k₁, by omega⟩
  constructor
  · intro i
    split_ifs with h
    · exact hmes₁ ⟨i, h⟩
    · exact hmes₂ ⟨i - k₁, by omega⟩
  · ext x
    rw [heq₁, heq₂]
    simp [Fin.sum_univ_add]

lemma RealSimpleFunction.smul {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) (a: ℝ)  : RealSimpleFunction (a • f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => a * (c i), E
  constructor
  · intro i
    exact hmes i
  · rw [heq]
    ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    ext i
    rw [mul_assoc]

lemma ComplexSimpleFunction.smul {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) (a: ℂ)  : ComplexSimpleFunction (a • f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => a * (c i), E
  constructor
  · intro i
    exact hmes i
  · rw [heq]
    ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    ext i
    rw [mul_assoc]

private lemma Complex.indicator_conj {X:Type*} (A: Set X) (x : X) :
    starRingEnd ℂ (Complex.indicator A x) = Complex.indicator A x := by
  simp only [Complex.indicator, Real.complex_fun]
  exact Complex.conj_ofReal _

lemma ComplexSimpleFunction.conj {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : ComplexSimpleFunction (Complex.conj_fun f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => starRingEnd ℂ (c i), E
  constructor
  · intro i
    exact hmes i
  · rw [heq]
    ext x
    simp only [Complex.conj_fun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [map_sum]
    congr 1
    ext i
    rw [map_mul, Complex.indicator_conj]

noncomputable def UnsignedSimpleFunction.integ {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) : EReal := ∑ i, (hf.choose_spec.choose i) * Lebesgue_measure (hf.choose_spec.choose_spec.choose i)

/-! ### Helper lemmas for Lemma 1.3.4

The proof uses a Venn diagram argument: given two representations of the same simple function,
we partition R^d into atoms (intersections of all sets and their complements), express each
original set as a disjoint union of atoms, and use finite additivity of Lebesgue measure.
-/

namespace UnsignedSimpleFunction.IntegralWellDef

/-- Given families of sets indexed by Fin k and Fin k', an atom is determined by
    a choice of "in" or "out" for each set. We encode this as a Fin (2^(k+k')) index. -/
def atomMembership (_k _k' : ℕ) (n : ℕ) (i : ℕ) : Bool := (n / 2^i) % 2 = 1

lemma atomMembership_eq_testBit (k k' n i : ℕ) : atomMembership k k' n i = n.testBit i := by
  simp only [atomMembership, Nat.testBit_eq_decide_div_mod_eq]

/-- The atom indexed by n is the intersection over all i of (E_i if bit i is 1, else E_i^c) -/
def atom {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (n : Fin (2^(k+k'))) : Set X :=
  {x | (∀ i : Fin k, atomMembership k k' n i ↔ x ∈ E i) ∧
       (∀ i : Fin k', atomMembership k k' n (k + i) ↔ x ∈ E' i)}

/-- Atoms are pairwise disjoint -/
lemma atom_pairwiseDisjoint {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) :
    Set.univ.PairwiseDisjoint (atom E E') := by
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro x hxi hxj
  simp only [atom, Set.mem_setOf_eq, atomMembership_eq_testBit] at hxi hxj
  -- If i ≠ j, they differ in some bit
  have hne : i.val ≠ j.val := Fin.val_ne_of_ne hij
  obtain ⟨bit, hbit⟩ := Nat.exists_testBit_ne_of_ne hne
  -- The bit must be < k + k' since both i, j < 2^(k+k')
  have hi_lt : i.val < 2^(k + k') := i.isLt
  have hj_lt : j.val < 2^(k + k') := j.isLt
  have hbit_bound : bit < k + k' := by
    by_contra h
    push_neg at h
    have hi_false : i.val.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi_lt (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h))
    have hj_false : j.val.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hj_lt (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h))
    exact hbit (hi_false.trans hj_false.symm)
  -- Now we know bit < k + k', so it indexes into E or E'
  by_cases hbit_k : bit < k
  · -- bit indexes into E
    have hi_iff := hxi.1 ⟨bit, hbit_k⟩
    have hj_iff := hxj.1 ⟨bit, hbit_k⟩
    -- hxi and hxj both give x ∈ E ⟨bit, _⟩ ↔ testBit = true
    -- But i and j have different bits, so one says x ∈ E and the other says x ∉ E
    cases h_i : i.val.testBit bit <;> cases h_j : j.val.testBit bit
    · exact hbit (h_i.trans h_j.symm)
    · have hx_in : x ∈ E ⟨bit, hbit_k⟩ := hj_iff.mp h_j
      have hx_out : x ∉ E ⟨bit, hbit_k⟩ := fun h => by simp [hi_iff.mpr h] at h_i
      exact hx_out hx_in
    · have hx_in : x ∈ E ⟨bit, hbit_k⟩ := hi_iff.mp h_i
      have hx_out : x ∉ E ⟨bit, hbit_k⟩ := fun h => by simp [hj_iff.mpr h] at h_j
      exact hx_out hx_in
    · exact hbit (h_i.trans h_j.symm)
  · -- bit indexes into E' (bit ∈ [k, k+k'))
    have hbit_k' : bit - k < k' := by omega
    have h_add : k + (bit - k) = bit := by omega
    have hi_iff := hxi.2 ⟨bit - k, hbit_k'⟩
    have hj_iff := hxj.2 ⟨bit - k, hbit_k'⟩
    simp only [h_add] at hi_iff hj_iff
    cases h_i : i.val.testBit bit <;> cases h_j : j.val.testBit bit
    · exact hbit (h_i.trans h_j.symm)
    · have hx_in : x ∈ E' ⟨bit - k, hbit_k'⟩ := hj_iff.mp h_j
      have hx_out : x ∉ E' ⟨bit - k, hbit_k'⟩ := fun h => by simp [hi_iff.mpr h] at h_i
      exact hx_out hx_in
    · have hx_in : x ∈ E' ⟨bit - k, hbit_k'⟩ := hi_iff.mp h_i
      have hx_out : x ∉ E' ⟨bit - k, hbit_k'⟩ := fun h => by simp [hj_iff.mpr h] at h_j
      exact hx_out hx_in
    · exact hbit (h_i.trans h_j.symm)

/-- Each point belongs to exactly one atom -/
lemma mem_atom_unique {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) :
    ∃! n : Fin (2^(k+k')), x ∈ atom E E' n := by
  -- The atom is determined uniquely by the membership pattern of x
  -- Existence: construct the atom index from membership in E_i and E'_j
  -- Uniqueness: follows from atom_pairwiseDisjoint
  sorry

/-- The atom containing a given point -/
noncomputable def atomOf {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) : Fin (2^(k+k')) :=
  (mem_atom_unique E E' x).choose

/-- Original set E_i is the union of atoms where bit i is 1 -/
lemma set_eq_biUnion_atoms {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (i : Fin k) :
    E i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n i}, atom E E' n := by
  sorry

/-- Atoms are measurable if the original sets are -/
lemma atom_measurable {d k k' : ℕ} {E : Fin k → Set (EuclideanSpace' d)} {E' : Fin k' → Set (EuclideanSpace' d)}
    (hE : ∀ i, LebesgueMeasurable (E i)) (hE' : ∀ i, LebesgueMeasurable (E' i)) (n : Fin (2^(k+k'))) :
    LebesgueMeasurable (atom E E' n) := by
  sorry

/-- Key: at any point, the sum of c_i over sets containing that point equals the function value -/
lemma sum_at_point {d k : ℕ} {c : Fin k → EReal} {E : Fin k → Set (EuclideanSpace' d)}
    (_hnonneg : ∀ i, c i ≥ 0) (x : EuclideanSpace' d) :
    (∑ i, (c i) • (EReal.indicator (E i))) x = ∑ i, (c i) * (EReal.indicator (E i) x) := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Indicator function evaluates to c if x ∈ E -/
lemma indicator_mul_mem {d : ℕ} (E : Set (EuclideanSpace' d)) (c : EReal) (x : EuclideanSpace' d)
    (h : x ∈ E) : c * (EReal.indicator E x) = c := by
  simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem h, EReal.coe_one, mul_one]

/-- Indicator function evaluates to 0 if x ∉ E -/
lemma indicator_mul_not_mem {d : ℕ} (E : Set (EuclideanSpace' d)) (c : EReal) (x : EuclideanSpace' d)
    (h : x ∉ E) : c * (EReal.indicator E x) = 0 := by
  simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem h, EReal.coe_zero, mul_zero]

/-- The weighted measure sum for a representation -/
noncomputable def weightedMeasureSum {d k : ℕ} (c : Fin k → EReal) (E : Fin k → Set (EuclideanSpace' d)) : EReal :=
  ∑ i, (c i) * Lebesgue_measure (E i)

/-- Core lemma: Two representations of the same function give the same weighted measure sum.
    This is the heart of Lemma 1.3.4 (Venn diagram argument). -/
lemma weightedMeasureSum_eq_of_eq {d k k' : ℕ}
    {c : Fin k → EReal} {E : Fin k → Set (EuclideanSpace' d)}
    {c' : Fin k' → EReal} {E' : Fin k' → Set (EuclideanSpace' d)}
    (hmes : ∀ i, LebesgueMeasurable (E i)) (hmes' : ∀ i, LebesgueMeasurable (E' i))
    (hnonneg : ∀ i, c i ≥ 0) (hnonneg' : ∀ i, c' i ≥ 0)
    (heq : ∑ i, (c i) • (EReal.indicator (E i)) = ∑ i, (c' i) • (EReal.indicator (E' i))) :
    weightedMeasureSum c E = weightedMeasureSum c' E' := by
  -- The proof uses the Venn diagram/atom argument from the textbook
  -- 1. Construct atoms from E and E'
  -- 2. Express each E_i and E'_j as disjoint union of atoms
  -- 3. Use finite additivity: m(E_i) = ∑_{atoms ⊆ E_i} m(atom)
  -- 4. For any x in a non-empty atom, evaluate heq at x to get scalar identity
  -- 5. Multiply by atom measure and sum
  sorry

end UnsignedSimpleFunction.IntegralWellDef

/-- Lemma 1.3.4 (Well-definedness of simple integral) -/
lemma UnsignedSimpleFunction.integral_eq {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) {k:ℕ} {c: Fin k → EReal}
    {E: Fin k → Set (EuclideanSpace' d)} (hmes: ∀ i, LebesgueMeasurable (E i)) (hnonneg: ∀ i, c i ≥ 0)
    (heq: f = ∑ i, (c i) • (EReal.indicator (E i))) :
    hf.integ = ∑ i, (c i) * Lebesgue_measure (E i) := by
  -- Extract the canonical representation from hf
  -- hf gives: ∃ k', ∃ (c': Fin k' → EReal) (E': Fin k' → Set _), (∀ i, LebesgueMeasurable (E' i) ∧ c' i ≥ 0) ∧ f = ∑...
  -- hf.choose_spec.choose is c', hf.choose_spec.choose_spec.choose is E'
  let k' := hf.choose
  let c' := hf.choose_spec.choose
  let E' := hf.choose_spec.choose_spec.choose
  have hmes'_nonneg : ∀ i, LebesgueMeasurable (E' i) ∧ c' i ≥ 0 := hf.choose_spec.choose_spec.choose_spec.1
  have heq' : f = ∑ i, (c' i) • (EReal.indicator (E' i)) := hf.choose_spec.choose_spec.choose_spec.2

  -- The canonical representation also equals f
  have hfunc_eq : ∑ i, (c i) • (EReal.indicator (E i)) = ∑ i, (c' i) • (EReal.indicator (E' i)) := by
    rw [← heq, ← heq']

  -- Apply the core lemma: two representations of the same function give the same weighted measure
  have h := IntegralWellDef.weightedMeasureSum_eq_of_eq
    hmes (fun i => (hmes'_nonneg i).1) hnonneg (fun i => (hmes'_nonneg i).2) hfunc_eq

  -- h says: weightedMeasureSum c E = weightedMeasureSum c' E'
  -- Goal: ∑ i, (c' i) * Lebesgue_measure (E' i) = ∑ i, (c i) * Lebesgue_measure (E i)
  simp only [UnsignedSimpleFunction.IntegralWellDef.weightedMeasureSum] at h
  exact h.symm

/-- Definition 1.3.5 -/
def AlmostAlways {d:ℕ} (P: EuclideanSpace' d → Prop) : Prop :=
  IsNull { x | ¬ P x }

/-- Definition 1.3.5 -/
def AlmostEverywhereEqual {d:ℕ} {X: Type*} (f g: EuclideanSpace' d → X) : Prop :=
  AlmostAlways (fun x ↦ f x = g x)

/-- Definition 1.3.5 -/
def Support {X Y: Type*} [Zero Y] (f: X → Y) : Set X := { x | f x ≠ 0 }

lemma UnsignedSimpleFunction.support_measurable {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) : LebesgueMeasurable (Support f) := by
  sorry

lemma AlmostAlways.ofAlways {d:ℕ} {P: EuclideanSpace' d → Prop} (h: ∀ x, P x) : AlmostAlways P := by
  sorry

lemma AlmostAlways.mp {d:ℕ} {P Q: EuclideanSpace' d → Prop} (hP: AlmostAlways P) (himp: ∀ x, P x → Q x) : AlmostAlways Q := by
  sorry

lemma AlmostAlways.countable {d:ℕ} {I: Type*} [Countable I] {P: I → EuclideanSpace' d → Prop} (hP: ∀ i, AlmostAlways (P i)) : AlmostAlways (fun x ↦ ∀ i, P i x) := by
  sorry

-- TODO: AlmostEverywhereEqual is an Equiv

/-- Exercise 1.3.1 (i) (Unsigned linearity) -/
lemma UnsignedSimpleFunction.integral_add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g) :
  (hf.add hg).integ = hf.integ + hg.integ := by
  sorry

/-- Exercise 1.3.1 (i) (Unsigned linearity) -/
lemma UnsignedSimpleFunction.integral_smul {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) {c:EReal} (hc: c ≥ 0) :
  (hf.smul hc).integ = c * hf.integ := by
  sorry

/-- Exercise 1.3.1 (ii) (Finiteness) -/
lemma UnsignedSimpleFunction.integral_finite_iff {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) :
  (hf.integ < ⊤) ↔ (AlmostAlways (fun x ↦ f x < ⊤)) ∧ (Lebesgue_measure (Support f)) < ⊤ := by
  sorry

/-- Exercise 1.3.1 (iii) (Vanishing) -/
lemma UnsignedSimpleFunction.integral_eq_zero_iff {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) :
  (hf.integ = 0) ↔ AlmostAlways (fun x ↦ f x = 0) := by
  sorry

/-- Exercise 1.3.1 (iv) (Equivalence) -/
lemma UnsignedSimpleFunction.integral_eq_integral_of_aeEqual {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g)
  (hae: AlmostEverywhereEqual f g) :
  hf.integ = hg.integ := by
  sorry

/-- Exercise 1.3.1 (v) (Monotonicity) -/
lemma UnsignedSimpleFunction.integral_le_integral_of_aeLe {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g)
  (hae: AlmostAlways (fun x ↦ f x ≤ g x)) :
  hf.integ ≤ hg.integ := by
  sorry

/-- Exercise 1.3.1(vi) (Compatibility with Lebesgue measure) -/
lemma UnsignedSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  UnsignedSimpleFunction (Real.toEReal ∘ E.indicator') := by
  sorry

/-- Exercise 1.3.1(vi) (Compatibility with Lebesgue measure) -/
lemma UnsignedSimpleFunction.integral_indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  (UnsignedSimpleFunction.indicator hE).integ = Lebesgue_measure E := by
  sorry

lemma RealSimpleFunction.abs {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : UnsignedSimpleFunction (EReal.abs_fun f) := by
  sorry

lemma ComplexSimpleFunction.abs {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : UnsignedSimpleFunction (EReal.abs_fun f) := by
  sorry

/-- Definition 1.3.6 (Absolutely convergent simple integral) -/
def RealSimpleFunction.AbsolutelyIntegrable {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : Prop :=
  (hf.abs).integ < ⊤

/-- Definition 1.3.6 (Absolutely convergent simple integral) -/
def ComplexSimpleFunction.AbsolutelyIntegrable {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : Prop :=
  (hf.abs).integ < ⊤

def RealSimpleFunction.pos {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : UnsignedSimpleFunction (EReal.pos_fun f) := by sorry

def RealSimpleFunction.neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : UnsignedSimpleFunction (EReal.neg_fun f) := by sorry

noncomputable def RealSimpleFunction.integ {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : ℝ := (hf.pos).integ.toReal - (hf.neg).integ.toReal

def ComplexSimpleFunction.re {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : RealSimpleFunction (Complex.re_fun f) := by sorry

def ComplexSimpleFunction.im {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : RealSimpleFunction (Complex.im_fun f) := by sorry

noncomputable def ComplexSimpleFunction.integ {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : ℂ :=
  hf.re.integ + Complex.I * hf.im.integ

lemma RealSimpleFunction.absolutelyIntegrable_iff {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : hf.AbsolutelyIntegrable ↔ Lebesgue_measure (Support f) < ⊤ := by
  sorry

lemma ComplexSimpleFunction.absolutelyIntegrable_iff {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : hf.AbsolutelyIntegrable ↔ Lebesgue_measure (Support f) < ⊤ := by
  sorry

lemma RealSimpleFunction.AbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} {hg: RealSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) :
  (hf.add hg).AbsolutelyIntegrable := by sorry

lemma ComplexSimpleFunction.AbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} {hg: ComplexSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) :
  (hf.add hg).AbsolutelyIntegrable := by sorry

lemma RealSimpleFunction.AbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℝ) :
  (hf.smul a).AbsolutelyIntegrable := by sorry

lemma ComplexSimpleFunction.AbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℂ) :
  (hf.smul a).AbsolutelyIntegrable := by sorry

lemma ComplexSimpleFunction.AbsolutelyIntegrable.conj {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) :
  (hf.conj).AbsolutelyIntegrable := by sorry

/-- Exercise 1.3.2 (i) (*-linearity) -/
lemma RealSimpleFunction.integ_add {d:ℕ} {f g: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} {hg: RealSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) : (hf.add hg).integ = hf.integ + hg.integ := by sorry

lemma ComplexSimpleFunction.integ_add {d:ℕ} {f g: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} {hg: ComplexSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) : (hf.add hg).integ = hf.integ + hg.integ := by
  sorry

/-- Exercise 1.3.2 (i) (*-linearity) -/
lemma RealSimpleFunction.integ_smul {d:ℕ} {f: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℝ) : (hf.smul a).integ = a * hf.integ := by
  sorry

lemma ComplexSimpleFunction.integ_smul {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℂ) : (hf.smul a).integ = a * hf.integ := by
  sorry

/-- Exercise 1.3.2 (i) (*-linearity) -/
lemma ComplexSimpleFunction.integral_conj {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) : (hf.conj).integ = (starRingEnd ℂ) hf.integ := by
  sorry

/-- Exercise 1.3.2 (ii) (equivalence) -/
lemma RealSimpleFunction.integral_eq_integral_of_aeEqual {d:ℕ} {f g: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} {hg: RealSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) (h_ae: AlmostEverywhereEqual f g) : hf.integ = hg.integ := by
  sorry

lemma ComplexSimpleFunction.integral_eq_integral_of_aeEqual {d:ℕ} {f g: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} {hg: ComplexSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) (h_ae: AlmostEverywhereEqual f g) : hf.integ = hg.integ := by
  sorry

/-- Exercise 1.3.2(iii) (Compatibility with Lebesgue measure) -/
lemma RealSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  RealSimpleFunction (E.indicator') := by
  sorry

lemma ComplexSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  ComplexSimpleFunction (Complex.indicator E) := by
  sorry

/-- Exercise 1.3.2(iii) (Compatibility with Lebesgue measure) -/
lemma RealSimpleFunction.integral_indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hfin: Lebesgue_measure E < ⊤): (RealSimpleFunction.indicator hE).integ = (Lebesgue_measure E).toReal := by
  sorry

lemma ComplexSimpleFunction.integral_indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hfin: Lebesgue_measure E < ⊤): (ComplexSimpleFunction.indicator hE).integ = (Lebesgue_measure E).toReal := by
  sorry
