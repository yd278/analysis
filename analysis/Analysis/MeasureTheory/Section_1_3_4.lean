import Analysis.MeasureTheory.Section_1_3_3

/-!
# Introduction to Measure Theory, Section 1.3.4: Absolute integrability

A companion to (the introduction to) Section 1.3.4 of the book "An introduction to Measure Theory".

-/

-- It is probably possible to unify the real and complex theory here using the `RCLike` class in Mathlib, but we will adopt the more pedestrian approach of duplicating definitions in the real and complex cases.

/-- Definition 1.3.17 -/

def UnsignedAbsolutelyIntegrable {d:ℕ} (f: EuclideanSpace' d → EReal) : Prop := UnsignedMeasurable f ∧ UnsignedLebesgueIntegral f < ⊤

def ComplexAbsolutelyIntegrable {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop := ComplexMeasurable f ∧ UnsignedLebesgueIntegral (EReal.abs_fun f) < ⊤

def RealAbsolutelyIntegrable {d:ℕ} (f: EuclideanSpace' d → ℝ) : Prop := RealMeasurable f ∧ UnsignedLebesgueIntegral (EReal.abs_fun f) < ⊤

lemma ComplexAbsolutelyIntegrable.abs {d:ℕ} (f: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.abs_fun f) := by
  constructor
  · -- UnsignedMeasurable (EReal.abs_fun f)
    constructor
    · -- Unsigned: ∀ x, EReal.abs_fun f x ≥ 0
      intro x
      simp only [EReal.abs_fun]
      exact EReal.coe_nonneg.mpr (norm_nonneg _)
    · -- Exists approximating unsigned simple functions
      obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
      use fun n => EReal.abs_fun (g n)
      constructor
      · intro n; exact (hg_simple n).abs
      · intro x
        simp only [EReal.abs_fun]
        exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
  · exact hf.2

lemma RealAbsolutelyIntegrable.abs {d:ℕ} (f: EuclideanSpace' d → ℝ) (hf: RealAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.abs_fun f) := by
  constructor
  · -- UnsignedMeasurable (EReal.abs_fun f)
    constructor
    · intro x
      simp only [EReal.abs_fun]
      exact EReal.coe_nonneg.mpr (norm_nonneg _)
    · obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
      use fun n => EReal.abs_fun (g n)
      constructor
      · intro n; exact (hg_simple n).abs
      · intro x
        simp only [EReal.abs_fun]
        exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
  · exact hf.2



lemma RealAbsolutelyIntegrable.iff {d:ℕ} (f: EuclideanSpace' d → ℝ) : RealAbsolutelyIntegrable f ↔ ComplexAbsolutelyIntegrable (fun x ↦ (f x:ℂ)) := by
  constructor
  · intro ⟨hf_meas, hf_integ⟩
    constructor
    · exact RealMeasurable.iff.mp hf_meas
    · convert hf_integ using 2
      funext x
      simp only [EReal.abs_fun]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs]
  · intro ⟨hf_meas, hf_integ⟩
    constructor
    · exact RealMeasurable.iff.mpr hf_meas
    · convert hf_integ using 2
      funext x
      simp only [EReal.abs_fun]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs]

lemma ComplexAbsolutelyIntegrable.re {d:ℕ} (f: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) : RealAbsolutelyIntegrable (Complex.re_fun f) := by
  have h_re_meas : RealMeasurable (Complex.re_fun f) := ComplexMeasurable.iff.mp hf.1 |>.1
  constructor
  · exact h_re_meas
  · have h_le : ∀ x, EReal.abs_fun (Complex.re_fun f) x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun, Complex.re_fun]
      apply EReal.coe_le_coe_iff.mpr
      rw [Real.norm_eq_abs]
      exact Complex.abs_re_le_norm (f x)
    -- Build UnsignedMeasurable for |Re(f)| directly from RealMeasurable (re_fun f)
    have h_re_abs_meas : UnsignedMeasurable (EReal.abs_fun (Complex.re_fun f)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨g, hg_simple, hg_conv⟩ := h_re_meas
        use fun n => EReal.abs_fun (g n)
        constructor
        · intro n; exact (hg_simple n).abs
        · intro x
          simp only [EReal.abs_fun, Complex.re_fun]
          exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono
      · exact h_re_abs_meas
      · exact hf.abs.1
      · exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

lemma ComplexAbsolutelyIntegrable.im {d:ℕ} (f: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) : RealAbsolutelyIntegrable (Complex.im_fun f) := by
  have h_im_meas : RealMeasurable (Complex.im_fun f) := ComplexMeasurable.iff.mp hf.1 |>.2
  constructor
  · exact h_im_meas
  · have h_le : ∀ x, EReal.abs_fun (Complex.im_fun f) x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun, Complex.im_fun]
      apply EReal.coe_le_coe_iff.mpr
      rw [Real.norm_eq_abs]
      exact Complex.abs_im_le_norm (f x)
    -- Build UnsignedMeasurable for |Im(f)| directly from RealMeasurable (im_fun f)
    have h_im_abs_meas : UnsignedMeasurable (EReal.abs_fun (Complex.im_fun f)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨g, hg_simple, hg_conv⟩ := h_im_meas
        use fun n => EReal.abs_fun (g n)
        constructor
        · intro n; exact (hg_simple n).abs
        · intro x
          simp only [EReal.abs_fun, Complex.im_fun]
          exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono
      · exact h_im_abs_meas
      · exact hf.abs.1
      · exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

lemma ComplexAbsolutelyIntegrable.iff {d:ℕ} (f: EuclideanSpace' d → ℂ) : ComplexAbsolutelyIntegrable f ↔ RealAbsolutelyIntegrable (Complex.re_fun f) ∧ RealAbsolutelyIntegrable (Complex.im_fun f) := by
  constructor
  · intro hf
    exact ⟨ComplexAbsolutelyIntegrable.re f hf, ComplexAbsolutelyIntegrable.im f hf⟩
  · intro ⟨hre, him⟩
    constructor
    · exact ComplexMeasurable.iff.mpr ⟨hre.1, him.1⟩
    · -- Use |f| ≤ |Re(f)| + |Im(f)| to bound the integral
      have h_bound : ∀ x, EReal.abs_fun f x ≤
          (EReal.abs_fun (Complex.re_fun f) + EReal.abs_fun (Complex.im_fun f)) x := fun x => by
        simp only [EReal.abs_fun, Complex.re_fun, Complex.im_fun, Pi.add_apply]
        apply EReal.coe_le_coe_iff.mpr
        calc ‖f x‖ = Real.sqrt ((f x).re^2 + (f x).im^2) := Complex.norm_eq_sqrt_sq_add_sq (f x)
          _ ≤ |((f x).re)| + |(f x).im| := by
            have h1 : (f x).re^2 + (f x).im^2 ≤ (|(f x).re| + |(f x).im|)^2 := by
              have h_cross : 0 ≤ 2 * |(f x).re| * |(f x).im| := by positivity
              calc (f x).re^2 + (f x).im^2
                  ≤ (f x).re^2 + 2 * |(f x).re| * |(f x).im| + (f x).im^2 := by linarith
                _ = |(f x).re|^2 + 2 * |(f x).re| * |(f x).im| + |(f x).im|^2 := by rw [sq_abs, sq_abs]
                _ = (|(f x).re| + |(f x).im|)^2 := by ring
            have h2 : 0 ≤ |(f x).re| + |(f x).im| := by positivity
            calc Real.sqrt ((f x).re^2 + (f x).im^2)
                ≤ Real.sqrt ((|(f x).re| + |(f x).im|)^2) := Real.sqrt_le_sqrt h1
              _ = |(f x).re| + |(f x).im| := Real.sqrt_sq h2
          _ = ‖(f x).re‖ + ‖(f x).im‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      -- Apply monotonicity and additivity of integral
      have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun f) ≤
                    UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f) +
                                              EReal.abs_fun (Complex.im_fun f)) := by
        apply LowerUnsignedLebesgueIntegral.mono
        · constructor
          · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
          · obtain ⟨g, hg_simple, hg_conv⟩ := ComplexMeasurable.iff.mpr ⟨hre.1, him.1⟩
            use fun n => EReal.abs_fun (g n)
            constructor
            · intro n; exact (hg_simple n).abs
            · intro x
              simp only [EReal.abs_fun]
              exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
        · exact hre.abs.1.add him.abs.1
        · exact AlmostAlways.ofAlways h_bound
      -- UnsignedLebesgueIntegral is defined as LowerUnsignedLebesgueIntegral
      have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f) +
                                             EReal.abs_fun (Complex.im_fun f)) =
                   UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f)) +
                   UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f)) := by
        exact LowerUnsignedLebesgueIntegral.add hre.abs.1 him.abs.1
          (UnsignedMeasurable.add hre.abs.1 him.abs.1)
      rw [h_add] at h_mono
      calc UnsignedLebesgueIntegral (EReal.abs_fun f)
          ≤ UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f)) +
            UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f)) := h_mono
        _ < ⊤ := EReal.add_lt_top (lt_top_iff_ne_top.mp hre.2) (lt_top_iff_ne_top.mp him.2)

noncomputable def UnsignedAbsolutelyIntegrable.integ {d:ℕ} (f: EuclideanSpace' d → EReal) (_: UnsignedAbsolutelyIntegrable f) : ℝ := (UnsignedLebesgueIntegral f).toReal

noncomputable def ComplexAbsolutelyIntegrable.norm {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ℝ := hf.abs.integ

noncomputable def RealAbsolutelyIntegrable.norm {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : ℝ := hf.abs.integ


def RealMeasurable.measurable_pos {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) : UnsignedMeasurable (EReal.pos_fun f) := by sorry

def RealMeasurable.measurable_neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) : UnsignedMeasurable (EReal.neg_fun f) := by sorry

def RealAbsolutelyIntegrable.pos {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.pos_fun f) := by sorry

def RealAbsolutelyIntegrable.neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.neg_fun f) := by sorry

noncomputable def RealAbsolutelyIntegrable.integ {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : ℝ := hf.pos.integ - hf.neg.integ

noncomputable def ComplexAbsolutelyIntegrable.integ {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ℂ := hf.re.integ + Complex.I * hf.im.integ

open Classical in
noncomputable def RealLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → ℝ) : ℝ  := if hf: RealAbsolutelyIntegrable f then hf.integ else 0

open Classical in
noncomputable def ComplexLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → ℂ) : ℂ  := if hf: ComplexAbsolutelyIntegrable f then hf.integ else 0

def RealSimpleFunction.absolutelyIntegrable_iff' {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : hf.AbsolutelyIntegrable ↔ RealAbsolutelyIntegrable f := by sorry

def ComplexSimpleFunction.absolutelyIntegrable_iff' {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : hf.AbsolutelyIntegrable ↔ ComplexAbsolutelyIntegrable f := by sorry

def RealSimpleFunction.AbsolutelyIntegrable.integ_eq {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) (hfi: hf.AbsolutelyIntegrable) : hf.integ = (hf.absolutelyIntegrable_iff'.mp hfi).integ := by sorry

def ComplexSimpleFunction.AbsolutelyIntegrable.integ_eq {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) (hfi: hf.AbsolutelyIntegrable) : hf.integ = (hf.absolutelyIntegrable_iff'.mp hfi).integ := by sorry

theorem RealAbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (hg: RealAbsolutelyIntegrable g) : RealAbsolutelyIntegrable (f + g) := by sorry

theorem ComplexAbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : ComplexAbsolutelyIntegrable (f + g) := by sorry

theorem RealAbsolutelyIntegrable.sub {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (hg: RealAbsolutelyIntegrable g) : RealAbsolutelyIntegrable (f - g) := by sorry

theorem ComplexAbsolutelyIntegrable.sub {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : ComplexAbsolutelyIntegrable (f - g) := by sorry

theorem RealAbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (c:ℝ) : RealAbsolutelyIntegrable (c • f) := by sorry

theorem ComplexAbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (c:ℂ) : ComplexAbsolutelyIntegrable (c • f) := by sorry

theorem RealAbsolutelyIntegrable.of_neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : RealAbsolutelyIntegrable (-f) := by sorry

theorem ComplexAbsolutelyIntegrable.of_neg {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ComplexAbsolutelyIntegrable (-f) := by sorry

theorem ComplexAbsolutelyIntegrable.conj {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ComplexAbsolutelyIntegrable (Complex.conj_fun f) := by sorry

@[ext]
structure PreL1 (d:ℕ) where
  f : EuclideanSpace' d → ℂ
  integrable : ComplexAbsolutelyIntegrable f

noncomputable def PreL1.norm {d:ℕ} {X:Type*} [RCLike X] (f: EuclideanSpace' d → X) := UnsignedLebesgueIntegral (EReal.abs_fun f)

def ComplexAbsolutelyIntegrable.to_PreL1 {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : PreL1 d := ⟨ f, hf ⟩

def PreL1.conj {d:ℕ} (F: PreL1 d) : PreL1 d := ⟨ Complex.conj_fun F.f, F.integrable.conj ⟩

instance PreL1.inst_AddZeroClass {d:ℕ} : AddZeroClass (PreL1 d) := {
  zero := ⟨ 0, by sorry ⟩
  add F G := ⟨ F.f + G.f, F.integrable.add G.integrable ⟩
  zero_add := by sorry
  add_zero := by sorry
}

instance PreL1.inst_addCommMonoid {d:ℕ} : AddCommMonoid (PreL1 d) := {
  add_assoc := by sorry
  add_comm := by sorry
  nsmul := nsmulRec
}

instance PreL1.inst_Neg {d:ℕ} : Neg (PreL1 d) := {
  neg F := ⟨ -F.f, F.integrable.of_neg ⟩
}

instance PreL1.inst_module {d:ℕ} : Module ℂ (PreL1 d) := {
  smul c F := ⟨ c • F.f, F.integrable.smul c ⟩
  zero_smul := by sorry
  smul_zero := by sorry
  one_smul := by sorry
  mul_smul := by sorry
  smul_add := by sorry
  add_smul := by sorry
}

noncomputable instance PreL1.inst_seminormedAddCommGroup {d:ℕ} : SeminormedAddCommGroup (PreL1 d) := {
  norm F := F.integrable.norm
  neg F := ⟨ -F.f, F.integrable.of_neg ⟩
  zsmul := zsmulRec
  neg_add_cancel := by sorry
  dist_self := by sorry
  dist_comm := by sorry
  dist_triangle := by sorry
}

instance PreL1.inst_normedSpace {d:ℕ} : NormedSpace ℂ (PreL1 d) := {
  norm_smul_le := by sorry
}

theorem PreL1.dist_eq {d:ℕ} (F G: PreL1 d) : dist F G = ‖F-G‖ := rfl

noncomputable abbrev L1 (d:ℕ) := SeparationQuotient (PreL1 d)

@[coe]
def PreL1.toL1 {d:ℕ} (F: PreL1 d) : L1 d := SeparationQuotient.mk F

instance PreL1.inst_coeL1 {d:ℕ} : Coe (PreL1 d) (L1 d) := ⟨ PreL1.toL1 ⟩

def ComplexAbsolutelyIntegrable.toL1 {d:ℕ} {f:EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : L1 d := SeparationQuotient.mk hf.to_PreL1

theorem L1.dist_eq {d:ℕ} (f g: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : dist hf.toL1 hg.toL1 = (hf.sub hg).norm := by sorry

theorem L1.dist_eq_zero {d:ℕ} (f g: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : dist hf.toL1 hg.toL1 = 0 ↔ AlmostEverywhereEqual f g := by sorry

/-- Exercise 1.3.19 (Integration is linear) -/
noncomputable def L1.integ {d:ℕ} : L1 d →ₗ[ℂ] ℂ := {
  toFun := Quotient.lift (fun F ↦ F.integrable.integ) (by sorry)
  map_smul' := by sorry
  map_add' := by sorry
}

noncomputable def L1.conj {d:ℕ} : L1 d → L1 d := Quotient.lift (fun F ↦ (F.conj : L1 d)) (by sorry)

theorem L1.integ_conj {d:ℕ} (F: L1 d) : L1.integ (L1.conj F) = starRingEnd ℂ (L1.integ F) := by sorry

/-- Exercise 1.3.20 (Translation invariance)-/
theorem RealAbsolutelyIntegrable.trans {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (a: EuclideanSpace' d) : RealAbsolutelyIntegrable (fun x ↦ f (x + a)) := by sorry

theorem RealAbsolutelyIntegrable.integ_trans {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (a: EuclideanSpace' d) : (hf.trans a).integ = hf.integ  := by sorry

theorem ComplexAbsolutelyIntegrable.trans {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (a: EuclideanSpace' d) : ComplexAbsolutelyIntegrable (fun x ↦ f (x + a)) := by sorry

theorem ComplexAbsolutelyIntegrable.integ_trans {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (a: EuclideanSpace' d) : (hf.trans a).integ = hf.integ  := by sorry

/-- Exercise 1.3.20 (Linear change of variables)-/
theorem RealAbsolutelyIntegrable.comp_linear {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) {A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA: A.det ≠ 0) :
    RealAbsolutelyIntegrable (fun x ↦ f (A x)) := by sorry

theorem RealAbsolutelyIntegrable.integ_comp_linear {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) {A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA: A.det ≠ 0) :
    (hf.comp_linear hA).integ = |A.det|⁻¹ * hf.integ := by sorry

theorem ComplexAbsolutelyIntegrable.comp_linear {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) {A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA: A.det ≠ 0) :
    ComplexAbsolutelyIntegrable (fun x ↦ f (A x)) := by sorry

theorem ComplexAbsolutelyIntegrable.integ_comp_linear {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) {A: EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d} (hA: A.det ≠ 0) :
    (hf.comp_linear hA).integ = |A.det|⁻¹ * hf.integ := by sorry

/-- Exercise 1.3.20 (Compatibility with the Riemann integral)-/
theorem RiemannIntegrableOn.realAbsolutelyIntegrable {I: BoundedInterval} {f: ℝ → ℝ} (hf: RiemannIntegrableOn f I) : RealAbsolutelyIntegrable ((fun x ↦ (f x) * (I.toSet.indicator' x)) ∘ EuclideanSpace'.equiv_Real) := by sorry

theorem RiemannIntegral.eq_integ {I: BoundedInterval} {f: ℝ → ℝ} (hf: RiemannIntegrableOn f I) :
    riemannIntegral f I  = hf.realAbsolutelyIntegrable.integ := by sorry

/-- Exercise 1.3.21 (Absolute summability is a special case of absolute integrability)-/
theorem AbsolutelySummable.realAbsolutelyIntegrable_iff {a: ℤ → ℝ} : ∑' n, |a n|.toEReal < ⊤ ↔ RealAbsolutelyIntegrable (fun x ↦ a ⌊EuclideanSpace'.equiv_Real x⌋) := by sorry

theorem AbsolutelySummable.complexAbsolutelyIntegrable_iff {a: ℤ → ℂ} : ∑' n, ‖a n‖.toEReal < ⊤ ↔ ComplexAbsolutelyIntegrable (fun x ↦ a ⌊EuclideanSpace'.equiv_Real x⌋) := by sorry

def ComplexAbsolutelyIntegrableOn {d:ℕ} (f: EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)) : Prop := ComplexAbsolutelyIntegrable (f * Complex.indicator E)

noncomputable def ComplexAbsolutelyIntegrableOn.integ {d:ℕ} {f: EuclideanSpace' d → ℂ} {E: Set (EuclideanSpace' d)} (hf: ComplexAbsolutelyIntegrableOn f E) : ℂ :=
  ComplexAbsolutelyIntegrable.integ hf

/-- Exercise 1.3.22 -/
theorem ComplexAbsolutelyIntegrableOn.glue {d:ℕ} {f: EuclideanSpace' d → ℂ} {E F: Set (EuclideanSpace' d)} (hdisj: Disjoint E F) (hf: ComplexAbsolutelyIntegrableOn f (E ∪ F)) : ∃ hE : ComplexAbsolutelyIntegrableOn f E, ∃ hF: ComplexAbsolutelyIntegrableOn f F, hf.integ = hE.integ + hF.integ := by sorry

def ComplexAbsolutelyIntegrableOn.restrict {d:ℕ} {f: EuclideanSpace' d → ℂ} {E F: Set (EuclideanSpace' d)} (hf: ComplexAbsolutelyIntegrableOn f E) (hF: LebesgueMeasurable F): ComplexAbsolutelyIntegrableOn (f * Complex.indicator F) E := by sorry

def ComplexAbsolutelyIntegrableOn.mono {d:ℕ} {f: EuclideanSpace' d → ℂ} {E F: Set (EuclideanSpace' d)} (hf: ComplexAbsolutelyIntegrableOn f E) (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) (hsub: F ⊆ E): ComplexAbsolutelyIntegrableOn f F := by sorry

theorem ComplexAbsolutelyIntegrableOn.integ_restrict {d:ℕ} {f: EuclideanSpace' d → ℂ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) (hsub: F ⊆ E) (hf: ComplexAbsolutelyIntegrableOn f E) : (hf.mono hE hF hsub).integ = (hf.restrict hF).integ:= by sorry

/-- Lemma 1.3.19 (Triangle inequality) -/

theorem ComplexAbsolutelyIntegrable.abs_le {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ‖hf.integ‖ ≤ hf.abs.integ := by sorry
