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
- (x) ⟹ (vii): {f < λ} = f⁻¹'(Iio λ) and Iio λ is open
- (v)-(xi) ⟹ (iv): construction of approximating sequence

**Derived transitively (by tfae_finish):**
- (ix) ⟹ (v) or (vi): via (ix) → (x) → (vii) → (vi) → (v)
- (x) ⟹ (v)-(ix): via (x) → (vii) → (vi) → (v) → (viii)/(ix)
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
  exact tendsto_atTop_iSup (hg_mono x)

/-! ### (iii) ⟹ (v): Via limsup representation -/

-- This is the main technical work of the proof
private lemma iii_imp_v : stmt_iii f → stmt_v f := by
  intro ⟨g, hg_simple, hg_ae_conv⟩
  intro t
  -- The key insight: f(x) = lim f_n(x) = lim sup f_n(x) a.e.
  -- So {f > λ} = ⋃_{M≥1} ⋂_{N≥1} ⋃_{n≥N} {f_n > λ + 1/M} outside a null set
  sorry

/-! ### (v) ⟹ (vi): {f ≥ λ} = ⋂_{n≥1} {f > λ - 1/n} -/

-- Helper: if x > n for all n ∈ ℕ, then x = ⊤
private lemma EReal.eq_top_of_forall_nat_lt {x : EReal} (h : ∀ n : ℕ, x > n) : x = ⊤ := by
  induction x using EReal.rec with
  | bot =>
    exfalso
    have h0 : (⊥ : EReal) > (0 : ℕ) := h 0
    simp only [Nat.cast_zero, gt_iff_lt, not_lt_bot] at h0
  | top => rfl
  | coe r =>
    exfalso
    have h1 : (r : EReal) > (⌈r⌉₊ : ℕ) := h ⌈r⌉₊
    have h1' : r > (⌈r⌉₊ : ℕ) := by
      simp only [gt_iff_lt] at h1 ⊢
      rwa [show ((⌈r⌉₊ : ℕ) : EReal) = ((⌈r⌉₊ : ℕ) : ℝ) by norm_cast,
           EReal.coe_lt_coe_iff] at h1
    have h2 : r ≤ ⌈r⌉₊ := Nat.le_ceil r
    linarith

private lemma v_imp_vi : stmt_v f → stmt_vi f := by
  intro hv t
  -- Handle cases based on t
  rcases eq_bot_or_bot_lt t with rfl | ht_bot
  · -- t = ⊥: {f ≥ ⊥} = Set.univ
    convert MeasurableSet.univ
    ext x; simp
  rcases eq_top_or_lt_top t with rfl | ht_top
  · -- t = ⊤: {f ≥ ⊤} = {f = ⊤} = ⋂_{n ∈ ℕ} {f > n}
    have h_eq : {x | f x ≥ ⊤} = ⋂ (n : ℕ), {x | f x > n} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, ge_iff_le, top_le_iff]
      constructor
      · intro hfx n
        simp only [gt_iff_lt]
        rw [hfx]; exact EReal.coe_lt_top n
      · intro hfx
        exact EReal.eq_top_of_forall_nat_lt hfx
    rw [h_eq]
    exact MeasurableSet.iInter (fun n => hv _)
  · -- t is finite: use {f ≥ t} = ⋂_{n≥1} {f > t - 1/(n+1)}
    -- Since t < ⊤ and ⊥ < t, we know t is a real number
    induction t using EReal.rec with
    | bot => exact (not_lt.mpr le_rfl ht_bot).elim
    | top => exact (not_lt.mpr le_rfl ht_top).elim
    | coe t' =>
      -- Use {f ≥ t'} = ⋂_n {f > (t' - 1/(n+1) : ℝ)}
      have h_eq : {x | f x ≥ (t' : EReal)} = ⋂ (n : ℕ), {x | f x > ((t' - 1 / (n + 1)) : ℝ)} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iInter, ge_iff_le, gt_iff_lt]
        constructor
        · intro hfx n
          have h1 : (0 : ℝ) < 1 / (n + 1) := by positivity
          have h2 : (t' - 1 / (n + 1) : ℝ) < t' := by linarith
          have h3 : ((t' - 1 / (n + 1)) : EReal) < (t' : EReal) := EReal.coe_lt_coe_iff.mpr h2
          exact lt_of_lt_of_le h3 hfx
        · intro hfx
          by_contra h
          push_neg at h
          -- f x < t'
          have hfx_lt_t' : f x < (t' : EReal) := h
          -- Get a witness for f x being a real
          have hfx_ne_bot : f x ≠ ⊥ := by
            intro hfx_eq_bot
            have hbot : ((t' - 1 / ((0 : ℕ) + 1)) : ℝ) < (⊥ : EReal) := by
              simp only [Nat.cast_zero, zero_add, div_one]
              rw [← hfx_eq_bot]
              convert hfx 0 using 2
              simp
            exact not_lt_bot hbot
          have hfx_ne_top : f x ≠ ⊤ := ne_top_of_lt hfx_lt_t'
          -- So f x is a real
          have hr : f x = (f x).toReal := (EReal.coe_toReal hfx_ne_top hfx_ne_bot).symm
          set r := (f x).toReal with hr_def
          rw [hr] at hfx_lt_t' hfx
          have hr_lt_t' : r < t' := EReal.coe_lt_coe_iff.mp hfx_lt_t'
          have hdiff_pos : 0 < t' - r := by linarith
          obtain ⟨n, hn⟩ := exists_nat_gt (1 / (t' - r))
          have h_n_pos : (0 : ℝ) < n := by
            by_cases hn0 : n = 0
            · subst hn0; simp at hn; linarith
            · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
          have hn' : 1 / ((n : ℝ) + 1) < t' - r := by
            calc 1 / ((n : ℝ) + 1) < 1 / (n : ℝ) := by
                  apply one_div_lt_one_div_of_lt h_n_pos; linarith
              _ < 1 / (1 / (t' - r)) := by
                  apply one_div_lt_one_div_of_lt (one_div_pos.mpr hdiff_pos) hn
              _ = t' - r := one_div_one_div (t' - r)
          -- So (t' - 1/(n+1) : ℝ) > r
          have hcontra := hfx n
          have hcontra' := EReal.coe_lt_coe_iff.mp hcontra
          linarith
      rw [h_eq]
      exact MeasurableSet.iInter (fun n => hv _)

/-! ### (vi) ⟹ (v): {f > λ} = ⋃_{q ∈ ℚ, q > λ} {f ≥ q} -/

private lemma vi_imp_v : stmt_vi f → stmt_v f := by
  intro hvi t
  -- {f > t} = ⋃_{q : ℚ, q > t} {f ≥ q}
  -- Since rationals are dense, for any x with f x > t, there exists q ∈ ℚ with t < q ≤ f x
  have h_eq : {x | f x > t} = ⋃ (q : ℚ), if (t < ((q : ℝ) : EReal)) then {x | f x ≥ ((q : ℝ) : EReal)} else ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hfx
      -- f x > t, so there exists q ∈ ℚ with t < q < f x
      obtain ⟨q, hq1, hq2⟩ := EReal.exists_rat_btwn_of_lt hfx
      use q
      simp only [hq1, if_true]
      exact le_of_lt hq2
    · intro ⟨q, hq⟩
      by_cases h : t < ((q : ℝ) : EReal)
      · simp only [h, if_true, Set.mem_setOf_eq] at hq
        calc t < ((q : ℝ) : EReal) := h
          _ ≤ f x := hq
      · simp only [h, if_false, Set.mem_empty_iff_false] at hq
  rw [h_eq]
  -- This is a countable union of measurable sets
  apply MeasurableSet.iUnion
  intro q
  split_ifs with h
  · exact hvi ((q : ℝ) : EReal)
  · exact MeasurableSet.empty

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
    have h_eq : f⁻¹' (Real.toEReal '' Set.Ioo a b) = {x | f x > a} ∩ {x | f x < b} := by
      rw [EReal.image_coe_Ioo]
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_inter_iff, Set.mem_setOf_eq, gt_iff_lt]
    rw [h_eq]
    exact MeasurableSet.inter (hv _) (hvii _)
  | Icc a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Icc a b) = {x | f x ≥ a} ∩ {x | f x ≤ b} := by
      rw [EReal.image_coe_Icc]
      ext x
      simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_inter_iff, Set.mem_setOf_eq, ge_iff_le]
    rw [h_eq]
    exact MeasurableSet.inter (hvi _) (hviii _)
  | Ioc a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Ioc a b) = {x | f x > a} ∩ {x | f x ≤ b} := by
      rw [EReal.image_coe_Ioc]
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_inter_iff, Set.mem_setOf_eq, gt_iff_lt]
    rw [h_eq]
    exact MeasurableSet.inter (hv _) (hviii _)
  | Ico a b =>
    simp only [BoundedInterval.toSet]
    have h_eq : f⁻¹' (Real.toEReal '' Set.Ico a b) = {x | f x ≥ a} ∩ {x | f x < b} := by
      rw [EReal.image_coe_Ico]
      ext x
      simp only [Set.mem_preimage, Set.mem_Ico, Set.mem_inter_iff, Set.mem_setOf_eq, ge_iff_le]
    rw [h_eq]
    exact MeasurableSet.inter (hvi _) (hvii _)

/-! ### (ix) ⟹ (x): Open sets are countable unions of intervals -/

-- For unsigned f, f⁻¹'({⊥}) = ∅
private lemma unsigned_preimage_bot_empty (hf : Unsigned f) : f⁻¹' {⊥} = ∅ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  intro hfx
  have h := hf x
  rw [hfx] at h
  simp only [ge_iff_le] at h
  exact not_le.mpr EReal.bot_lt_zero h

-- The embedded reals ℝ as a subset of EReal
private lemma ereal_reals_eq_iUnion :
    (Set.range Real.toEReal : Set EReal) = ⋃ (n : ℕ), Real.toEReal '' Set.Ioo (-(n:ℝ) - 1) (n + 1) := by
  ext x
  simp only [Set.mem_range, Set.mem_iUnion, Set.mem_image, Set.mem_Ioo]
  constructor
  · intro ⟨r, hr⟩
    use ⌈|r|⌉₊, r
    constructor
    · constructor
      · have h1 : -|r| ≤ r := neg_abs_le r
        have h2 : |r| ≤ ⌈|r|⌉₊ := Nat.le_ceil |r|
        linarith
      · have h1 : r ≤ |r| := le_abs_self r
        have h2 : |r| ≤ ⌈|r|⌉₊ := Nat.le_ceil |r|
        linarith
    · exact hr
  · intro ⟨_, r, _, hr⟩
    exact ⟨r, hr⟩

-- ℝ embedded in EReal has measurable preimage
private lemma measurable_preimage_reals (hix : stmt_ix f) : MeasurableSet (f⁻¹' (Set.range Real.toEReal)) := by
  rw [ereal_reals_eq_iUnion, Set.preimage_iUnion]
  apply MeasurableSet.iUnion
  intro n
  exact hix (BoundedInterval.Ioo (-(n:ℝ) - 1) (n + 1))

-- {⊤} as complement of ℝ ∪ {⊥}
private lemma ereal_top_singleton_eq : ({⊤} : Set EReal) = (Set.range Real.toEReal ∪ {⊥})ᶜ := by
  ext x
  simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_union, Set.mem_range]
  constructor
  · intro hx
    rw [hx]
    push_neg
    constructor
    · intro r hr
      exact EReal.coe_ne_top r hr
    · intro h; exact absurd h.symm (ne_of_lt bot_lt_top)
  · intro hx
    push_neg at hx
    induction x using EReal.rec with
    | bot => exact (hx.2 rfl).elim
    | top => rfl
    | coe r => exact (hx.1 r rfl).elim

-- For unsigned f, f⁻¹'({⊤}) is measurable
private lemma measurable_preimage_top (hf : Unsigned f) (hix : stmt_ix f) : MeasurableSet (f⁻¹' {⊤}) := by
  rw [ereal_top_singleton_eq, Set.preimage_compl]
  apply MeasurableSet.compl
  rw [Set.preimage_union]
  apply MeasurableSet.union
  · exact measurable_preimage_reals hix
  · rw [unsigned_preimage_bot_empty hf]
    exact MeasurableSet.empty

-- The intersection of an open set with ℝ can be expressed using countable intervals
private lemma open_inter_reals_eq_countable_union (U : Set EReal) (hU : IsOpen U) :
    ∃ S : Set (Set ℝ), S.Countable ∧ (∀ I ∈ S, ∃ a b, I = Set.Ioo a b) ∧
    U ∩ Set.range Real.toEReal = ⋃ I ∈ S, Real.toEReal '' I := by
  let V : Set ℝ := Real.toEReal ⁻¹' U
  have hV_open : IsOpen V := hU.preimage continuous_coe_real_ereal
  let RatIntervals := {I : Set ℝ | ∃ (a b : ℚ), I = Set.Ioo (a : ℝ) b ∧ I ⊆ V}
  have hRI_count : RatIntervals.Countable := by
    have h : RatIntervals ⊆ Set.range (fun p : ℚ × ℚ => Set.Ioo (p.1 : ℝ) p.2) := by
      intro I hI
      obtain ⟨a, b, hab, _⟩ := hI
      exact ⟨(a, b), hab.symm⟩
    exact Set.Countable.mono h (Set.countable_range _)
  have hRI_intervals : ∀ I ∈ RatIntervals, ∃ a b, I = Set.Ioo a b := by
    intro I hI
    obtain ⟨a, b, hab, _⟩ := hI
    exact ⟨a, b, hab⟩
  have hRI_union : V = ⋃ I ∈ RatIntervals, I := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open x hx
      obtain ⟨a, ha_lo, ha_hi⟩ := exists_rat_btwn (by linarith : x - ε / 2 < x)
      obtain ⟨b, hb_lo, hb_hi⟩ := exists_rat_btwn (by linarith : x < x + ε / 2)
      refine ⟨Set.Ioo a b, ?_, ?_⟩
      · refine ⟨a, b, rfl, ?_⟩
        intro y hy
        apply hε_ball
        rw [Metric.mem_ball, Real.dist_eq]
        simp only [Set.mem_Ioo] at hy
        have h1 : y - x < ε / 2 := by linarith [hy.2]
        have h2 : x - y < ε / 2 := by linarith [hy.1]
        rw [abs_lt]
        constructor <;> linarith
      · simp only [Set.mem_Ioo]
        exact ⟨ha_hi, hb_lo⟩
    · intro ⟨I, hI, hxI⟩
      obtain ⟨_, _, _, hI_sub⟩ := hI
      exact hI_sub hxI
  use RatIntervals
  refine ⟨hRI_count, hRI_intervals, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_iUnion, Set.mem_image]
  constructor
  · intro ⟨hy_U, r, hr⟩
    have hr_V : r ∈ V := by
      show Real.toEReal r ∈ U
      rw [hr]; exact hy_U
    rw [hRI_union] at hr_V
    simp only [Set.mem_iUnion] at hr_V
    obtain ⟨I, hI_mem, hr_I⟩ := hr_V
    exact ⟨I, hI_mem, r, hr_I, hr⟩
  · intro ⟨I, hI_mem, r, hr_I, hr⟩
    constructor
    · obtain ⟨_, _, _, hI_sub⟩ := hI_mem
      have : r ∈ V := hI_sub hr_I
      rw [← hr]
      exact this
    · exact ⟨r, hr⟩

private lemma ix_imp_x (hf : Unsigned f) : stmt_ix f → stmt_x f := by
  intro hix U hU
  -- Decompose U = (U ∩ ℝ) ∪ (U ∩ {⊤}) ∪ (U ∩ {⊥})
  have hU_decomp : U = (U ∩ Set.range Real.toEReal) ∪ (U ∩ {⊤}) ∪ (U ∩ {⊥}) := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · intro hx
      induction x using EReal.rec with
      | bot => right; exact ⟨hx, rfl⟩
      | top => left; right; exact ⟨hx, rfl⟩
      | coe r => left; left; exact ⟨hx, r, rfl⟩
    · intro hx
      rcases hx with (⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩ <;> exact hx
  rw [hU_decomp, Set.preimage_union, Set.preimage_union]
  apply MeasurableSet.union
  apply MeasurableSet.union
  -- Part 1: f⁻¹'(U ∩ ℝ) is measurable
  · obtain ⟨S, hS_count, hS_intervals, hS_eq⟩ := open_inter_reals_eq_countable_union U hU
    rw [hS_eq, Set.preimage_iUnion₂]
    apply MeasurableSet.biUnion hS_count
    intro I hI
    obtain ⟨a, b, hab⟩ := hS_intervals I hI
    rw [hab]
    exact hix (BoundedInterval.Ioo a b)
  -- Part 2: f⁻¹'(U ∩ {⊤}) is measurable
  · by_cases htop : ⊤ ∈ U
    · have h_eq : U ∩ {⊤} = {⊤} := Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr htop)
      rw [h_eq]
      exact measurable_preimage_top hf hix
    · have h_eq : U ∩ {⊤} = ∅ := Set.inter_singleton_eq_empty.mpr htop
      rw [h_eq, Set.preimage_empty]
      exact MeasurableSet.empty
  -- Part 3: f⁻¹'(U ∩ {⊥}) is measurable (empty for unsigned f)
  · rw [Set.preimage_inter, unsigned_preimage_bot_empty hf, Set.inter_empty]
    exact MeasurableSet.empty

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

/-! ### (x) ⟹ (vii): {f < λ} = f⁻¹'(Iio λ) and Iio λ is open -/

private lemma x_imp_vii : stmt_x f → stmt_vii f := by
  intro hx t
  have h_open : IsOpen (Set.Iio t) := isOpen_Iio
  have h_eq : {x | f x < t} = f⁻¹' (Set.Iio t) := rfl
  rw [h_eq]
  exact hx _ h_open

/-! ### (v)-(xi) ⟹ (iv): Construction of approximating sequence -/

-- Helper: the closed ball is Lebesgue measurable
private lemma closedBall_LebesgueMeasurable (c : EuclideanSpace' d) (r : ℝ) :
    LebesgueMeasurable (Metric.closedBall c r) :=
  Metric.isClosed_closedBall.measurable

-- Helper: the norm ball centered at origin is Lebesgue measurable
private lemma normBall_LebesgueMeasurable (r : ℝ) :
    LebesgueMeasurable {x : EuclideanSpace' d | ‖x‖ ≤ r} := by
  have h : {x : EuclideanSpace' d | ‖x‖ ≤ r} = Metric.closedBall 0 r := by
    ext x; simp [Metric.closedBall, dist_zero_right]
  rw [h]
  exact closedBall_LebesgueMeasurable 0 r

-- Helper: truncation function min(f(x), n)
private noncomputable def truncate_at (f : EuclideanSpace' d → EReal) (n : ℕ) (x : EuclideanSpace' d) : EReal :=
  min (f x) n

-- Helper: discretization to multiples of 2^{-n}, capped at n
private noncomputable def discretize (t : EReal) (n : ℕ) : EReal :=
  if t = ⊤ then (n : EReal)
  else if t = ⊥ then 0
  else
    let r := t.toReal
    if r < 0 then 0
    else min ((⌊r * 2^n⌋₊ : ℕ) / (2^n : ℝ) : EReal) n

-- Helper: the approximating sequence
private noncomputable def approx_seq (f : EuclideanSpace' d → EReal) (n : ℕ) (x : EuclideanSpace' d) : EReal :=
  if ‖x‖ ≤ n then discretize (truncate_at f n x) n else 0

-- The main construction lemma
private lemma v_to_xi_imp_iv (hf : Unsigned f) (hv : stmt_v f) (hvi : stmt_vi f)
    (hvii : stmt_vii f) (hviii : stmt_viii f) (hix : stmt_ix f)
    (hx : stmt_x f) (hxi : stmt_xi f) :
    stmt_iv f := by
  -- Construct f_n(x) = largest k·2^{-n} ≤ min(f(x), n) when |x| ≤ n, else 0
  use approx_seq f
  constructor
  · -- Each approx_seq f n is a simple function, bounded, with finite measure support
    intro n
    constructor
    · -- UnsignedSimpleFunction (approx_seq f n)
      -- approx_seq takes values in {0, 1/2^n, 2/2^n, ..., n}
      -- Level sets are intersections of {f ≥ k/2^n}, {f < (k+1)/2^n}, {‖x‖ ≤ n}
      -- These are measurable by assumptions hv, hvii, hviii
      sorry
    constructor
    · -- EReal.BoundedFunction (approx_seq f n)
      -- approx_seq f n is in [0, n], so its abs is ≤ n
      use n
      intro x
      -- The value of approx_seq f n x is either 0, or k/2^n for some k ≤ n·2^n
      -- In all cases, 0 ≤ value ≤ n, so abs ≤ n
      sorry
    · -- FiniteMeasureSupport (approx_seq f n)
      -- Support is contained in {‖x‖ ≤ n}, which has finite measure
      sorry
  constructor
  · -- Monotonicity: approx_seq f is monotone in n for each x
    intro x m n hmn
    simp only [approx_seq, discretize, truncate_at]
    sorry -- Need to show approx_seq f m x ≤ approx_seq f n x
  · -- Convergence: f x = iSup (approx_seq f · x)
    intro x
    -- For each x, eventually ‖x‖ ≤ n, so approx_seq f n x approximates f x to within 2^{-n}
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
  tfae_have 9 → 10 := ix_imp_x hf
  tfae_have 10 ↔ 11 := x_iff_xi
  tfae_have 10 → 7 := x_imp_vii
  tfae_have 5 → 4 := fun hv => v_to_xi_imp_iv hf hv (v_imp_vi hv) (vi_imp_vii (v_imp_vi hv))
    (v_imp_viii hv) (v_to_viii_imp_ix hv (v_imp_vi hv) (vi_imp_vii (v_imp_vi hv)) (v_imp_viii hv))
    (ix_imp_x hf (v_to_viii_imp_ix hv (v_imp_vi hv) (vi_imp_vii (v_imp_vi hv)) (v_imp_viii hv)))
    (x_iff_xi.mp (ix_imp_x hf (v_to_viii_imp_ix hv (v_imp_vi hv) (vi_imp_vii (v_imp_vi hv)) (v_imp_viii hv))))
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
