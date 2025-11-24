import Analysis.MeasureTheory.Section_1_2

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/

open BoundedInterval

/-- Exercise 1.2.3(i) (Empty set) -/
theorem Lebesgue_outer_measure.of_empty (d:ℕ) : Lebesgue_outer_measure (∅: Set (EuclideanSpace' d)) = 0 := by
  sorry

/-- Exercise 1.2.3(ii) (Monotonicity) -/
theorem Lebesgue_outer_measure.mono {d: ℕ} {E F : Set (EuclideanSpace' d)} (h : E ⊆ F) :
    Lebesgue_outer_measure E ≤ Lebesgue_outer_measure F := by
  sorry

/-- Exercise 1.2.3(iii) (Countable subadditivity) -/
theorem Lebesgue_outer_measure.union_le {d: ℕ} (E : ℕ → Set (EuclideanSpace' d)) :
    Lebesgue_outer_measure (⋃ i, E i) ≤ ∑' i, Lebesgue_outer_measure (E i) := by
  sorry

/-- Finite subadditivity -/
theorem Lebesgue_outer_measure.finite_union_le {d n:ℕ} (E: Fin n → Set (EuclideanSpace' d)) :
    Lebesgue_outer_measure (⋃ i, E i) ≤ ∑ i, Lebesgue_outer_measure (E i) := by
  sorry

noncomputable def set_dist {X:Type*} [PseudoMetricSpace X] (A B: Set X) : ℝ :=
  sInf ((fun p: X × X ↦ dist p.1 p.2) '' (A ×ˢ B))

-- ========================================================================
-- Start of Helpers about Box Infrastructure, for lemma 1.2.5: Lebesgue_outer_measure.union_of_separated
-- ========================================================================

/-! ### Helper lemmas for sqrt inequalities -/

/-- The square root function is subadditive: √(x + y) ≤ √x + √y for non-negative reals.
    This follows from the fact that (√x + √y)² = x + y + 2√(xy) ≥ x + y. -/
lemma Real.sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    √(x + y) ≤ √x + √y := by
  by_cases hxy : x + y = 0
  · simp [hxy]
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · rw [Real.sqrt_le_left (by positivity)]
    have : x + y ≤ (√x + √y) ^ 2 := by
      calc x + y
          = (√x) ^ 2 + (√y) ^ 2 := by
              rw [Real.sq_sqrt hx, Real.sq_sqrt hy]
        _ ≤ (√x) ^ 2 + (√y) ^ 2 + 2 * √x * √y := by
              apply le_add_of_nonneg_right
              apply mul_nonneg; apply mul_nonneg
              · norm_num
              · exact Real.sqrt_nonneg _
              · exact Real.sqrt_nonneg _
        _ = (√x + √y) ^ 2 := by ring
    exact this

/-- The square root function is subadditive over finite sums: √(∑ᵢ xᵢ) ≤ ∑ᵢ √xᵢ
    for non-negative terms. This is a consequence of the concavity of sqrt. -/
lemma Real.sqrt_sum_le_sum_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    √(∑ i, f i) ≤ ∑ i, √(f i) := by
  -- Proof by induction on the Finset
  let s := (Finset.univ : Finset ι)
  show √(∑ i ∈ s, f i) ≤ ∑ i ∈ s, √(f i)
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      simp [Finset.sum_insert hi]
      calc √(f i + ∑ x ∈ s, f x)
          ≤ √(f i) + √(∑ x ∈ s, f x) := by
              apply Real.sqrt_add_le_add_sqrt (hf i)
              apply Finset.sum_nonneg
              intro j _; exact hf j
        _ ≤ √(f i) + ∑ x ∈ s, √(f x) := by
              apply add_le_add_left
              exact ih

/-! ### Box diameter properties -/

/-- The diameter of a box is the supremum of Euclidean distances between points in the box -/
noncomputable def Box.diameter {d:ℕ} (B: Box d) : ℝ :=
  sSup { r | ∃ x ∈ B.toSet, ∃ y ∈ B.toSet, r = √(∑ i, (x i - y i)^2) }

/-- Diameter is always nonnegative -/
lemma Box.diameter_nonneg {d:ℕ} (B: Box d) : 0 ≤ B.diameter := by
  unfold Box.diameter
  by_cases h : B.toSet.Nonempty
  · obtain ⟨x, hx⟩ := h
    apply le_csSup
    · -- The set is bounded above
      use (∑ i : Fin d, |B.side i|ₗ)
      intro r ⟨y, hy, z, hz, hr⟩
      -- dist y z is bounded by sum of side lengths
      rw [hr]
      -- y, z ∈ B.toSet means ∀ i, y i ∈ B.side i and z i ∈ B.side i
      have hy_coord : ∀ i, y i ∈ (B.side i).toSet := by
        intro i; exact hy i (Set.mem_univ i)
      have hz_coord : ∀ i, z i ∈ (B.side i).toSet := by
        intro i; exact hz i (Set.mem_univ i)
      -- For each coordinate, the difference is bounded by the side length
      have coord_bound : ∀ i, |(y - z) i| ≤ |B.side i|ₗ := by
        intro i
        have hy_i := hy_coord i
        have hz_i := hz_coord i
        -- All interval types have the same bound: |y i - z i| ≤ max (b - a) 0
        -- This is because both y i and z i are in [a,b] (or (a,b) with open endpoints)
        cases h_side : B.side i with
        | Ioo a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
        | Icc a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
        | Ioc a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
        | Ico a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
      -- Now prove that √(∑ (y i - z i)²) ≤ ∑ |B.side i|ₗ
      -- We use: √(∑ xᵢ²) ≤ ∑ √(xᵢ²) = ∑ |xᵢ| (subadditivity of sqrt)
      have sqrt_sum_le : (∑ i, (y i - z i) ^ 2).sqrt ≤ ∑ i, |(y i - z i)| := by
        -- ℓ² ≤ ℓ¹ norm: √(∑ xᵢ²) ≤ ∑ |xᵢ|
        calc (∑ i, (y i - z i) ^ 2).sqrt
            = (∑ i, |(y i - z i)| ^ 2).sqrt := by
                congr 1; congr 1; ext i; rw [sq_abs]
          _ ≤ ∑ i, (|(y i - z i)| ^ 2).sqrt := by
                -- Apply sqrt subadditivity lemma
                apply Real.sqrt_sum_le_sum_sqrt
                intro i; exact sq_nonneg _
          _ = ∑ i, |(y i - z i)| := by
                congr 1; ext i
                rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]
      calc √(∑ i, (y i - z i) ^ 2)
          ≤ ∑ i, |(y i - z i)| := sqrt_sum_le
        _ = ∑ i, |(y - z) i| := by rfl
        _ ≤ ∑ i, |B.side i|ₗ := by
            apply Finset.sum_le_sum
            intro i _
            exact coord_bound i
    · -- 0 is in the set (distance from any point to itself)
      use x, hx, x, hx
      simp
  · -- Empty box has diameter 0
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h]
    simp [sSup]

/-- Empty box has diameter 0 -/
lemma Box.diameter_of_empty {d:ℕ} (B: Box d) (h: B.toSet = ∅) :
    B.diameter = 0 := by
  unfold Box.diameter
  simp [h, sSup]

/-- Any two points in a box have Euclidean distance at most the diameter -/
lemma Box.dist_le_diameter {d:ℕ} (B: Box d) {x y: EuclideanSpace' d}
    (hx: x ∈ B.toSet) (hy: y ∈ B.toSet) :
    √(∑ i, (x i - y i)^2) ≤ B.diameter := by
  unfold Box.diameter
  apply le_csSup
  · -- The set is bounded above
    use (∑ i : Fin d, |B.side i|ₗ)
    intro r ⟨z, hz, w, hw, hr⟩
    -- dist z w is bounded by sum of side lengths
    rw [hr]
    -- z, w ∈ B.toSet means ∀ i, z i ∈ B.side i and w i ∈ B.side i
    have hz_coord : ∀ i, z i ∈ (B.side i).toSet := by
      intro i; exact hz i (Set.mem_univ i)
    have hw_coord : ∀ i, w i ∈ (B.side i).toSet := by
      intro i; exact hw i (Set.mem_univ i)
    -- For each coordinate, the difference is bounded by the side length
    have coord_bound : ∀ i, |(z - w) i| ≤ |B.side i|ₗ := by
      intro i
      have hz_i := hz_coord i
      have hw_i := hw_coord i
      -- All interval types have the same bound: |z i - w i| ≤ max (b - a) 0
      cases h_side : B.side i with
      | Ioo a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
      | Icc a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
      | Ioc a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
      | Ico a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
    -- Now prove that √(∑ (z i - w i)²) ≤ ∑ |B.side i|ₗ
    have sqrt_sum_le : (∑ i, (z i - w i) ^ 2).sqrt ≤ ∑ i, |(z i - w i)| := by
      -- ℓ² ≤ ℓ¹ norm: √(∑ xᵢ²) ≤ ∑ |xᵢ|
      calc (∑ i, (z i - w i) ^ 2).sqrt
          = (∑ i, |(z i - w i)| ^ 2).sqrt := by
              congr 1; congr 1; ext i; rw [sq_abs]
        _ ≤ ∑ i, (|(z i - w i)| ^ 2).sqrt := by
              apply Real.sqrt_sum_le_sum_sqrt
              intro i; exact sq_nonneg _
        _ = ∑ i, |(z i - w i)| := by
              congr 1; ext i
              rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]
    calc √(∑ i, (z i - w i) ^ 2)
        ≤ ∑ i, |(z i - w i)| := sqrt_sum_le
      _ = ∑ i, |(z - w) i| := by rfl
      _ ≤ ∑ i, |B.side i|ₗ := by
          apply Finset.sum_le_sum
          intro i _
          exact coord_bound i
  · -- √(∑ (x i - y i)²) is in the set
    exact ⟨x, hx, y, hy, rfl⟩

/-- Diameter is bounded by √d times the maximum side length -/
lemma Box.diameter_bound_by_sides {d:ℕ} (B: Box d) :
    B.diameter ≤ Real.sqrt d * (⨆ i, |B.side i|ₗ) := by
  unfold Box.diameter
  by_cases h : B.toSet.Nonempty
  · apply csSup_le
    · obtain ⟨x, hx⟩ := h
      exact ⟨√(∑ i, (x i - x i)^2), x, hx, x, hx, rfl⟩
    · intro r ⟨x, hx, y, hy, hr⟩
      -- √(∑ i, (x i - y i)²) ≤ √(d * max²) = √d * max
      rw [hr]
      let max_side := ⨆ i, |B.side i|ₗ
      -- Each coordinate difference is bounded by the maximum side length
      have coord_bound : ∀ i, |(x - y) i| ≤ max_side := by
        intro i
        have hx_i : x i ∈ (B.side i).toSet := hx i (Set.mem_univ i)
        have hy_i : y i ∈ (B.side i).toSet := hy i (Set.mem_univ i)
        -- |x i - y i| ≤ |B.side i|ₗ ≤ max_side
        have bound_by_side : |(x - y) i| ≤ |B.side i|ₗ := by
          cases h_side : B.side i with
          | Ioo a b =>
              simp [BoundedInterval.toSet, h_side] at hx_i hy_i
              simp [BoundedInterval.length]
              left
              rw [abs_sub_le_iff]
              constructor <;> linarith [hx_i.1, hx_i.2, hy_i.1, hy_i.2]
          | Icc a b =>
              simp [BoundedInterval.toSet, h_side] at hx_i hy_i
              simp [BoundedInterval.length]
              left
              rw [abs_sub_le_iff]
              constructor <;> linarith [hx_i.1, hx_i.2, hy_i.1, hy_i.2]
          | Ioc a b =>
              simp [BoundedInterval.toSet, h_side] at hx_i hy_i
              simp [BoundedInterval.length]
              left
              rw [abs_sub_le_iff]
              constructor <;> linarith [hx_i.1, hx_i.2, hy_i.1, hy_i.2]
          | Ico a b =>
              simp [BoundedInterval.toSet, h_side] at hx_i hy_i
              simp [BoundedInterval.length]
              left
              rw [abs_sub_le_iff]
              constructor <;> linarith [hx_i.1, hx_i.2, hy_i.1, hy_i.2]
        calc |(x - y) i|
            ≤ |B.side i|ₗ := bound_by_side
          _ ≤ max_side := by
              show |B.side i|ₗ ≤ ⨆ j, |B.side j|ₗ
              apply le_ciSup _ i
              -- The set is bounded above
              refine ⟨∑ j : Fin d, |B.side j|ₗ, ?_⟩
              intro r ⟨j, hj⟩
              simp only at hj
              rw [← hj]
              -- |B.side j|ₗ ≤ sum of all sides
              have single_le : ∀ j : Fin d, |B.side j|ₗ ≤ ∑ k : Fin d, |B.side k|ₗ := by
                intro j'
                calc |B.side j'|ₗ
                    = ∑ k ∈ ({j'} : Finset (Fin d)), |B.side k|ₗ := by simp
                  _ ≤ ∑ k ∈ Finset.univ, |B.side k|ₗ := by
                      apply Finset.sum_le_sum_of_subset_of_nonneg
                      · intro x _; simp
                      · intro k _ _; simp [BoundedInterval.length]
                  _ = ∑ k : Fin d, |B.side k|ₗ := rfl
              exact single_le j
      -- Now: (x i - y i)² ≤ max_side² for each i
      have sq_bound : ∀ i, (x i - y i)^2 ≤ max_side^2 := by
        intro i
        have := coord_bound i
        calc (x i - y i)^2
            ≤ |(x i - y i)|^2 := by rw [← sq_abs]
          _ = |(x - y) i|^2 := by rfl
          _ ≤ max_side^2 := by
              apply sq_le_sq'
              · linarith [abs_nonneg ((x - y) i)]
              · exact this
      -- Sum: ∑ i, (x i - y i)² ≤ d * max_side²
      have sum_bound : ∑ i, (x i - y i)^2 ≤ d * max_side^2 := by
        calc ∑ i, (x i - y i)^2
            ≤ ∑ i : Fin d, max_side^2 := by
                apply Finset.sum_le_sum
                intro i _
                exact sq_bound i
          _ = Finset.card (Finset.univ : Finset (Fin d)) * max_side^2 := by
                rw [Finset.sum_const, nsmul_eq_mul]
          _ = d * max_side^2 := by
                rw [Finset.card_fin]
      -- Apply sqrt to both sides
      calc √(∑ i, (x i - y i)^2)
          ≤ √(d * max_side^2) := by
              apply Real.sqrt_le_sqrt
              exact sum_bound
        _ = √d * √(max_side^2) := by
              rw [Real.sqrt_mul (Nat.cast_nonneg d)]
        _ = √d * max_side := by
              rw [Real.sqrt_sq (by
                -- max_side ≥ 0
                apply Real.iSup_nonneg
                intro i
                -- BoundedInterval.length is max (b - a) 0, which is always ≥ 0
                simp [BoundedInterval.length])]
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h]
    simp [sSup]
    apply mul_nonneg
    · exact Real.sqrt_nonneg _
    · apply Real.iSup_nonneg
      intro i
      -- BoundedInterval.length is max (b - a) 0, which is always ≥ 0
      simp [BoundedInterval.length]


/-- If a box intersects two sets, any two points (one from each set)
    in the box have distance at most the diameter -/
lemma Box.diameter_ge_dist_of_intersects {d:ℕ} (B: Box d) (E F : Set (EuclideanSpace' d))
    (hE : (B.toSet ∩ E).Nonempty) (hF : (B.toSet ∩ F).Nonempty) :
    set_dist E F ≤ B.diameter := by
  obtain ⟨x, hx_box, hx_E⟩ := hE
  obtain ⟨y, hy_box, hy_F⟩ := hF
  -- set_dist E F ≤ dist x y (by definition of set_dist as infimum)
  have h_dist : set_dist E F ≤ dist x y := by
    unfold set_dist
    apply csInf_le
    · -- Bounded below by 0
      use 0
      intro r ⟨p, hp, hr⟩
      rw [← hr]
      exact dist_nonneg
    · -- The distance from x to y is in the set
      simp only [Set.mem_image]
      use (x, y)
      exact ⟨Set.mem_prod.mpr ⟨hx_E, hy_F⟩, rfl⟩
  -- dist x y ≤ B.diameter (by dist_le_diameter)
  have h_le_diam : √(∑ i, (x i - y i)^2) ≤ B.diameter :=
    Box.dist_le_diameter B hx_box hy_box
  -- Note: For EuclideanSpace' d, dist x y = √(∑ i, (x i - y i)^2)
  have h_eq : dist x y = √(∑ i, (x i - y i)^2) := by
    simp only [EuclideanSpace.dist_eq]
    congr 1
    congr 1
    ext i
    rw [Real.dist_eq, sq_abs]
  -- Combine
  calc set_dist E F
      ≤ dist x y := h_dist
    _ = √(∑ i, (x i - y i)^2) := h_eq
    _ ≤ B.diameter := h_le_diam

/-- If B.diameter < set_dist E F, then B cannot intersect both E and F.
    This is the core geometric fact needed for finite additivity of separated sets. -/
lemma Box.not_intersects_both_of_diameter_lt {d:ℕ} (B: Box d) (E F : Set (EuclideanSpace' d))
    (h : B.diameter < set_dist E F) :
    ¬((B.toSet ∩ E).Nonempty ∧ (B.toSet ∩ F).Nonempty) := by
  intro ⟨hE, hF⟩
  -- If B intersects both, then set_dist E F ≤ B.diameter
  have := Box.diameter_ge_dist_of_intersects B E F hE hF
  -- But we assumed B.diameter < set_dist E F
  linarith

-- ========================================================================
-- End of Box Infrastructure
-- ========================================================================

/-- Lemma 1.2.5 (Finite additivity for separated sets).  Proof has not been formalized yet. -/
theorem Lebesgue_outer_measure.union_of_separated {d:ℕ} {E F : Set (EuclideanSpace' d)} (hsep: set_dist E F > 0) :
    Lebesgue_outer_measure (E ∪ F) = Lebesgue_outer_measure E + Lebesgue_outer_measure F := by
  sorry

example : set_dist (Ico 0 1).toSet (Icc 1 2).toSet = 0 := by sorry

/-- Exercise 1.2.4 -/
theorem dist_of_disj_compact_pos {d:ℕ} (E F: Set (EuclideanSpace' d)) (hE: IsCompact E) (hF: IsCompact F) (hdisj: E ∩ F = ∅) :
    set_dist E F > 0 := by
  sorry

/-- Lemma 1.2.6 (Outer measure of elementary sets).  Proof has not been formalized yet. -/
theorem Lebesgue_outer_measure.elementary {d:ℕ} (E: Set (EuclideanSpace' d)) (hE: IsElementary E) :
    Lebesgue_outer_measure E = hE.measure := by
  sorry

/-- Cantor's theorem -/
theorem EuclideanSpace'.uncountable (d:ℕ) : Uncountable (EuclideanSpace' d) := by sorry

/-- No uncountable subadditivity-/
example {d:ℕ} : ∃ (S:Type) (E: S → Set (EuclideanSpace' d)), ¬ Lebesgue_outer_measure (⋃ i, E i) ≤ ∑' i, Lebesgue_outer_measure (E i) := by sorry

/-- Remark 1.2.8 -/
example : ∃ (E: Set (EuclideanSpace' 1)), Bornology.IsBounded E ∧
    IsOpen E ∧ ¬ JordanMeasurable E := by sorry

/-- Remark 1.2.8 -/
example : ∃ (E: Set (EuclideanSpace' 1)), Bornology.IsBounded E ∧
    IsCompact E ∧ ¬ JordanMeasurable E := by sorry

def AlmostDisjoint {d:ℕ} (B B': Box d) : Prop := interior B.toSet ∩ interior B'.toSet = ∅

theorem IsElementary.almost_disjoint {d k:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) (B: Fin k → Box d) (hEB: E = ⋃ i, (B i).toSet) (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) : hE.measure = ∑ i, |B i|ᵥ := by
  sorry

/-- Lemma 1.2.9 (Outer measure of countable unions of almost disjoint boxes).  Proof has not been formalized yet. -/
theorem Lebesgue_outer_measure.union_of_almost_disjoint {d:ℕ} {B : ℕ → Box d} (h : Pairwise (Function.onFun AlmostDisjoint B)) :
    Lebesgue_outer_measure (⋃ i, (B i).toSet) = ∑' i, Lebesgue_outer_measure (B i).toSet := by
  sorry

theorem Lebesgue_outer_measure.univ {d:ℕ} : Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) = ⊤ := by
  sorry

/-- Remark 1.2.10 -/
theorem Box.sum_volume_eq {d:ℕ} (B B': ℕ → Box d) (hdisj: Pairwise (Function.onFun AlmostDisjoint B)) (hdisj': Pairwise (Function.onFun AlmostDisjoint B)) (hcover: (⋃ n, (B n).toSet) = (⋃ n, (B' n).toSet)) :
    ∑' n, (B n).volume = ∑' n, (B' n).volume := by
  sorry

/-- Exercise 1.2.5 -/
example {d:ℕ} (E: Set (EuclideanSpace' d)) (B: ℕ → Box d) (hE: E = ⋃ n, (B n).toSet) (hdisj: Pairwise (Function.onFun AlmostDisjoint B)) : Lebesgue_outer_measure E = Jordan_inner_measure E := by
  sorry

def IsCube {d:ℕ} (B: Box d) : Prop := ∃ r, ∀ i, |B.side i|ₗ = r

noncomputable def DyadicCube {d:ℕ} (n:ℤ) (a: Fin d → ℤ) : Box d := { side := fun i ↦ Icc (a i/2^n) ((a i + 1)/2^n) }

lemma DyadicCube.isCube {d:ℕ} (n:ℤ) (a: Fin d → ℤ) : IsCube (DyadicCube n a) := by
  sorry

def Box.IsDyadicAtScale {d:ℕ} (B: Box d) (n:ℤ) : Prop := ∃ a: Fin d → ℤ, B = DyadicCube n a

def Box.IsDyadic {d:ℕ} (B: Box d) : Prop := ∃ n:ℕ, B.IsDyadicAtScale n

/-- Lemma 1.2.11.  Proof has not been formalized yet. -/
theorem IsOpen.eq_union_boxes {d:ℕ} (E: Set (EuclideanSpace' d)) (hE: IsOpen E) : ∃ B: ℕ → Box d, (E = ⋃ n, (B n).toSet) ∧ (∀ n, (B n).IsDyadic) ∧ Pairwise (Function.onFun AlmostDisjoint B) := by
  sorry

theorem Lebesgue_outer_measure.of_open {d:ℕ} (E: Set (EuclideanSpace' d)) (hE: IsOpen E) : Lebesgue_outer_measure E = Jordan_inner_measure E := by
  sorry

/-- Lemma 1.2.12 (Outer regularity).  Proof has not been formalized yet. -/
theorem Lebesgue_outer_measure.eq {d:ℕ} (E: Set (EuclideanSpace' d)) : Lebesgue_outer_measure E = sInf { M | ∃ U, E ⊆ U ∧ IsOpen U ∧ M = Lebesgue_outer_measure U} := by
  sorry

/-- Exercise 1.2.6 -/
example : ∃ (d:ℕ) (E: Set (EuclideanSpace' d)), Lebesgue_outer_measure E ≠ sSup { M | ∃ U, U ⊆ E ∧ IsOpen U ∧ M = Lebesgue_outer_measure U} := by sorry
