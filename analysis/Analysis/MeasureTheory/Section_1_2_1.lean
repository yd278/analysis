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
    sorry
  · -- √(∑ (x i - y i)²) is in the set
    exact ⟨x, hx, y, hy, rfl⟩

/-- Diameter is bounded by √d times the maximum side length -/
lemma Box.diameter_bound_by_sides {d:ℕ} (B: Box d) (hd: 0 < d) :
    B.diameter ≤ Real.sqrt d * (⨆ i, |B.side i|ₗ) := by
  unfold Box.diameter
  by_cases h : B.toSet.Nonempty
  · apply csSup_le
    · obtain ⟨x, hx⟩ := h
      exact ⟨√(∑ i, (x i - x i)^2), x, hx, x, hx, rfl⟩
    · intro r ⟨x, hx, y, hy, hr⟩
      -- √(∑ i, (x i - y i)²) ≤ √(d * max²) = √d * max
      sorry
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h]
    simp [sSup]
    sorry

/-- Subdivide a box into 2^d equal sub-boxes by bisecting each side.
    This function enumerates the 2^d sub-boxes by treating each natural number < 2^d
    as a d-bit binary string, where bit i indicates which half (low/high) to take for dimension i. -/
noncomputable def Box.subdivide {d:ℕ} (B: Box d) : Finset (Box d) :=
  open Classical in
  -- Generate all 2^d combinations of (low half, high half) for each dimension
  Finset.image (fun (bits : Fin (2^d)) =>
    { side := fun i =>
        let mid := (B.side i).a + ((B.side i).b - (B.side i).a) / 2
        -- Extract bit i from bits.val to decide low/high half
        if (bits.val / 2^i.val) % 2 = 0
        then match B.side i with
          | Ioo a _ => Ioo a mid
          | Icc a _ => Icc a mid
          | Ioc a _ => Ioc a mid
          | Ico a _ => Ico a mid
        else match B.side i with
          | Ioo _ b => Ioo mid b
          | Icc _ b => Icc mid b
          | Ioc _ b => Ioc mid b
          | Ico _ b => Ico mid b
    : Box d })
  Finset.univ

/-- Subdivision covers the original box -/
lemma Box.subdivide_covers {d:ℕ} (B: Box d) :
    B.toSet = ⋃ B' ∈ B.subdivide, B'.toSet := by
  sorry

/-- Sub-boxes have disjoint interiors -/
lemma Box.subdivide_almost_disjoint {d:ℕ} (B: Box d) :
    ∀ B₁ ∈ B.subdivide, ∀ B₂ ∈ B.subdivide, B₁ ≠ B₂ →
      (interior B₁.toSet) ∩ (interior B₂.toSet) = ∅ := by
  sorry

/-- Volume is preserved under subdivision: sum of sub-box volumes equals original volume -/
lemma Box.volume_subdivide {d:ℕ} (B: Box d) :
    ∑ B' ∈ B.subdivide, |B'|ᵥ = |B|ᵥ := by
  unfold Box.subdivide Box.volume
  -- Each dimension is halved, giving volume_sub = volume / 2^d for each sub-box
  -- We have 2^d sub-boxes, so total = 2^d * (volume / 2^d) = volume
  sorry

/-- Diameter of sub-boxes is at most half the diameter of the original box -/
lemma Box.subdivide_diameter_bound {d:ℕ} (B: Box d) (B': Box d)
    (hB': B' ∈ B.subdivide) :
    B'.diameter ≤ B.diameter / 2 := by
  -- Each side is halved, so maximum distance is approximately halved
  sorry

/-- Subdivide repeatedly until all boxes have diameter at most δ.
    Uses well-founded recursion on the number of subdivisions needed. -/
noncomputable def Box.subdivide_to_diameter {d:ℕ} (B: Box d) (δ: ℝ) (hδ: 0 < δ) :
    Finset (Box d) :=
  if h : B.diameter ≤ δ then
    {B}  -- Already small enough
  else
    -- Subdivide and recursively subdivide each piece
    -- Note: This requires a termination proof showing diameter decreases
    have : B.diameter / 2 < B.diameter := by
      apply div_two_lt_of_pos
      by_contra h_neg
      push_neg at h_neg
      have : B.diameter ≤ 0 := h_neg
      have : 0 ≤ B.diameter := Box.diameter_nonneg B
      have : B.diameter = 0 := le_antisymm ‹B.diameter ≤ 0› ‹0 ≤ B.diameter›
      exact h (this.symm ▸ (le_of_lt hδ))
    sorry  -- Recursive subdivision needs well-founded recursion setup

/-- All boxes in subdivide_to_diameter have diameter at most δ -/
lemma Box.subdivide_to_diameter_diameter_bound {d:ℕ} (B: Box d)
    (δ: ℝ) (hδ: 0 < δ) (B': Box d)
    (hB': B' ∈ B.subdivide_to_diameter δ hδ) :
    B'.diameter ≤ δ := by
  sorry

/-- subdivide_to_diameter covers the original box -/
lemma Box.subdivide_to_diameter_covers {d:ℕ} (B: Box d)
    (δ: ℝ) (hδ: 0 < δ) :
    B.toSet = ⋃ B' ∈ B.subdivide_to_diameter δ hδ, B'.toSet := by
  sorry

/-- Volume is preserved under repeated subdivision -/
lemma Box.volume_subdivide_to_diameter {d:ℕ} (B: Box d)
    (δ: ℝ) (hδ: 0 < δ) :
    ∑ B' ∈ B.subdivide_to_diameter δ hδ, |B'|ᵥ = |B|ᵥ := by
  sorry

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
