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
  -- Extend E to ℕ → Set by using empty set for indices ≥ n, then use countable subadditivity
  let E' : ℕ → Set (EuclideanSpace' d) := fun k =>
    if h : k < n then E ⟨k, h⟩ else ∅
  -- The union over Fin n equals the union over all k with E' k
  have h_union : (⋃ i, E i) = (⋃ k, E' k) := by
    ext x
    simp [E']
    constructor
    · intro ⟨i, hi⟩
      use i.val
      simp [hi]
    · intro ⟨k, hx⟩
      by_cases hk : k < n
      · use ⟨k, hk⟩
        simpa [dif_pos hk] using hx
      · simp [dif_neg hk] at hx
  rw [h_union]
  -- Apply countable subadditivity
  calc Lebesgue_outer_measure (⋃ k, E' k)
      ≤ ∑' k, Lebesgue_outer_measure (E' k) := union_le E'
    _ = ∑ i : Fin n, Lebesgue_outer_measure (E i) := by
        -- The sum over ℕ equals the sum over Fin n because E' k = ∅ for k ≥ n
        -- First, establish that E' k = ∅ for k ≥ n, so its outer measure is 0
        have h_empty : ∀ k ≥ n, E' k = ∅ := fun k hk => dif_neg (not_lt.mpr hk)
        have h_measure_empty : ∀ k ≥ n, Lebesgue_outer_measure (E' k) = 0 := by
          intro k hk
          rw [h_empty k hk, of_empty]

        -- Convert the tsum to a sum over Fin n
        -- The key lemma we need is: tsum equals finite sum when function has finite support
        -- In our case, E' k is non-empty only for k < n

        -- Define an explicit bijection and use it
        have : ∑' k, Lebesgue_outer_measure (E' k) = ∑ i : Fin n, Lebesgue_outer_measure (E' i.val) := by
          -- Use tsum_eq_sum with finite support
          let s : Finset ℕ := Finset.range n
          have h_support : ∀ k ∉ s, Lebesgue_outer_measure (E' k) = 0 := by
            intro k hk
            have : ¬ k < n := by simpa [s, Finset.mem_range] using hk
            exact h_measure_empty k (le_of_not_gt this)
          rw [tsum_eq_sum h_support]
          -- Now show the sums are equal by reindexing
          refine Finset.sum_bij (fun (k : ℕ) (hk : k ∈ s) => ⟨k, ?_⟩) ?_ ?_ ?_ ?_
          · simpa [s, Finset.mem_range] using hk
          · intros; simp
          · intros k₁ k₂ hk₁ hk₂ heq; simp at heq; exact heq
          · intro i _
            use i.val
            refine ⟨?_, ?_⟩
            · simp [s, Finset.mem_range, i.isLt]
            · simp
          · intro i _; simp

        rw [this]
        congr 1
        ext i
        simp [E', dif_pos i.isLt]


noncomputable def set_dist {X:Type*} [PseudoMetricSpace X] (A B: Set X) : ℝ :=
  sInf ((fun p: X × X ↦ dist p.1 p.2) '' (A ×ˢ B))

-- ========================================================================
-- Start of Helpers for lemma 1.2.5: Lebesgue_outer_measure.union_of_separated
-- ========================================================================
/-- max distributes over division by 2 -/
lemma max_div_two (x : ℝ) : max x 0 / 2 = max (x / 2) 0 := by
  by_cases hx : 0 ≤ x
  · simp [max_eq_left hx, max_eq_left (div_nonneg hx (by norm_num : (0:ℝ) < 2).le)]
  · push_neg at hx
    simp [max_eq_right (le_of_lt hx), max_eq_right (by linarith : x / 2 ≤ 0)]

/-- For EReal, adding a positive real value to a value that is neither ⊥ nor ⊤ gives a strictly greater result. -/
lemma EReal.lt_add_of_pos_coe {x : EReal} {ε : ℝ} (hε : 0 < ε) (h_ne_bot : x ≠ ⊥) (h_ne_top : x ≠ ⊤) :
    x < x + ↑ε := by
  have h_eps : (0 : EReal) < (ε : EReal) := EReal.coe_pos.mpr hε
  have : 0 + x < ↑ε + x := EReal.add_lt_add_of_lt_of_le h_eps (le_refl x) h_ne_bot h_ne_top
  simpa [add_comm] using this

/-- EReal epsilon argument: if for all positive ε, a ≤ b + ε, then a ≤ b.
    This holds when b ≠ ⊤ (if b = ⊤, the implication is trivially true). -/
lemma EReal.le_of_forall_pos_le_add' {a b : EReal}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ε) : a ≤ b := by
  by_cases hb : b = ⊤
  · simp [hb]
  · by_contra ha_gt
    push_neg at ha_gt
    -- a > b and b ≠ ⊤
    induction a using EReal.rec with
    | bot => simp at ha_gt
    | top =>
      -- a = ⊤, b ≠ ⊤ means ⊤ ≤ b + 1 must hold by h, but b + 1 < ⊤
      specialize h 1 (by norm_num : (0:ℝ) < 1)
      have hb1 : b + (1 : ℝ) < ⊤ := by
        cases b with
        | bot => simp
        | top => exact (hb rfl).elim
        | coe b' =>
          have : (b' : EReal) + (1:ℝ) = ((b' + 1) : ℝ) := by norm_cast
          rw [this]; exact EReal.coe_lt_top _
      exact not_le.mpr hb1 h
    | coe a' =>
      induction b using EReal.rec with
      | bot =>
        -- b = ⊥, so a' > ⊥ always. But ⊥ + ε = ⊥, so h gives a' ≤ ⊥, contradiction
        specialize h 1 (by norm_num : (0:ℝ) < 1)
        simp at h
      | top => exact hb rfl
      | coe b' =>
        -- Both finite: a' > b', pick ε = (a' - b') / 2
        have hab : b' < a' := EReal.coe_lt_coe_iff.mp ha_gt
        specialize h ((a' - b') / 2) (by linarith)
        rw [show (b' : EReal) + ((a' - b') / 2 : ℝ) = ((b' + (a' - b') / 2) : ℝ) by norm_cast] at h
        have h_ineq : b' + (a' - b') / 2 < a' := by linarith
        exact not_le.mpr (EReal.coe_lt_coe_iff.mpr h_ineq) h



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



namespace BoundedInterval
/-- Extract the left and right endpoints of a BoundedInterval.
    Returns (a, b) where a is the left endpoint and b is the right endpoint. -/
def endpoints (I : BoundedInterval) : ℝ × ℝ :=
  match I with
  | Ioo a b => (a, b)
  | Icc a b => (a, b)
  | Ioc a b => (a, b)
  | Ico a b => (a, b)

/-- Compute the midpoint of a BoundedInterval. -/
noncomputable def midpoint (I : BoundedInterval) : ℝ :=
  let (a, b) := I.endpoints
  (a + b) / 2

/-- Bisect a BoundedInterval into left and right halves using closed intervals.
    Left half: [a, m], Right half: [m, b], where m is the midpoint.
    Using closed intervals ensures coverage (union equals original) while
    maintaining measure-theoretic properties (overlap has measure zero). -/
noncomputable def bisect (I : BoundedInterval) : BoundedInterval × BoundedInterval :=
  let (a, b) := I.endpoints
  let m := I.midpoint
  (Icc a m, Icc m b)

/-- Bisecting an interval gives distinct sub-intervals unless the interval is degenerate -/
lemma bisect_fst_ne_snd (I : BoundedInterval) :
    I.bisect.fst ≠ I.bisect.snd ∨ I.a = I.b := by
  unfold bisect midpoint endpoints
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    by_cases hab : a = b
    · right; exact hab
    · left
      intro h
      have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h
      have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h
      exact hab (by linarith)
  | Icc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    by_cases hab : a = b
    · right; exact hab
    · left
      intro h
      have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h
      have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h
      exact hab (by linarith)
  | Ioc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    by_cases hab : a = b
    · right; exact hab
    · left
      intro h
      have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h
      have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h
      exact hab (by linarith)
  | Ico a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    by_cases hab : a = b
    · right; exact hab
    · left
      intro h
      have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h
      have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h
      exact hab (by linarith)

/-- The left half of bisection has half the original length -/
lemma bisect_fst_length (I : BoundedInterval) :
    |(I.bisect.fst)|ₗ = |I|ₗ / 2 := by
  unfold bisect midpoint endpoints length
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    -- Goal: max ((a + b) / 2 - a) 0 = max (b - a) 0 / 2
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Icc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ioc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ico a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]

/-- The right half of bisection has half the original length -/
lemma bisect_snd_length (I : BoundedInterval) :
    |(I.bisect.snd)|ₗ = |I|ₗ / 2 := by
  unfold bisect midpoint endpoints length
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    -- Goal: max (b - (a + b) / 2) 0 = max (b - a) 0 / 2
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Icc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ioc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ico a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]

/-- Bisecting preserves total length -/
lemma bisect_length_sum (I : BoundedInterval) :
    |(I.bisect.fst)|ₗ + |(I.bisect.snd)|ₗ = |I|ₗ := by
  rw [bisect_fst_length, bisect_snd_length]
  ring

/-- The left endpoint of bisect.fst is I.a -/
@[simp]
lemma bisect_fst_a (I : BoundedInterval) : (I.bisect.fst).a = I.a := by
  unfold bisect endpoints
  cases I <;> simp [BoundedInterval.a]

/-- The left endpoint of bisect.snd is I.midpoint -/
@[simp]
lemma bisect_snd_a (I : BoundedInterval) : (I.bisect.snd).a = I.midpoint := by
  unfold bisect endpoints
  cases I <;> simp [BoundedInterval.a, midpoint]

/-- The midpoint equals a + length/2 when a ≤ b (non-degenerate interval) -/
lemma midpoint_eq_a_add_half_length (I : BoundedInterval) (h : I.a ≤ I.b) :
    I.midpoint = I.a + |I|ₗ / 2 := by
  unfold midpoint endpoints length
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring
  | Icc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring
  | Ioc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring
  | Ico a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring

/-- For Icc intervals (the result of bisect), midpoint = a + (b-a)/2 -/
lemma Icc_midpoint_eq (a b : ℝ) : (Icc a b : BoundedInterval).midpoint = (a + b) / 2 := by
  simp [midpoint, endpoints]

/-- The midpoint is in the first half of bisection (as the right endpoint of Icc) -/
lemma midpoint_mem_bisect_fst (I : BoundedInterval) (h : I.toSet.Nonempty) :
    I.midpoint ∈ (I.bisect.fst).toSet := by
  obtain ⟨x, hx⟩ := h
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩

/-- The midpoint is in the second half of bisection (as the left endpoint of Icc) -/
lemma midpoint_mem_bisect_snd (I : BoundedInterval) (h : I.toSet.Nonempty) :
    I.midpoint ∈ (I.bisect.snd).toSet := by
  obtain ⟨x, hx⟩ := h
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩

/-- Every point in I.toSet is in one half of the bisection -/
lemma mem_bisect_of_mem_toSet (I : BoundedInterval) (x : ℝ) (hx : x ∈ I.toSet) :
    x ∈ (I.bisect.fst).toSet ∨ x ∈ (I.bisect.snd).toSet := by
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    by_cases hm : x ≥ (a + b) / 2
    · right; simp only [Set.mem_Icc]; exact ⟨hm, by linarith⟩
    · left; push_neg at hm; simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    by_cases hm : x ≥ (a + b) / 2
    · right; simp only [Set.mem_Icc]; exact ⟨hm, by linarith⟩
    · left; push_neg at hm; simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    by_cases hm : x ≥ (a + b) / 2
    · right; simp only [Set.mem_Icc]; exact ⟨hm, by linarith⟩
    · left; push_neg at hm; simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    by_cases hm : x ≥ (a + b) / 2
    · right; simp only [Set.mem_Icc]; exact ⟨hm, by linarith⟩
    · left; push_neg at hm; simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩

/-- A point is in I.bisect.snd iff it's in I.toSet and at or above the midpoint -/
lemma mem_bisect_snd_iff (I : BoundedInterval) (x : ℝ) (hx : x ∈ I.toSet) :
    x ∈ (I.bisect.snd).toSet ↔ x ≥ I.midpoint := by
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩

/-- A point is in I.bisect.fst iff it's in I.toSet and below the midpoint -/
lemma mem_bisect_fst_iff (I : BoundedInterval) (x : ℝ) (hx : x ∈ I.toSet) :
    x ∈ (I.bisect.fst).toSet ↔ x ≤ I.midpoint := by
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩

/-- If two intervals have equal bisect.fst, then their endpoints match -/
lemma bisect_fst_eq_endpoints {I₁ I₂ : BoundedInterval}
    (h : I₁.bisect.fst = I₂.bisect.fst) : I₁.a = I₂.a ∧ I₁.b = I₂.b := by
  -- bisect.fst = Icc I.a I.midpoint, so (bisect.fst).a = I.a
  have ha' : (I₁.bisect.fst).a = (I₂.bisect.fst).a := congrArg (·.a) h
  have hm' : (I₁.bisect.fst).b = (I₂.bisect.fst).b := congrArg (·.b) h
  simp only [bisect, endpoints, midpoint, BoundedInterval.a, BoundedInterval.b] at ha' hm'
  constructor
  · cases I₁ <;> cases I₂ <;> simp_all
  · cases I₁ <;> cases I₂ <;> simp only [BoundedInterval.b] at ha' hm' ⊢ <;> linarith

/-- If two intervals have equal bisect.snd, then their endpoints match -/
lemma bisect_snd_eq_endpoints {I₁ I₂ : BoundedInterval}
    (h : I₁.bisect.snd = I₂.bisect.snd) : I₁.a = I₂.a ∧ I₁.b = I₂.b := by
  -- bisect.snd = Icc midpoint b, so (bisect.snd).a = midpoint and (bisect.snd).b = b
  have hm' : (I₁.bisect.snd).a = (I₂.bisect.snd).a := congrArg (·.a) h
  have hb' : (I₁.bisect.snd).b = (I₂.bisect.snd).b := congrArg (·.b) h
  -- The .b of bisect.snd is just I.b, and .a is (I.a + I.b)/2
  cases I₁ with | _ a₁ b₁ =>
  cases I₂ with | _ a₂ b₂ =>
  all_goals simp only [bisect, endpoints, midpoint, BoundedInterval.a, BoundedInterval.b] at hm' hb' ⊢
  -- Now hm' : (a₁ + b₁)/2 = (a₂ + b₂)/2 and hb' : b₁ = b₂
  all_goals constructor <;> linarith

/-- When a = b, bisect.fst = bisect.snd -/
lemma bisect_fst_eq_snd_of_endpoints_eq {I : BoundedInterval} (h : I.a = I.b) :
    I.bisect.fst = I.bisect.snd := by
  cases I with
  | Ioo a b => simp only [BoundedInterval.a, BoundedInterval.b] at h; simp [bisect, endpoints, midpoint, h]
  | Icc a b => simp only [BoundedInterval.a, BoundedInterval.b] at h; simp [bisect, endpoints, midpoint, h]
  | Ioc a b => simp only [BoundedInterval.a, BoundedInterval.b] at h; simp [bisect, endpoints, midpoint, h]
  | Ico a b => simp only [BoundedInterval.a, BoundedInterval.b] at h; simp [bisect, endpoints, midpoint, h]

/-- Cross-case fst=snd equality forces a₁ = b₁ when a₁ = a₂ -/
lemma bisect_fst_eq_snd_forces_degenerate {I₁ I₂ : BoundedInterval}
    (h : I₁.bisect.fst = I₂.bisect.snd) (ha : I₁.a = I₂.a) : I₁.a = I₁.b ∧ I₂.a = I₂.b := by
  cases I₁ with | _ a₁ b₁ =>
  cases I₂ with | _ a₂ b₂ =>
  simp only [bisect, endpoints, midpoint, BoundedInterval.a, BoundedInterval.b] at h ha ⊢
  -- Extract the equality of left and right endpoints from bisect equality
  have h_a_eq : a₁ = (a₂ + b₂) / 2 := congrArg BoundedInterval.a h
  have h_b_eq : (a₁ + b₁) / 2 = b₂ := congrArg BoundedInterval.b h
  simp only [] at h_a_eq h_b_eq
  constructor <;> linarith

/-- Cross-case: if bisect.fst = bisect.snd, the intervals have overlapping midpoint and endpoint -/
lemma bisect_fst_eq_snd_shift {I₁ I₂ : BoundedInterval}
    (h : I₁.bisect.fst = I₂.bisect.snd) : I₁.a = (I₂.a + I₂.b) / 2 := by
  -- (bisect.fst).a = I.a, (bisect.snd).a = I.midpoint = (I.a + I.b)/2
  have ha' : (I₁.bisect.fst).a = (I₂.bisect.snd).a := congrArg (·.a) h
  cases I₁ with | _ a₁ b₁ =>
  cases I₂ with | _ a₂ b₂ =>
  all_goals simp only [bisect, endpoints, midpoint, BoundedInterval.a, BoundedInterval.b] at ha' ⊢
  all_goals linarith

/-- Cross-case: if bisect.snd = bisect.fst, the intervals have overlapping endpoint and midpoint -/
lemma bisect_snd_eq_fst_shift {I₁ I₂ : BoundedInterval}
    (h : I₁.bisect.snd = I₂.bisect.fst) : I₂.a = (I₁.a + I₁.b) / 2 := by
  have : I₂.bisect.fst = I₁.bisect.snd := h.symm
  exact bisect_fst_eq_snd_shift this

/-- Icc intervals with equal endpoints are equal -/
@[simp]
lemma Icc_eq_Icc_iff {a₁ b₁ a₂ b₂ : ℝ} :
    (Icc a₁ b₁ : BoundedInterval) = Icc a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · intro h
    exact ⟨congrArg BoundedInterval.a h, congrArg BoundedInterval.b h⟩
  · intro ⟨ha, hb⟩
    simp [ha, hb]

end BoundedInterval

namespace Box
/-- The diameter of a box is the supremum of Euclidean distances between points in the box -/
noncomputable def diameter {d:ℕ} (B: Box d) : ℝ :=
  sSup { r | ∃ x ∈ B.toSet, ∃ y ∈ B.toSet, r = √(∑ i, (x i - y i)^2) }

/-- Diameter is always nonnegative -/
lemma diameter_nonneg {d:ℕ} (B: Box d) : 0 ≤ B.diameter := by
  unfold diameter
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
lemma diameter_of_empty {d:ℕ} (B: Box d) (h: B.toSet = ∅) :
    B.diameter = 0 := by
  unfold diameter
  simp [h, sSup]

/-- Any two points in a box have Euclidean distance at most the diameter -/
lemma dist_le_diameter {d:ℕ} (B: Box d) {x y: EuclideanSpace' d}
    (hx: x ∈ B.toSet) (hy: y ∈ B.toSet) :
    √(∑ i, (x i - y i)^2) ≤ B.diameter := by
  unfold diameter
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
lemma diameter_bound_by_sides {d:ℕ} (B: Box d) :
    B.diameter ≤ Real.sqrt d * (⨆ i, |B.side i|ₗ) := by
  unfold diameter
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

/-- For any nonempty interval and target value less than the length,
    we can find two points in the interval with separation exceeding the target.
    This is the key density fact: achievable differences are dense in [0, length]. -/
lemma BoundedInterval.exists_points_with_diff {I : BoundedInterval}
    (h_nonempty : I.toSet.Nonempty) {t : ℝ} (ht_nonneg : 0 ≤ t) (ht : t < |I|ₗ) :
    ∃ x ∈ I.toSet, ∃ y ∈ I.toSet, t < |x - y| := by
  -- Since t < |I|ₗ = max (b - a) 0 and t ≥ 0, we have b - a > t ≥ 0
  have h_len_pos : 0 < |I|ₗ := lt_of_le_of_lt ht_nonneg ht
  cases I with
  | Icc a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Closed: use endpoints a and b
    refine ⟨a, Set.left_mem_Icc.mpr (le_of_lt h_ab), b, Set.right_mem_Icc.mpr (le_of_lt h_ab), ?_⟩
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < b - a)]
    linarith
  | Ioo a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Open: use points close to endpoints
    set δ := ((b - a) - t) / 2 with hδ_def
    have h_δ_pos : 0 < δ := by linarith
    have hx_mem : a + δ / 2 ∈ Set.Ioo a b := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    have hy_mem : b - δ / 2 ∈ Set.Ioo a b := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    refine ⟨a + δ / 2, hx_mem, b - δ / 2, hy_mem, ?_⟩
    have h_diff : (b - δ / 2) - (a + δ / 2) = (b - a) - δ := by ring
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < (b - δ / 2) - (a + δ / 2)), h_diff]
    linarith
  | Ioc a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Left open, right closed: use point close to a and b
    set δ := ((b - a) - t) / 2 with hδ_def
    have h_δ_pos : 0 < δ := by linarith
    have hx_mem : a + δ / 2 ∈ Set.Ioc a b := Set.mem_Ioc.mpr ⟨by linarith, by linarith⟩
    have hy_mem : b ∈ Set.Ioc a b := Set.mem_Ioc.mpr ⟨h_ab, le_refl b⟩
    refine ⟨a + δ / 2, hx_mem, b, hy_mem, ?_⟩
    have h_diff : b - (a + δ / 2) = (b - a) - δ / 2 := by ring
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < b - (a + δ / 2)), h_diff]
    linarith
  | Ico a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Left closed, right open: use a and point close to b
    set δ := ((b - a) - t) / 2 with hδ_def
    have h_δ_pos : 0 < δ := by linarith
    have hx_mem : a ∈ Set.Ico a b := Set.mem_Ico.mpr ⟨le_refl a, h_ab⟩
    have hy_mem : b - δ / 2 ∈ Set.Ico a b := Set.mem_Ico.mpr ⟨by linarith, by linarith⟩
    refine ⟨a, hx_mem, b - δ / 2, hy_mem, ?_⟩
    have h_diff : (b - δ / 2) - a = (b - a) - δ / 2 := by ring
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < (b - δ / 2) - a), h_diff]
    linarith

/-- The diameter of a nonempty box equals the diagonal length √(∑ |side i|ₗ²).
    This is the key fact: the supremum of pairwise distances equals the diagonal.
    For closed intervals, the diagonal is achieved at corners.
    For open intervals, the diagonal is the limit (supremum) of achievable distances. -/
lemma diameter_eq_sqrt_sum_sq {d:ℕ} (B: Box d) (h: B.toSet.Nonempty) :
    B.diameter = √(∑ i, |B.side i|ₗ^2) := by
  unfold diameter
  -- Use csSup_eq_of_forall_le_of_forall_lt_exists_gt:
  -- if s.Nonempty ∧ (∀ a ∈ s, a ≤ b) ∧ (∀ c < b, ∃ a ∈ s, c < a), then sSup s = b
  let s := { r | ∃ x ∈ B.toSet, ∃ y ∈ B.toSet, r = √(∑ i, (x i - y i)^2) }
  let b := √(∑ i, |B.side i|ₗ^2)
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · -- s is nonempty
    obtain ⟨x, hx⟩ := h
    exact ⟨√(∑ i, (x i - x i)^2), x, hx, x, hx, rfl⟩
  · -- ∀ a ∈ s, a ≤ b (upper bound)
    intro r ⟨x, hx, y, hy, hr⟩
    rw [hr]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    -- |x i - y i|² ≤ |B.side i|ₗ²
    have hx_i : x i ∈ (B.side i).toSet := hx i (Set.mem_univ i)
    have hy_i : y i ∈ (B.side i).toSet := hy i (Set.mem_univ i)
    have coord_bound : |x i - y i| ≤ |B.side i|ₗ := by
      cases h_side : B.side i <;>
          simp [BoundedInterval.toSet, h_side] at hx_i hy_i <;>
          simp [BoundedInterval.length] <;>
          (left; rw [abs_sub_le_iff]; constructor <;> linarith [hx_i.1, hx_i.2, hy_i.1, hy_i.2])
    calc (x i - y i)^2 = |x i - y i|^2 := by rw [sq_abs]
      _ ≤ |B.side i|ₗ^2 := by
          apply sq_le_sq' <;> [linarith [abs_nonneg (x i - y i), coord_bound]; exact coord_bound]
  · -- ∀ c < b, ∃ a ∈ s, c < a (density: can get arbitrarily close to b)
    intro c hc
    -- Need to find x, y ∈ B with √(∑ (x i - y i)²) > c
    -- Strategy: for each coordinate, pick points near opposite ends of the interval
    -- The resulting distance will be close to √(∑ side²)
    -- Since c < √(∑ side²), we can find ε > 0 such that c < √(∑ side²) - ε
    -- Then pick x, y such that |x i - y i| ≥ |side i| - δ for small enough δ
    -- This gives √(∑ (x i - y i)²) ≥ √(∑ (side - δ)²) > c for small δ
    --
    -- For the formal proof, we use that intervals are nonempty (from h_nonempty)
    -- and that we can pick points with controlled distances from endpoints.
    by_cases h_zero : (∑ i, |B.side i|ₗ^2) = 0
    · -- All sides have length 0, so b = 0
      -- c < 0 is impossible since distances are ≥ 0
      simp only [h_zero, Real.sqrt_zero] at hc
      -- c < 0, but any distance is ≥ 0, so we need c < some distance ≥ 0
      -- Since c < 0, we have c < 0 ≤ any distance
      obtain ⟨x, hx⟩ := h
      use 0
      constructor
      · exact ⟨x, hx, x, hx, by simp⟩
      · linarith
    · -- Some side has positive length
      -- Use the characterization: √(∑ side²) > c means ∑ side² > c²
      have h_pos : 0 < ∑ i, |B.side i|ₗ^2 := by
        apply lt_of_le_of_ne
        · apply Finset.sum_nonneg; intro i _; exact sq_nonneg _
        · exact Ne.symm h_zero
      -- Get ε such that c + ε < √(∑ side²)
      have h_c_lt : c < √(∑ i, |B.side i|ₗ^2) := hc
      -- Since c < √(∑ side²), we have c² < ∑ side² (for c ≥ 0) or c < 0
      by_cases hc_nonneg : 0 ≤ c
      · -- c ≥ 0 case: we need to construct points with large distance
        -- Strategy: use exists_points_with_diff for positive-length coordinates
        -- Each interval is nonempty (from h: B.toSet.Nonempty)
        have h_interval_nonempty : ∀ i, (B.side i).toSet.Nonempty := by
          intro i; obtain ⟨x, hx⟩ := h
          exact ⟨x i, hx i (Set.mem_univ i)⟩
        -- We'll construct points coordinate-wise with ≥ for all and > for positive-length
        let ratio := c / √(∑ i, |B.side i|ₗ^2)
        have h_ratio_lt_one : ratio < 1 := by
          show c / √(∑ i, |B.side i|ₗ^2) < 1
          rw [div_lt_one (Real.sqrt_pos.mpr h_pos)]
          exact h_c_lt
        have h_ratio_nonneg : 0 ≤ ratio := by
          show 0 ≤ c / √(∑ i, |B.side i|ₗ^2)
          exact div_nonneg hc_nonneg (Real.sqrt_nonneg _)
        -- For positive-length coordinates: get strict inequality
        have h_exists_points : ∀ i, ∃ xi ∈ (B.side i).toSet, ∃ yi ∈ (B.side i).toSet,
            |B.side i|ₗ * ratio ≤ |xi - yi| ∧
            (0 < |B.side i|ₗ → |B.side i|ₗ * ratio < |xi - yi|) := by
          intro i
          by_cases h_len_zero : |B.side i|ₗ = 0
          · -- Zero-length interval: xi = yi gives 0 ≤ 0
            obtain ⟨xi, hxi⟩ := h_interval_nonempty i
            refine ⟨xi, hxi, xi, hxi, ?_, ?_⟩
            · simp [h_len_zero]
            · simp [h_len_zero]
          · -- Positive-length interval: use exists_points_with_diff
            have h_len_pos : 0 < |B.side i|ₗ := by
              apply lt_of_le_of_ne; simp [BoundedInterval.length]; exact Ne.symm h_len_zero
            have h_target_lt : |B.side i|ₗ * ratio < |B.side i|ₗ := by
              calc |B.side i|ₗ * ratio < |B.side i|ₗ * 1 := by
                    apply mul_lt_mul_of_pos_left h_ratio_lt_one h_len_pos
                _ = |B.side i|ₗ := mul_one _
            obtain ⟨xi, hxi, yi, hyi, hlt⟩ := BoundedInterval.exists_points_with_diff
              (h_interval_nonempty i) (mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg)
              h_target_lt
            exact ⟨xi, hxi, yi, hyi, le_of_lt hlt, fun _ => hlt⟩
        -- Use Classical.choose to extract the points
        classical
        let x : Fin d → ℝ := fun i => (h_exists_points i).choose
        let y : Fin d → ℝ := fun i => (h_exists_points i).choose_spec.2.choose
        have hx_mem : ∀ i, x i ∈ (B.side i).toSet := fun i => (h_exists_points i).choose_spec.1
        have hy_mem : ∀ i, y i ∈ (B.side i).toSet := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.1
        have h_diff_le : ∀ i, |B.side i|ₗ * ratio ≤ |x i - y i| := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.2.1
        have h_diff_lt : ∀ i, 0 < |B.side i|ₗ → |B.side i|ₗ * ratio < |x i - y i| := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.2.2
        -- x, y ∈ B.toSet
        have hx_box : x ∈ B.toSet := fun i _ => hx_mem i
        have hy_box : y ∈ B.toSet := fun i _ => hy_mem i
        -- The distance √(∑ (x_i - y_i)²) > c
        use √(∑ i, (x i - y i)^2)
        constructor
        · exact ⟨x, hx_box, y, hy_box, rfl⟩
        · -- Need: c < √(∑ (x_i - y_i)²)
          rw [← Real.sqrt_sq hc_nonneg]
          apply Real.sqrt_lt_sqrt (sq_nonneg c)
          -- Need: c² < ∑ (x_i - y_i)²
          -- c² = ∑ (side * ratio)² and we have ≤ for all, < for at least one positive side
          have h_target : c^2 = ∑ i, (|B.side i|ₗ * ratio)^2 := by
            have h_sum_nonneg : 0 ≤ ∑ i : Fin d, |B.side i|ₗ^2 :=
              Finset.sum_nonneg (fun i _ => sq_nonneg (|B.side i|ₗ))
            have h_sqrt_ne : √(∑ i, |B.side i|ₗ^2) ≠ 0 := Real.sqrt_ne_zero'.mpr h_pos
            calc c^2 = (√(∑ i, |B.side i|ₗ^2) * ratio)^2 := by
                  show c^2 = (√(∑ i, |B.side i|ₗ^2) * (c / √(∑ i, |B.side i|ₗ^2)))^2
                  field_simp
              _ = (∑ i, |B.side i|ₗ^2) * ratio^2 := by
                  rw [mul_pow, Real.sq_sqrt h_sum_nonneg]
              _ = ∑ i, |B.side i|ₗ^2 * ratio^2 := Finset.sum_mul _ _ _
              _ = ∑ i, (|B.side i|ₗ * ratio)^2 := by congr 1; ext i; ring
          rw [h_target]
          -- Since ∑ side² > 0, at least one side is positive
          have h_exists_pos : ∃ j, 0 < |B.side j|ₗ := by
            by_contra h_all_zero; push_neg at h_all_zero
            have h_sum_zero : (∑ i, |B.side i|ₗ^2) = 0 := by
              apply Finset.sum_eq_zero; intro i _
              have : |B.side i|ₗ ≤ 0 := h_all_zero i
              have h_nonneg : 0 ≤ |B.side i|ₗ := by simp [BoundedInterval.length]
              have : |B.side i|ₗ = 0 := le_antisymm this h_nonneg
              simp [this]
            exact h_zero h_sum_zero
          obtain ⟨j, hj_pos⟩ := h_exists_pos
          apply Finset.sum_lt_sum
          · intro i _
            have h_sq : (|B.side i|ₗ * ratio)^2 ≤ |x i - y i|^2 := by
              apply sq_le_sq' _ (h_diff_le i)
              calc -(|x i - y i|) ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
                _ ≤ |B.side i|ₗ * ratio := mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg
            calc (|B.side i|ₗ * ratio)^2 ≤ |x i - y i|^2 := h_sq
              _ = (x i - y i)^2 := by rw [sq_abs]
          · use j, Finset.mem_univ j
            have h_sq_lt : (|B.side j|ₗ * ratio)^2 < |x j - y j|^2 := by
              -- From h_diff_lt we know side * ratio < |x j - y j|, so |x j - y j| > 0
              have h_diff_pos : 0 < |x j - y j| :=
                lt_of_le_of_lt (mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg)
                  (h_diff_lt j hj_pos)
              apply sq_lt_sq' _ (h_diff_lt j hj_pos)
              calc -(|x j - y j|) < 0 := neg_neg_of_pos h_diff_pos
                _ ≤ |B.side j|ₗ * ratio := mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg
            calc (|B.side j|ₗ * ratio)^2 < |x j - y j|^2 := h_sq_lt
              _ = (x j - y j)^2 := by rw [sq_abs]
      · -- c < 0 case: any distance ≥ 0 > c
        push_neg at hc_nonneg
        obtain ⟨x, hx⟩ := h
        use 0
        constructor
        · exact ⟨x, hx, x, hx, by simp⟩
        · linarith

/-- If a box intersects two sets, any two points (one from each set)
    in the box have distance at most the diameter -/
lemma diameter_ge_dist_of_intersects {d:ℕ} (B: Box d) (E F : Set (EuclideanSpace' d))
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
    dist_le_diameter B hx_box hy_box
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
lemma not_intersects_both_of_diameter_lt {d:ℕ} (B: Box d) (E F : Set (EuclideanSpace' d))
    (h : B.diameter < set_dist E F) :
    ¬((B.toSet ∩ E).Nonempty ∧ (B.toSet ∩ F).Nonempty) := by
  intro ⟨hE, hF⟩
  -- If B intersects both, then set_dist E F ≤ B.diameter
  have := diameter_ge_dist_of_intersects B E F hE hF
  -- But we assumed B.diameter < set_dist E F
  linarith

open Classical in
/-- Decidable equality for boxes, needed for Finset operations -/
noncomputable instance {d:ℕ} : DecidableEq (Box d) := instDecidableEqOfLawfulBEq

/-- Subdivide a box by bisecting each coordinate axis, producing 2^d sub-boxes.
    Each sub-box is formed by taking one half-interval from each coordinate.
    We use Finset.univ (all possible d-bit patterns) to enumerate all 2^d combinations. -/
noncomputable def subdivide {d:ℕ} (B: Box d) : Finset (Box d) :=
  -- For each choice ∈ Fin d → Bool (which half to take for each coordinate),
  -- construct a sub-box by taking the left half (if false) or right half (if true)
  Finset.univ.image fun (choice : Fin d → Bool) =>
    { side := fun i =>
        let (left, right) := (B.side i).bisect
        if choice i then right else left }

/-- Distributive law: product of sums over Fin d equals sum over boolean choices of products.
    This is the key identity: ∏ᵢ (aᵢ + bᵢ) = ∑_{c : Fin d → Bool} ∏ᵢ (if cᵢ then bᵢ else aᵢ) -/
lemma Fin.prod_add_eq_sum_prod_choice (d : ℕ) (a b : Fin d → ℝ) :
    ∏ i, (a i + b i) = ∑ c : Fin d → Bool, ∏ i, (if c i then b i else a i) := by
  induction d with
  | zero =>
    -- Empty product = 1, and there's exactly one function Fin 0 → Bool
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    have h_card : (Finset.univ : Finset (Fin 0 → Bool)).card = 1 := by simp
    rw [Finset.card_eq_one] at h_card
    obtain ⟨f, hf⟩ := h_card
    simp only [hf, Finset.sum_singleton]
  | succ d ih =>
    -- Split off first coordinate: ∏_{i:Fin(d+1)} = (first term) * ∏_{i:Fin d}
    rw [Fin.prod_univ_succ]
    -- Apply IH to the tail
    let a' : Fin d → ℝ := fun i => a i.succ
    let b' : Fin d → ℝ := fun i => b i.succ
    have h_tail : ∏ i : Fin d, (a i.succ + b i.succ) = ∏ i, (a' i + b' i) := rfl
    rw [h_tail, ih a' b']
    -- Distribute: (a 0 + b 0) * (∑ c', ...) = b 0 * (∑ c', ...) + a 0 * (∑ c', ...)
    rw [add_comm (a 0) (b 0), add_mul, Finset.mul_sum, Finset.mul_sum]
    -- Split RHS sum by first bit: ∑_c = ∑_{c 0 = true} + ∑_{c 0 = false}
    symm
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c : Fin (d+1) → Bool => c 0)]
    -- Now: (∑_{c 0 = true} ...) + (∑_{c 0 = false} ...) = b 0 * (...) + a 0 * (...)
    congr 1
    · -- c 0 = true case
      have h_factor : ∀ c ∈ Finset.filter (fun c : Fin (d+1) → Bool => c 0) Finset.univ,
          ∏ i, (if c i then b i else a i) =
          b 0 * ∏ i : Fin d, (if c i.succ then b' i else a' i) := by
        intro c hc
        rw [Fin.prod_univ_succ]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        simp only [hc, ↓reduceIte, a', b']
      rw [Finset.sum_congr rfl h_factor, ← Finset.mul_sum]
      -- Now goal is: b 0 * (∑ c ∈ filter, ∏...) = b 0 * (∑ c' ∈ univ, ∏...)
      -- Need to show the sums are equal, then multiply by b 0
      have h_sum_eq : ∑ c ∈ Finset.filter (fun c : Fin (d+1) → Bool => c 0) Finset.univ,
          ∏ i : Fin d, (if c i.succ then b' i else a' i) =
          ∑ c' : Fin d → Bool, ∏ i, (if c' i then b' i else a' i) := by
        symm
        refine Finset.sum_bij (fun (c' : Fin d → Bool) _ => Fin.cons true c') ?_ ?_ ?_ ?_
        · intro c' _
          simp only [Finset.mem_filter, Finset.mem_univ, Fin.cons_zero, true_and]
        · intro c₁ _ c₂ _ heq
          simp only at heq
          funext i
          have h : (Fin.cons true c₁ : Fin (d+1) → Bool) i.succ =
                   (Fin.cons true c₂ : Fin (d+1) → Bool) i.succ := by rw [heq]
          simp only [Fin.cons_succ] at h
          exact h
        · intro c hc
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          refine ⟨fun i => c i.succ, Finset.mem_univ _, ?_⟩
          funext i; cases' i using Fin.cases with i
          · simp only [Fin.cons_zero]; exact hc.symm
          · simp only [Fin.cons_succ]
        · intro c' _
          apply Finset.prod_congr rfl; intro i _
          simp only [Fin.cons_succ]
      rw [h_sum_eq, Finset.mul_sum]
    · -- c 0 = false case
      have h_factor : ∀ c ∈ Finset.filter (fun c : Fin (d+1) → Bool => ¬c 0) Finset.univ,
          ∏ i, (if c i then b i else a i) =
          a 0 * ∏ i : Fin d, (if c i.succ then b' i else a' i) := by
        intro c hc
        rw [Fin.prod_univ_succ]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        simp only [Bool.eq_false_iff.mpr hc, Bool.false_eq_true, ↓reduceIte, a', b']
      rw [Finset.sum_congr rfl h_factor, ← Finset.mul_sum]
      have h_sum_eq : ∑ c ∈ Finset.filter (fun c : Fin (d+1) → Bool => ¬c 0) Finset.univ,
          ∏ i : Fin d, (if c i.succ then b' i else a' i) =
          ∑ c' : Fin d → Bool, ∏ i, (if c' i then b' i else a' i) := by
        symm
        refine Finset.sum_bij (fun (c' : Fin d → Bool) _ => Fin.cons false c') ?_ ?_ ?_ ?_
        · intro c' _
          simp only [Finset.mem_filter, Finset.mem_univ, Fin.cons_zero]
          trivial
        · intro c₁ _ c₂ _ heq
          simp only at heq
          funext i
          have h : (Fin.cons false c₁ : Fin (d+1) → Bool) i.succ =
                   (Fin.cons false c₂ : Fin (d+1) → Bool) i.succ := by rw [heq]
          simp only [Fin.cons_succ] at h
          exact h
        · intro c hc
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          refine ⟨fun i => c i.succ, Finset.mem_univ _, ?_⟩
          funext i; cases' i using Fin.cases with i
          · simp only [Fin.cons_zero]; exact (Bool.eq_false_iff.mpr hc).symm
          · simp only [Fin.cons_succ]
        · intro c' _
          apply Finset.prod_congr rfl; intro i _
          simp only [Fin.cons_succ]
      rw [h_sum_eq, Finset.mul_sum]

/-- The volume of a subdivided box equals the sum of its sub-box volumes -/
lemma volume_subdivide {d:ℕ} (B: Box d) :
    ∑ B' ∈ B.subdivide, |B'|ᵥ = |B|ᵥ := by
  unfold subdivide Box.volume
  -- Establish that each coordinate's length splits into two halves
  have h_sum : ∀ i, |(B.side i)|ₗ = |(B.side i).bisect.fst|ₗ + |(B.side i).bisect.snd|ₗ := by
    intro i; exact (BoundedInterval.bisect_length_sum (B.side i)).symm
  -- Rewrite RHS using the sum identity
  have h_rhs : ∏ i, |(B.side i)|ₗ = ∏ i, (|(B.side i).bisect.fst|ₗ + |(B.side i).bisect.snd|ₗ) := by
    apply Finset.prod_congr rfl; intro i _; exact h_sum i
  rw [h_rhs, Fin.prod_add_eq_sum_prod_choice d _ _]
  -- The mapping from choice to box
  let g : (Fin d → Bool) → Box d := fun c =>
    { side := fun i => let (l, r) := (B.side i).bisect; if c i then r else l }
  -- Key: volume of g c equals the product of half-lengths
  have h_vol_eq : ∀ c : Fin d → Bool, |g c|ᵥ =
      ∏ i, (if c i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ) := by
    intro c; unfold Box.volume; apply Finset.prod_congr rfl; intro i _
    simp only [g]; split_ifs <;> rfl
  -- Two choices give same product when they map to same box
  have h_prod_eq : ∀ c₁ c₂ : Fin d → Bool, g c₁ = g c₂ →
      (∏ i, (if c₁ i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ)) =
      (∏ i, (if c₂ i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ)) := by
    intro c₁ c₂ heq
    apply Finset.prod_congr rfl; intro i _
    have hside : (g c₁).side i = (g c₂).side i := congrArg (·.side i) heq
    simp only [g] at hside
    cases hc₁ : c₁ i <;> cases hc₂ : c₂ i <;> simp only [hc₁, hc₂, ↓reduceIte, Bool.false_eq_true] at hside ⊢
    -- true/false case: hside : bisect.snd = bisect.fst
    · rw [congrArg BoundedInterval.length hside]
    -- false/true case: hside : bisect.fst = bisect.snd
    · rw [congrArg BoundedInterval.length hside]
  -- Use sum_image' which handles non-injective maps
  let h_func : (Fin d → Bool) → ℝ := fun c =>
    ∏ i, (if c i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ)
  have h_fiber : ∀ c ∈ Finset.univ, |g c|ᵥ = ∑ j ∈ Finset.univ with g j = g c, h_func j := by
    intro c _
    rw [h_vol_eq c]
    have h_fib_eq : ∀ j ∈ Finset.univ, g j = g c → h_func j = h_func c := by
      intro j _ hgj; exact h_prod_eq j c hgj
    -- Goal: h_func c = ∑ j with g j = g c, h_func j
    -- All elements in fiber have value h_func c, so sum = card * h_func c
    conv_rhs => rw [show ∑ j ∈ Finset.univ with g j = g c, h_func j =
        ∑ j ∈ Finset.univ.filter (fun j => g j = g c), h_func j from rfl]
    rw [Finset.sum_eq_card_nsmul (fun x hx => by
      rw [Finset.mem_filter] at hx; exact h_fib_eq x hx.1 hx.2)]
    rw [nsmul_eq_mul]
    -- Need: h_func c = card * h_func c. Holds when card = 1 OR h_func c = 0.
    by_cases h_card : (Finset.univ.filter (fun j => g j = g c)).card = 1
    · simp only [h_card, Nat.cast_one, one_mul]; rfl
    · -- Card ≠ 1, and card ≥ 1 (since c is in fiber), so card > 1
      have h_card_pos : 0 < (Finset.univ.filter (fun j => g j = g c)).card := by
        apply Finset.card_pos.mpr; use c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h_card_gt : 1 < (Finset.univ.filter (fun j => g j = g c)).card := by omega
      obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := Finset.one_lt_card.mp h_card_gt
      rw [Finset.mem_filter] at hc₁ hc₂
      -- c₁ and c₂ differ at some coordinate
      have ⟨i, hi_ne⟩ : ∃ i, c₁ i ≠ c₂ i := by
        by_contra h; push_neg at h; exact hne (funext h)
      -- At that coordinate, g c₁ = g c₂ implies bisect.fst = bisect.snd
      have hside : (g c₁).side i = (g c₂).side i := congrArg (·.side i) (hc₁.2.trans hc₂.2.symm)
      simp only [g] at hside
      -- Extract bisect equality from hside by case analysis on c₁ i and c₂ i
      have h_bisect_eq : (B.side i).bisect.fst = (B.side i).bisect.snd := by
        cases hc₁i : c₁ i <;> cases hc₂i : c₂ i <;>
        simp only [hc₁i, hc₂i, Bool.false_eq_true, ↓reduceIte] at hside hi_ne
        · exact (hi_ne rfl).elim  -- false/false case: contradiction
        · exact hside             -- false/true case: hside : fst = snd
        · exact hside.symm        -- true/false case: hside : snd = fst
        · exact (hi_ne rfl).elim  -- true/true case: contradiction
      -- When fst = snd, the interval is degenerate (point), so length = 0
      have h_len_zero : |(B.side i).bisect.snd|ₗ = 0 := by
        rw [← h_bisect_eq]
        -- bisect.fst = bisect.snd means Icc a m = Icc m b, so a = m = b
        unfold BoundedInterval.bisect BoundedInterval.midpoint BoundedInterval.endpoints at h_bisect_eq
        cases hI : B.side i with
        | Ioo a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
        | Icc a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
        | Ioc a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
        | Ico a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
      -- h_func c has a zero factor at coordinate i, so the product is 0
      have h_len_fst_zero : |(B.side i).bisect.fst|ₗ = 0 := by rw [h_bisect_eq]; exact h_len_zero
      have h_prod_zero : h_func c = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        cases hci : c i
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact h_len_fst_zero
        · simp only [↓reduceIte]; exact h_len_zero
      simp only [h_prod_zero, mul_zero]
      -- Goal: h_func c = 0, which is exactly h_prod_zero
      exact h_prod_zero
  rw [Finset.sum_image' h_func h_fiber]

/-- Each sub-box of a subdivision has diameter at most the original diameter divided by √2.
    This follows because each side is halved, reducing the diagonal by a factor related to √2.
    Note: The hypothesis that B is nonempty is necessary because bisection always creates closed
    intervals, which can turn degenerate open intervals (Ioo a a) into nonempty singletons. -/
lemma subdivide_diameter_bound {d:ℕ} (B: Box d) (hB : B.toSet.Nonempty) :
    ∀ B' ∈ B.subdivide, B'.diameter ≤ B.diameter / Real.sqrt 2 := by
  intro B' hB'
  -- Extract the choice function that defines B'
  unfold subdivide at hB'
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hB'
  obtain ⟨choice, rfl⟩ := hB'
  -- Abbreviate the sub-box for readability
  set B' : Box d := { side := fun i => if choice i then (B.side i).bisect.snd
      else (B.side i).bisect.fst } with hB'_def
  -- Key: B'.diameter ≤ B.diameter / 2 ≤ B.diameter / √2
  -- Since √2 < 2, we have B.diameter / 2 ≤ B.diameter / √2
  suffices h : B'.diameter ≤ B.diameter / 2 by
    calc B'.diameter
        ≤ B.diameter / 2 := h
      _ ≤ B.diameter / √2 := by
          apply div_le_div_of_nonneg_left (diameter_nonneg B)
          · exact Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
          · calc √2 ≤ √4 := Real.sqrt_le_sqrt (by norm_num : (2:ℝ) ≤ 4)
              _ = 2 := by norm_num
  -- Now prove B'.diameter ≤ B.diameter / 2
  -- Key: |B'.side i|ₗ = |B.side i|ₗ / 2 for all i, so diagonal is halved
  -- From nonemptiness of B, each side interval is nonempty
  have h_side_nonempty : ∀ i, (B.side i).toSet.Nonempty := by
    intro i; obtain ⟨x, hx⟩ := hB
    exact ⟨x i, hx i (Set.mem_univ i)⟩
  -- First show B' is nonempty (the midpoint of each side is in both halves)
  have hB'_nonempty : B'.toSet.Nonempty := by
    use fun i => (B.side i).midpoint
    intro i _
    simp only [hB'_def]
    split_ifs with h
    · exact BoundedInterval.midpoint_mem_bisect_snd (B.side i) (h_side_nonempty i)
    · exact BoundedInterval.midpoint_mem_bisect_fst (B.side i) (h_side_nonempty i)
  -- Each side of B' has half the length of B's side
  have h_side_half : ∀ i, |B'.side i|ₗ = |B.side i|ₗ / 2 := by
    intro i
    simp only [hB'_def]
    split_ifs with h
    · exact BoundedInterval.bisect_snd_length _
    · exact BoundedInterval.bisect_fst_length _
  -- Use diameter_eq_sqrt_sum_sq for both boxes
  rw [diameter_eq_sqrt_sum_sq B' hB'_nonempty, diameter_eq_sqrt_sum_sq B hB]
  -- √(∑ (side/2)²) = √(∑ side²) / 2
  have h_sum_eq : ∑ i, |B'.side i|ₗ^2 = (∑ i, |B.side i|ₗ^2) / 4 := by
    simp_rw [h_side_half, div_pow]
    rw [Finset.sum_div]
    ring_nf
  rw [h_sum_eq, Real.sqrt_div (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  norm_num

/-- Subdivide a box k times, producing a Finset of boxes.
    After k iterations, each original box becomes up to 2^(d*k) sub-boxes. -/
noncomputable def subdivide_iter {d:ℕ} (B: Box d) : ℕ → Finset (Box d)
  | 0 => {B}
  | k+1 => (subdivide_iter B k).biUnion Box.subdivide

lemma subdivide_iter_zero {d:ℕ} (B: Box d) : subdivide_iter B 0 = {B} := rfl

lemma subdivide_iter_succ {d:ℕ} (B: Box d) (k: ℕ) :
    subdivide_iter B (k+1) = (subdivide_iter B k).biUnion Box.subdivide := rfl

/-- All sides in subdivide (single level) are Icc intervals -/
lemma subdivide_side_is_Icc {d:ℕ} (B: Box d) (B' : Box d) (hB' : B' ∈ B.subdivide) (i : Fin d) :
    ∃ a b, B'.side i = Icc a b := by
  simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hB'
  obtain ⟨c, rfl⟩ := hB'
  -- B' = { side := fun j => if c j then ... else ... }
  -- B'.side i = if c i then (B.side i).bisect.snd else (B.side i).bisect.fst
  simp only  -- This introduces the if-then-else in the goal
  split_ifs with hc
  · -- snd case: (B.side i).bisect.snd is Icc
    unfold BoundedInterval.bisect BoundedInterval.endpoints BoundedInterval.midpoint
    cases B.side i <;> exact ⟨_, _, rfl⟩
  · -- fst case: (B.side i).bisect.fst is Icc
    unfold BoundedInterval.bisect BoundedInterval.endpoints BoundedInterval.midpoint
    cases B.side i <;> exact ⟨_, _, rfl⟩

/-- All sides in subdivide_iter for k ≥ 1 are Icc intervals -/
lemma subdivide_iter_side_is_Icc {d:ℕ} (B: Box d) (k : ℕ) (B' : Box d)
    (hB' : B' ∈ subdivide_iter B (k+1)) (i : Fin d) :
    ∃ a b, B'.side i = Icc a b := by
  induction k generalizing B' with
  | zero =>
    simp only [subdivide_iter, Finset.mem_biUnion, Finset.mem_singleton] at hB'
    obtain ⟨B'', rfl, hB'_sub⟩ := hB'
    exact subdivide_side_is_Icc B'' B' hB'_sub i
  | succ k ih =>
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB'', hB'_sub⟩ := hB'
    exact subdivide_side_is_Icc B'' B' hB'_sub i

/-- All boxes in subdivide_iter have the same side lengths at each coordinate -/
lemma subdivide_iter_side_length {d:ℕ} (B : Box d) (k : ℕ) (B' : Box d)
    (hB' : B' ∈ subdivide_iter B k) (i : Fin d) :
    |B'.side i|ₗ = |B.side i|ₗ / 2^k := by
  induction k generalizing B' with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton] at hB'
    simp [hB']
  | succ k ih =>
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB'', hB'_sub⟩ := hB'
    have h1 := ih B'' hB''
    simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hB'_sub
    obtain ⟨c, rfl⟩ := hB'_sub
    simp only
    split_ifs with hc
    · rw [BoundedInterval.bisect_snd_length, h1]; ring
    · rw [BoundedInterval.bisect_fst_length, h1]; ring

/-- A nonempty box remains nonempty after subdivision -/
lemma subdivide_one_step_nonempty {d:ℕ} (B: Box d) (hB: B.toSet.Nonempty) :
    ∀ B' ∈ B.subdivide, B'.toSet.Nonempty := by
  intro B' hB'
  unfold subdivide at hB'
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hB'
  obtain ⟨choice, rfl⟩ := hB'
  -- The midpoint of B is in all sub-boxes
  use fun i => (B.side i).midpoint
  intro i _
  have h_side_nonempty : (B.side i).toSet.Nonempty := by
    obtain ⟨x, hx⟩ := hB
    exact ⟨x i, hx i (Set.mem_univ i)⟩
  simp only
  split_ifs with h
  · exact BoundedInterval.midpoint_mem_bisect_snd (B.side i) h_side_nonempty
  · exact BoundedInterval.midpoint_mem_bisect_fst (B.side i) h_side_nonempty

/-- A nonempty box remains nonempty after k iterations of subdivision -/
lemma subdivide_iter_nonempty {d:ℕ} (B: Box d) (hB: B.toSet.Nonempty) (k: ℕ) :
    ∀ B' ∈ subdivide_iter B k, B'.toSet.Nonempty := by
  induction k with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton]
    intro B' hB'; rw [hB']; exact hB
  | succ k ih =>
    intro B' hB'
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB''_mem, hB'_sub⟩ := hB'
    exact subdivide_one_step_nonempty B'' (ih B'' hB''_mem) B' hB'_sub

/-- Grid alignment: sides in subdivide_iter start at grid positions.
    Requires nonempty box to ensure sides have a ≤ b (backwards intervals break the formula). -/
lemma subdivide_iter_side_grid {d:ℕ} (B : Box d) (hB : B.toSet.Nonempty) (k : ℕ) (B' : Box d)
    (hB' : B' ∈ subdivide_iter B k) (i : Fin d) :
    ∃ j : ℕ, j < 2^k ∧ (B'.side i).a = (B.side i).a + j * (|B.side i|ₗ / 2^k) := by
  induction k generalizing B' with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton] at hB'
    use 0
    simp [hB']
  | succ k ih =>
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB'', hB'_sub⟩ := hB'
    obtain ⟨j'', hj''_bound, hj''_eq⟩ := ih B'' hB''
    simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hB'_sub
    obtain ⟨c, rfl⟩ := hB'_sub
    have h_len := subdivide_iter_side_length B k B'' hB'' i
    simp only
    split_ifs with hc
    · -- snd case: start at midpoint of B''
      use 2 * j'' + 1
      constructor
      · omega
      · -- (bisect.snd).a = midpoint = B''.a + |B''|ₗ/2
        rw [BoundedInterval.bisect_snd_a]
        have h_B''_len : |B''.side i|ₗ = |B.side i|ₗ / 2 ^ k := h_len
        by_cases h_nondeg : (B''.side i).a ≤ (B''.side i).b
        · -- Non-degenerate: use midpoint_eq_a_add_half_length
          rw [BoundedInterval.midpoint_eq_a_add_half_length _ h_nondeg, hj''_eq, h_B''_len]
          have h2k : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
          rw [h2k]
          have h2k_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
          field_simp [h2k_ne]
          ring
        · -- Degenerate case: impossible for nonempty boxes (all sides have a ≤ b)
          -- B'' is nonempty since B is nonempty
          have hB''_nonempty : B''.toSet.Nonempty := subdivide_iter_nonempty B hB k B'' hB''
          -- Therefore (B''.side i) is nonempty
          have h_side_nonempty : (B''.side i).toSet.Nonempty :=
            Box.side_nonempty_of_nonempty B'' hB''_nonempty i
          -- Nonempty intervals have a ≤ b
          have h_order : (B''.side i).a ≤ (B''.side i).b :=
            BoundedInterval.nonempty_implies_le _ h_side_nonempty
          -- Contradiction with ¬h_nondeg
          exact absurd h_order h_nondeg
    · -- fst case: start at B''.a (left endpoint preserved)
      use 2 * j''
      constructor
      · omega
      · rw [BoundedInterval.bisect_fst_a, hj''_eq]
        have h2k : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
        rw [h2k]
        have h2k_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
        field_simp [h2k_ne]
        ring

/-- Volume is preserved through iterative subdivision -/
lemma volume_subdivide_iter {d:ℕ} (B: Box d) (hB : B.toSet.Nonempty) (k: ℕ) :
    ∑ B' ∈ subdivide_iter B k, |B'|ᵥ = |B|ᵥ := by
  induction k with
  | zero => simp [subdivide_iter]
  | succ k ih =>
    simp only [subdivide_iter_succ]
    rw [Finset.sum_biUnion]
    · -- Each inner sum ∑ i ∈ x.subdivide, |i|ᵥ = |x|ᵥ by volume_subdivide
      calc ∑ x ∈ subdivide_iter B k, ∑ i ∈ x.subdivide, |i|ᵥ
          = ∑ x ∈ subdivide_iter B k, |x|ᵥ := by
            apply Finset.sum_congr rfl
            intro B' _
            exact volume_subdivide B'
        _ = |B|ᵥ := ih
    · -- Pairwise disjointness of subdivisions from different parent boxes
      intro B₁ hB₁ B₂ hB₂ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_iff_ne]
      intro s₁ hs₁ s₂ hs₂
      -- Extract choice functions from membership in subdivide
      simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hs₁ hs₂
      obtain ⟨c₁, rfl⟩ := hs₁
      obtain ⟨c₂, rfl⟩ := hs₂
      -- Suppose for contradiction that s₁ = s₂
      intro heq
      apply hne
      -- Show B₁ = B₂ using Box.ext
      ext i
      -- At coordinate i, the sides of s₁ and s₂ must be equal
      have h_side_eq : (if c₁ i then (B₁.side i).bisect.snd else (B₁.side i).bisect.fst) =
                       (if c₂ i then (B₂.side i).bisect.snd else (B₂.side i).bisect.fst) := by
        have := congrFun (congrArg Box.side heq) i
        simpa using this
      -- At level k ≥ 1, all sides are Icc. k = 0 case: subdivide_iter B 0 = {B}, so B₁ = B₂
      match k with
      | 0 =>
        -- subdivide_iter B 0 = {B}, so B₁ = B and B₂ = B
        have hB₁' : B₁ = B := by simpa [subdivide_iter] using hB₁
        have hB₂' : B₂ = B := by simpa [subdivide_iter] using hB₂
        simp [hB₁', hB₂']
      | k'+1 =>
      -- Get Icc structure for both sides
      obtain ⟨a₁, b₁, h_side₁⟩ := subdivide_iter_side_is_Icc B k' B₁ hB₁ i
      obtain ⟨a₂, b₂, h_side₂⟩ := subdivide_iter_side_is_Icc B k' B₂ hB₂ i
      -- Get grid positions for B₁.side i and B₂.side i
      obtain ⟨j₁, _, hj₁⟩ := subdivide_iter_side_grid B hB (k'+1) B₁ hB₁ i
      obtain ⟨j₂, _, hj₂⟩ := subdivide_iter_side_grid B hB (k'+1) B₂ hB₂ i
      -- Both have the same length
      have h_len₁ := subdivide_iter_side_length B (k'+1) B₁ hB₁ i
      have h_len₂ := subdivide_iter_side_length B (k'+1) B₂ hB₂ i
      have h_same_len : |B₁.side i|ₗ = |B₂.side i|ₗ := by rw [h_len₁, h_len₂]
      -- Case analysis on c₁ i and c₂ i
      cases hc₁ : c₁ i <;> cases hc₂ : c₂ i <;> simp only [hc₁, hc₂, ite_true] at h_side_eq
      · -- fst = fst case: endpoint equality implies parent equality
        obtain ⟨ha, hb⟩ := BoundedInterval.bisect_fst_eq_endpoints h_side_eq
        -- Both sides are Icc with same endpoints
        simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at ha hb ⊢
        simp [ha, hb]
      · -- fst = snd cross case: parity contradiction via grid positions
        -- Key insight: Grid positions are integers, but fst=snd requires half-integer offset
        -- For degenerate case (L=0): all intervals collapse, so B₁=B₂
        by_cases hL : |B.side i|ₗ = 0
        · -- Degenerate case: all sides at dimension i are singletons
          -- When length = 0 for nonempty box, a = b (singleton)
          -- All subdivisions have same singleton side
          have h1a : (B₁.side i).a = (B.side i).a := by rw [hj₁, hL]; simp
          have h2a : (B₂.side i).a = (B.side i).a := by rw [hj₂, hL]; simp
          have h1len : |B₁.side i|ₗ = 0 := by rw [h_len₁, hL]; simp
          have h2len : |B₂.side i|ₗ = 0 := by rw [h_len₂, hL]; simp
          -- For nonempty Icc intervals with length 0: a = b
          have hB1_nonempty : B₁.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₁ hB₁
          have hB2_nonempty : B₂.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₂ hB₂
          have h1b : (B₁.side i).b = (B₁.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₁ hB1_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            -- For Icc a b, length 0 with a ≤ b means a = b
            unfold BoundedInterval.length at h1len
            simp only [max_eq_right_iff] at h1len
            linarith
          have h2b : (B₂.side i).b = (B₂.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₂ hB2_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            unfold BoundedInterval.length at h2len
            simp only [max_eq_right_iff] at h2len
            linarith
          -- Both Icc intervals have same a and b, so they're equal
          simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at h1a h2a h1b h2b ⊢
          simp [h1a, h2a, h1b, h2b]
        · -- Non-degenerate case: derive parity contradiction
          -- From h_side_eq: bisect.fst of B₁ = bisect.snd of B₂
          -- So (B₁.side i).a = (B₂.side i).midpoint = (B₂.side i).a + |B₂.side i|ₗ/2
          have h_fst_a := BoundedInterval.bisect_fst_a (B₁.side i)
          have h_snd_a := BoundedInterval.bisect_snd_a (B₂.side i)
          have hB2_nonempty : B₂.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₂ hB₂
          have h_side2_nonempty := Box.side_nonempty_of_nonempty B₂ hB2_nonempty i
          have h_order2 := BoundedInterval.nonempty_implies_le _ h_side2_nonempty
          have h_mid := BoundedInterval.midpoint_eq_a_add_half_length (B₂.side i) h_order2
          -- From h_side_eq, left endpoints are equal
          have h_a_eq : (B₁.side i).bisect.fst.a = (B₂.side i).bisect.snd.a := congrArg (·.a) h_side_eq
          rw [h_fst_a, h_snd_a, h_mid] at h_a_eq
          -- Now we have: B₁.side i.a = B₂.side i.a + |B₂.side i|ₗ/2
          -- Substitute grid formulas
          rw [hj₁, hj₂, h_len₂] at h_a_eq
          -- j₁ * step = j₂ * step + step/2 where step = |B.side i|ₗ / 2^(k'+2)
          have hstep_pos : (0:ℝ) < |B.side i|ₗ / 2 ^ (k' + 2) := by
            apply div_pos
            · exact lt_of_le_of_ne (BoundedInterval.length_nonneg _) (Ne.symm hL)
            · positivity
          -- This gives j₁ = j₂ + 1/2, impossible for natural numbers
          -- Cancel (B.side i).a from both sides
          have h_cancel : j₁ * (|B.side i|ₗ / 2^(k'+1)) =
                          j₂ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) / 2 := by
            have := h_a_eq; linarith
          -- Multiply both sides by 2^(k'+2) / L to get: 2*j₁ = 2*j₂ + 1
          have h2k1_ne : (2:ℝ) ^ (k' + 1) ≠ 0 := by positivity
          have hL_pos : (0:ℝ) < |B.side i|ₗ := lt_of_le_of_ne (BoundedInterval.length_nonneg _) (Ne.symm hL)
          have hL_ne : |B.side i|ₗ ≠ 0 := hL
          have h_step_ne : |B.side i|ₗ / 2^(k'+1) ≠ 0 := by positivity
          have h_parity : (2 * j₁ : ℝ) = 2 * j₂ + 1 := by
            -- From h_cancel: j₁ * step = j₂ * step + step/2
            -- Multiply both sides by 2, then cancel step
            have h2 : 2 * (j₁ * (|B.side i|ₗ / 2^(k'+1))) =
                      2 * j₂ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) := by linarith
            have h3 : (|B.side i|ₗ / 2^(k'+1)) * (2 * j₁) = (|B.side i|ₗ / 2^(k'+1)) * (2 * j₂ + 1) := by
              ring_nf at h2 ⊢; linarith
            exact mul_left_cancel₀ h_step_ne h3
          -- 2*j₁ is even, 2*j₂+1 is odd: contradiction via omega
          have h_eq_nat : 2 * j₁ = 2 * j₂ + 1 := by
            have := h_parity
            norm_cast at this
          omega
      · -- snd = fst cross case: symmetric to fst = snd
        by_cases hL : |B.side i|ₗ = 0
        · -- Degenerate case: identical to fst = snd case
          have h1a : (B₁.side i).a = (B.side i).a := by rw [hj₁, hL]; simp
          have h2a : (B₂.side i).a = (B.side i).a := by rw [hj₂, hL]; simp
          have h1len : |B₁.side i|ₗ = 0 := by rw [h_len₁, hL]; simp
          have h2len : |B₂.side i|ₗ = 0 := by rw [h_len₂, hL]; simp
          have hB1_nonempty : B₁.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₁ hB₁
          have hB2_nonempty : B₂.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₂ hB₂
          have h1b : (B₁.side i).b = (B₁.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₁ hB1_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            unfold BoundedInterval.length at h1len
            simp only [max_eq_right_iff] at h1len
            linarith
          have h2b : (B₂.side i).b = (B₂.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₂ hB2_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            unfold BoundedInterval.length at h2len
            simp only [max_eq_right_iff] at h2len
            linarith
          simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at h1a h2a h1b h2b ⊢
          simp [h1a, h2a, h1b, h2b]
        · -- Non-degenerate case: derive parity contradiction (symmetric argument)
          -- From h_side_eq: bisect.snd of B₁ = bisect.fst of B₂
          -- So (B₁.side i).midpoint = (B₂.side i).a
          have h_snd_a := BoundedInterval.bisect_snd_a (B₁.side i)
          have h_fst_a := BoundedInterval.bisect_fst_a (B₂.side i)
          have hB1_nonempty : B₁.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₁ hB₁
          have h_side1_nonempty := Box.side_nonempty_of_nonempty B₁ hB1_nonempty i
          have h_order1 := BoundedInterval.nonempty_implies_le _ h_side1_nonempty
          have h_mid := BoundedInterval.midpoint_eq_a_add_half_length (B₁.side i) h_order1
          -- From h_side_eq, left endpoints are equal
          have h_a_eq : (B₁.side i).bisect.snd.a = (B₂.side i).bisect.fst.a := congrArg (·.a) h_side_eq
          rw [h_snd_a, h_fst_a, h_mid] at h_a_eq
          -- Now we have: B₁.side i.a + |B₁.side i|ₗ/2 = B₂.side i.a
          -- Substitute grid formulas
          rw [hj₁, hj₂, h_len₁] at h_a_eq
          -- This gives j₁ + 1/2 = j₂, impossible for natural numbers
          -- Cancel (B.side i).a from both sides
          have h_cancel : j₁ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) / 2 =
                          j₂ * (|B.side i|ₗ / 2^(k'+1)) := by
            have := h_a_eq; linarith
          -- Multiply both sides by 2^(k'+2) / L to get: 2*j₁ + 1 = 2*j₂
          have h2k1_ne : (2:ℝ) ^ (k' + 1) ≠ 0 := by positivity
          have hL_pos : (0:ℝ) < |B.side i|ₗ := lt_of_le_of_ne (BoundedInterval.length_nonneg _) (Ne.symm hL)
          have hL_ne : |B.side i|ₗ ≠ 0 := hL
          have h_step_ne : |B.side i|ₗ / 2^(k'+1) ≠ 0 := by positivity
          have h_parity : (2 * j₁ + 1 : ℝ) = 2 * j₂ := by
            -- From h_cancel: j₁ * step + step/2 = j₂ * step
            -- Multiply both sides by 2, then cancel step
            have h2 : 2 * j₁ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) =
                      2 * j₂ * (|B.side i|ₗ / 2^(k'+1)) := by linarith
            have h3 : (|B.side i|ₗ / 2^(k'+1)) * (2 * j₁ + 1) = (|B.side i|ₗ / 2^(k'+1)) * (2 * j₂) := by
              ring_nf at h2 ⊢; linarith
            exact mul_left_cancel₀ h_step_ne h3
          -- 2*j₁+1 is odd, 2*j₂ is even: contradiction via omega
          have h_eq_nat : 2 * j₁ + 1 = 2 * j₂ := by
            have := h_parity
            norm_cast at this
          omega
      · -- snd = snd case: endpoint equality implies parent equality
        obtain ⟨ha, hb⟩ := BoundedInterval.bisect_snd_eq_endpoints h_side_eq
        -- Both sides are Icc with same endpoints
        simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at ha hb ⊢
        simp [ha, hb]

/-- Diameter bound after k iterations of subdivision.
    Each iteration reduces diameter by factor of √2. -/
lemma diameter_subdivide_iter {d:ℕ} (B: Box d) (hB: B.toSet.Nonempty) (k: ℕ) :
    ∀ B' ∈ subdivide_iter B k, B'.diameter ≤ B.diameter / (Real.sqrt 2) ^ k := by
  induction k with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton, pow_zero, div_one]
    intro B' hB'; rw [hB']
  | succ k ih =>
    intro B' hB'
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB''_mem, hB'_sub⟩ := hB'
    -- B'' is in subdivide_iter B k, and B' is in B''.subdivide
    have hB''_diam := ih B'' hB''_mem
    -- Need: B'' is nonempty to apply subdivide_diameter_bound
    have hB''_nonempty : B''.toSet.Nonempty := subdivide_iter_nonempty B hB k B'' hB''_mem
    have hB'_diam := subdivide_diameter_bound B'' hB''_nonempty B' hB'_sub
    calc B'.diameter
        ≤ B''.diameter / Real.sqrt 2 := hB'_diam
      _ ≤ (B.diameter / (Real.sqrt 2) ^ k) / Real.sqrt 2 := by
          apply div_le_div_of_nonneg_right hB''_diam (Real.sqrt_nonneg 2)
      _ = B.diameter / ((Real.sqrt 2) ^ k * Real.sqrt 2) := by rw [div_div]
      _ = B.diameter / (Real.sqrt 2 * (Real.sqrt 2) ^ k) := by ring_nf
      _ = B.diameter / (Real.sqrt 2) ^ (k + 1) := by rw [pow_succ']

/-- Number of subdivisions needed to get diameter below threshold r.
    Each subdivision reduces diameter by factor of √2, so after k iterations:
    diameter ≤ original_diameter / (√2)^k
    We need (√2)^k > diameter/r, i.e., k > log(diameter/r) / log(√2) = 2·log₂(diameter/r). -/
noncomputable def iter_count {d:ℕ} (B: Box d) (r: ℝ) : ℕ :=
  if B.diameter ≤ 0 then 0
  else if B.diameter < r then 0
  else Nat.ceil (2 * Real.log (B.diameter / r) / Real.log 2) + 1

/-- After iter_count subdivisions, all sub-boxes have diameter < r -/
lemma diameter_lt_of_iter_count {d:ℕ} (B: Box d) (hB: B.toSet.Nonempty) (r: ℝ) (hr: 0 < r) :
    ∀ B' ∈ subdivide_iter B (B.iter_count r), B'.diameter < r := by
  intro B' hB'
  by_cases h_diam_le : B.diameter ≤ 0
  · -- Degenerate case: diameter ≤ 0 means all sub-boxes also have diameter ≤ 0 < r
    simp only [iter_count, h_diam_le, ↓reduceIte, subdivide_iter] at hB'
    simp only [Finset.mem_singleton] at hB'
    rw [hB']
    calc B.diameter ≤ 0 := h_diam_le
      _ < r := hr
  · push_neg at h_diam_le
    by_cases h_small : B.diameter < r
    · -- Already small enough, no subdivisions needed
      simp only [iter_count, not_le.mpr h_diam_le, h_small, ↓reduceIte, subdivide_iter] at hB'
      simp only [Finset.mem_singleton] at hB'
      rw [hB']; exact h_small
    · -- Need subdivisions: B.diameter ≥ r, so we use the logarithmic formula
      push_neg at h_small
      have h_iter_bound := diameter_subdivide_iter B hB (B.iter_count r) B' hB'
      -- Show that B.diameter / (√2)^k < r for k = iter_count
      -- Key: iter_count = ⌈2 * log(B.diameter / r) / log 2⌉ + 1
      -- So k > 2 * log₂(B.diameter / r), meaning (√2)^k > B.diameter / r
      calc B'.diameter
          ≤ B.diameter / (Real.sqrt 2) ^ (B.iter_count r) := h_iter_bound
        _ < r := by
            -- Need: B.diameter / (√2)^k < r, i.e., (√2)^k > B.diameter / r
            have h_k_def : B.iter_count r = Nat.ceil (2 * Real.log (B.diameter / r) / Real.log 2) + 1 := by
              simp only [iter_count, not_le.mpr h_diam_le, not_lt.mpr h_small, ↓reduceIte]
            -- Prove (√2)^k > B.diameter / r using the logarithmic definition
            have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
            have hsqrt2_pow_pos : 0 < (Real.sqrt 2) ^ (B.iter_count r) := pow_pos hsqrt2_pos _
            have hDr_pos : 0 < B.diameter / r := div_pos h_diam_le hr
            have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
            rw [div_lt_iff₀ hsqrt2_pow_pos]
            -- Goal: B.diameter < r * (√2)^k
            set L := 2 * Real.log (B.diameter / r) / Real.log 2 with hL_def
            -- k > L because k = ⌈L⌉ + 1 > L
            have hk_gt : ((B.iter_count r) : ℝ) > L := by
              have h_ceil_ge : (Nat.ceil L : ℝ) ≥ L := Nat.le_ceil L
              have hk_eq : ((B.iter_count r) : ℝ) = (Nat.ceil L : ℝ) + 1 := by
                simp only [h_k_def]; norm_cast
              linarith
            -- k/2 > log₂(B.diameter/r)
            have hL_eq : L = 2 * (Real.log (B.diameter / r) / Real.log 2) := by ring
            have hk_half_gt : ((B.iter_count r) : ℝ) / 2 > Real.log (B.diameter / r) / Real.log 2 := by
              have : ((B.iter_count r) : ℝ) > 2 * (Real.log (B.diameter / r) / Real.log 2) := by
                rw [← hL_eq]; exact hk_gt
              linarith
            -- (√2)^k = 2^(k/2)
            have hsqrt_pow : (Real.sqrt 2) ^ (B.iter_count r) =
                             (2 : ℝ) ^ (((B.iter_count r) : ℝ) / 2) := by
              have h1 : Real.sqrt 2 = (2 : ℝ) ^ ((1:ℝ) / 2) := Real.sqrt_eq_rpow 2
              conv_lhs => rw [h1]
              rw [← Real.rpow_natCast ((2:ℝ) ^ ((1:ℝ)/2)) (B.iter_count r)]
              rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
              congr 1; ring
            -- 2^(k/2) > B.diameter/r
            have h2pow_gt : (2 : ℝ) ^ (((B.iter_count r) : ℝ) / 2) > B.diameter / r := by
              rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
              have hsimp : Real.log (B.diameter / r) / Real.log 2 * Real.log 2 =
                          Real.log (B.diameter / r) := by field_simp
              have h_exp_ineq : Real.log 2 * (((B.iter_count r) : ℝ) / 2) >
                               Real.log (B.diameter / r) := by
                calc Real.log 2 * (((B.iter_count r) : ℝ) / 2)
                    = ((B.iter_count r) : ℝ) / 2 * Real.log 2 := by ring
                  _ > Real.log (B.diameter / r) / Real.log 2 * Real.log 2 := by
                       apply mul_lt_mul_of_pos_right hk_half_gt hlog2_pos
                  _ = Real.log (B.diameter / r) := hsimp
              calc Real.exp (Real.log 2 * (((B.iter_count r) : ℝ) / 2))
                  > Real.exp (Real.log (B.diameter / r)) := Real.exp_strictMono h_exp_ineq
                _ = B.diameter / r := Real.exp_log hDr_pos
            -- Combine
            rw [hsqrt_pow]
            calc B.diameter = (B.diameter / r) * r := by field_simp
              _ < (2 : ℝ) ^ (((B.iter_count r) : ℝ) / 2) * r := by
                  apply mul_lt_mul_of_pos_right h2pow_gt hr
              _ = r * (2 : ℝ) ^ (((B.iter_count r) : ℝ) / 2) := by ring

/-- Subdivided boxes cover the original box: any point in B.toSet is contained in
    some box in subdivide_iter B k. -/
lemma subdivide_iter_covers {d:ℕ} (B : Box d) (k : ℕ) (x : EuclideanSpace' d)
    (hx : x ∈ B.toSet) : ∃ B' ∈ subdivide_iter B k, x ∈ B'.toSet := by
  induction k with
  | zero =>
    refine ⟨B, ?_, hx⟩
    simp only [subdivide_iter_zero, Finset.mem_singleton]
  | succ k ih =>
    obtain ⟨B'', hB''_mem, hx_B''⟩ := ih
    -- B'' is subdivided, x is in B''.toSet, need to find B' ∈ B''.subdivide with x ∈ B'
    -- Define choice function: c i = true iff x i is in right half
    let c : Fin d → Bool := fun i => decide (x i ≥ (B''.side i).midpoint)
    -- The sub-box for this choice contains x
    let B' : Box d := {
      side := fun i => if c i then (B''.side i).bisect.snd else (B''.side i).bisect.fst
    }
    refine ⟨B', ?_, ?_⟩
    · -- B' ∈ subdivide_iter B (k+1)
      simp only [subdivide_iter_succ, Finset.mem_biUnion]
      exact ⟨B'', hB''_mem, by simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨c, rfl⟩⟩
    · -- x ∈ B'.toSet: for each i, x i is in the appropriate half
      intro i hi
      have hx_i : x i ∈ (B''.side i).toSet := by
        have := hx_B''
        simp only [toSet] at this
        exact this i (Set.mem_univ i)
      simp only [B']
      by_cases hm : x i ≥ (B''.side i).midpoint
      · have hc : c i = true := decide_eq_true hm
        simp only [hc, ite_true]
        exact (BoundedInterval.mem_bisect_snd_iff (B''.side i) (x i) hx_i).mpr hm
      · push_neg at hm
        have hc : c i = false := decide_eq_false (not_le.mpr hm)
        simp only [hc]
        exact (BoundedInterval.mem_bisect_fst_iff (B''.side i) (x i) hx_i).mpr (le_of_lt hm)

/-- Box volume is non-negative (product of non-negative interval lengths). -/
lemma volume_nonneg {d : ℕ} (B : Box d) : 0 ≤ B.volume := by
  unfold volume
  apply Finset.prod_nonneg
  intro i _
  unfold BoundedInterval.length
  exact le_max_right _ _

end Box

namespace Lebesgue_outer_measure

/-- Any ℕ-indexed cover gives an upper bound on outer measure.
    Follows directly from the infimum definition. -/
lemma le_of_nat_cover {d:ℕ} (hd: 0 < d) (E: Set (EuclideanSpace' d))
    (S : ℕ → Box d) (hcover : E ⊆ ⋃ n, (S n).toSet) :
    Lebesgue_outer_measure E ≤ ∑' n, (S n).volume.toEReal := by
  rw [Lebesgue_outer_measure_eq_nat_indexed hd]
  apply csInf_le
  · -- Show the set is bounded below by 0
    use 0
    intro v hv
    obtain ⟨S', _, rfl⟩ := hv
    apply tsum_nonneg
    intro n
    exact EReal.coe_nonneg.mpr (Box.volume_nonneg _)
  · -- S is in the set of covers
    exact ⟨S, hcover, rfl⟩

/-- Upper bound from finset-indexed cover: if a set is covered by ⋃ n, ⋃ B ∈ I n, B.toSet
    where each I n is a finite set of boxes, then the outer measure is bounded by the
    sum of volumes. -/
lemma le_of_finset_cover {d:ℕ} (hd: 0 < d) (E: Set (EuclideanSpace' d))
    (I : ℕ → Finset (Box d)) (hcover : E ⊆ ⋃ n, ⋃ B ∈ I n, B.toSet) :
    Lebesgue_outer_measure E ≤ ∑' n, (∑ B ∈ I n, B.volume).toEReal := by
  -- Strategy: Enumerate boxes from all finsets into a single ℕ-indexed sequence,
  -- then apply le_of_nat_cover.
  --
  -- Key steps:
  -- 1. The sigma type (n : ℕ) × (I n) is countable (sigma of ℕ and finite sets)
  -- 2. Enumerate it as S : ℕ → Box d (padding with zero-volume boxes when needed)
  -- 3. Coverage is preserved: E ⊆ ⋃ m, (S m).toSet
  -- 4. Volume sum is preserved: ∑' m, (S m).volume = ∑' n, (∑ B ∈ I n, B.volume)
  --    (uses tsum_sigma' and the fact that zero-volume padding contributes nothing)
  sorry


/-- For any set with finite outer measure, we can find a cover whose volume is within ε of the outer measure.
    This follows from the definition of outer measure as an infimum. -/
lemma exists_cover_close {d:ℕ} (hd: 0 < d)
    (E: Set (EuclideanSpace' d)) (ε: ℝ) (hε: 0 < ε)
    (h_finite: Lebesgue_outer_measure E ≠ ⊤) :
    ∃ (S: ℕ → Box d), E ⊆ ⋃ n, (S n).toSet ∧
      ∑' n, (S n).volume.toEReal ≤ Lebesgue_outer_measure E + ε := by
  -- Use the ℕ-indexed characterization of outer measure
  rw [Lebesgue_outer_measure_eq_nat_indexed hd] at h_finite ⊢

  -- Key fact: inf + ε is not a lower bound (since ε > 0)
  -- Therefore, there exists some cover with volume < inf + ε, which implies ≤ inf + ε

  have h_not_lb : ¬ IsGLB (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) ''
      { S | E ⊆ ⋃ n, (S n).toSet }) (sInf (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) ''
      { S | E ⊆ ⋃ n, (S n).toSet }) + (ε : EReal)) := by
    intro h_glb
    -- If inf + ε were the GLB, then inf ≤ inf + ε ≤ inf (since inf is also a lower bound)
    -- This would imply ε ≤ 0, contradiction
    let img_set := ((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet }
    let inf_val := sInf img_set
    -- sInf img_set is the GLB of img_set
    have h_inf_glb : IsGLB img_set inf_val := isGLB_sInf img_set
    -- From h_glb, we have that inf_val + ε is also a GLB
    -- But GLB is unique, so if both are GLBs, they must be equal
    -- However, inf_val < inf_val + ε (since ε > 0 and inf_val ≠ ⊥ and inf_val ≠ ⊤)
    -- inf_val is an infimum of box volumes (sums of volumes), which are non-negative, so inf_val ≠ ⊥
    have h_ne_bot : inf_val ≠ ⊥ := by
      intro h_eq
      -- If inf_val = ⊥, then ⊥ is the GLB of img_set
      have h_glb_bot : IsGLB img_set ⊥ := by rwa [← h_eq]
      -- But 0 is a lower bound of img_set (since all box volumes are non-negative)
      have h_zero_lb : (0 : EReal) ∈ lowerBounds img_set := by
        intro v hv
        obtain ⟨S, _, rfl⟩ := hv
        -- v = ∑' n, (S n).volume.toEReal, and each term is ≥ 0
        apply tsum_nonneg
        intro n
        exact EReal.coe_nonneg.mpr (by
          unfold Box.volume
          apply Finset.prod_nonneg
          intro i _
          unfold BoundedInterval.length
          exact le_max_right _ _)
      -- Since ⊥ is the GLB, we have 0 ≤ ⊥ (as 0 is a lower bound)
      have : (0 : EReal) ≤ ⊥ := h_glb_bot.2 h_zero_lb
      -- But 0 > ⊥ in EReal
      exact not_le.mpr EReal.bot_lt_zero this
    have h_lt : inf_val < inf_val + (ε : EReal) := EReal.lt_add_of_pos_coe hε h_ne_bot h_finite
    -- GLB is unique: if both x and y are GLBs of the same set, then x = y
    have h_eq : inf_val = inf_val + (ε : EReal) := h_inf_glb.unique h_glb
    -- But inf_val < inf_val + ε, contradicting h_eq
    rw [← h_eq] at h_lt
    simp at h_lt

  -- Since sInf is the infimum and sInf + ε is not a lower bound,
  -- there must exist some cover with volume ≤ sInf + ε
  let img_set := ((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet }
  let inf_val := sInf img_set
  -- From h_not_lb, inf_val + ε is not a GLB, which means it's not a lower bound
  -- (since if it were a lower bound ≥ inf_val, it would have to equal inf_val to be a GLB)
  -- So there exists some element in img_set that is < inf_val + ε
  have h_exists_lt : ∃ v ∈ img_set, v < inf_val + (ε : EReal) := by
    -- If no such element existed, then inf_val + ε would be a lower bound
    by_contra h_not_exists
    push_neg at h_not_exists
    -- h_not_exists says: ∀ v ∈ img_set, inf_val + ε ≤ v
    -- This means inf_val + ε is a lower bound
    have h_is_lb : inf_val + (ε : EReal) ∈ lowerBounds img_set := by
      intro v hv
      exact h_not_exists v hv
    -- And since inf_val is the GLB (greatest lower bound), we have inf_val + ε ≤ inf_val
    have h_inf_glb : IsGLB img_set inf_val := isGLB_sInf img_set
    have h_le : inf_val + (ε : EReal) ≤ inf_val := h_inf_glb.2 h_is_lb
    -- But we also have inf_val < inf_val + ε (since ε > 0, inf_val ≠ ⊥, and inf_val ≠ ⊤)
    -- inf_val is an infimum of box volumes, which are non-negative, so inf_val ≠ ⊥
    have h_ne_bot : inf_val ≠ ⊥ := by
      intro h_eq
      have h_glb_bot : IsGLB img_set ⊥ := by rwa [← h_eq]
      have h_zero_lb : (0 : EReal) ∈ lowerBounds img_set := by
        intro v hv
        obtain ⟨S, _, rfl⟩ := hv
        apply tsum_nonneg
        intro n
        exact EReal.coe_nonneg.mpr (by
          unfold Box.volume
          apply Finset.prod_nonneg
          intro i _
          unfold BoundedInterval.length
          exact le_max_right _ _)
      have : (0 : EReal) ≤ ⊥ := h_glb_bot.2 h_zero_lb
      exact not_le.mpr EReal.bot_lt_zero this
    have h_lt : inf_val < inf_val + (ε : EReal) := EReal.lt_add_of_pos_coe hε h_ne_bot h_finite
    -- Contradiction: h_le says inf_val + ε ≤ inf_val, but h_lt says inf_val < inf_val + ε
    have : inf_val < inf_val := calc inf_val
        < inf_val + ↑ε := h_lt
      _ ≤ inf_val := h_le
    exact lt_irrefl _ this
  -- Extract the witness from the image set
  obtain ⟨v, ⟨S, hS_cover, rfl⟩, hv_lt⟩ := h_exists_lt
  -- S is our witness cover
  exact ⟨S, hS_cover, le_of_lt hv_lt⟩


/-- The set of indices of boxes that intersect a given set E -/
def intersecting_indices {d:ℕ} (S: ℕ → Box d) (E: Set (EuclideanSpace' d)) : Set ℕ :=
  { n | ((S n).toSet ∩ E).Nonempty }

/-- If all boxes have diameter less than dist(E,F), then the sets of indices intersecting
    E and F are disjoint. This follows from Box.not_intersects_both_of_diameter_lt. -/
lemma partition_disjoint {d:ℕ} {E F: Set (EuclideanSpace' d)} (S: ℕ → Box d)
    (_h_sep: 0 < set_dist E F) (h_diam: ∀ n, (S n).diameter < set_dist E F) :
    Disjoint (intersecting_indices S E) (intersecting_indices S F) := by
  rw [Set.disjoint_iff]
  intro n ⟨hE, hF⟩
  -- Box n intersects both E and F
  unfold intersecting_indices at hE hF
  simp at hE hF
  -- But diameter of box n < dist(E,F)
  have h_diam_n := h_diam n
  -- This contradicts Box.not_intersects_both_of_diameter_lt
  have := Box.not_intersects_both_of_diameter_lt (S n) E F h_diam_n
  exact this ⟨hE, hF⟩

end Lebesgue_outer_measure

/-- Helper: Coercion from ENNReal to EReal preserves summability.
    All ENNReal sequences are summable, and their coercions to EReal are also summable. -/
lemma Summable.coe_ennreal {α : Type*} {f : α → ENNReal} :
    Summable (fun x => ↑(f x) : α → EReal) := by
  -- All ENNReal sequences are summable
  have h_sum : Summable f := ENNReal.summable
  -- Get the HasSum for the original sequence
  have h_has_sum : HasSum f (∑' x, f x) := h_sum.hasSum
  -- The coercion preserves addition: ↑(x + y) = ↑x + ↑y
  have h_add : ∀ x y : ENNReal, (↑(x + y) : EReal) = (↑x : EReal) + (↑y : EReal) := EReal.coe_ennreal_add
  -- Construct an AddMonoidHom from the coercion
  -- Note: We need to show the coercion is an additive monoid homomorphism
  let φ : ENNReal →+ EReal := {
    toFun := fun x => (↑x : EReal)
    map_zero' := by simp
    map_add' := h_add
  }
  -- Coercion is continuous
  have h_cont : Continuous φ := continuous_coe_ennreal_ereal
  -- Apply HasSum.map to show the coerced sequence has a sum
  have h_has_sum_coe : HasSum (fun x => ↑(f x) : α → EReal) ↑(∑' x, f x) :=
    h_has_sum.map φ h_cont
  -- Summable follows from HasSum
  exact h_has_sum_coe.summable

/-- Helper: Addition of tsums of ENNReal values coerced to EReal.
    (∑' n, ↑(a n) : EReal) + (∑' n, ↑(b n) : EReal) = (∑' n, ↑(a n + b n) : EReal)

    This follows from ENNReal.tsum_add and the fact that coercion commutes with addition. -/
lemma EReal.tsum_add_coe_ennreal {α : Type*} {a b : α → ENNReal} :
    (∑' n, ↑(a n) : EReal) + (∑' n, ↑(b n) : EReal) = (∑' n, ↑(a n + b n) : EReal) := by
  -- Use ENNReal.tsum_add: ∑' n, (a n + b n) = ∑' n, a n + ∑' n, b n
  have h_tsum_add : (∑' n, (a n + b n) : ENNReal) = (∑' n, a n : ENNReal) + (∑' n, b n : ENNReal) := by
    rw [ENNReal.tsum_add]
  -- Coerce both sides: ↑(∑' n, a n + b n) = ↑(∑' n, a n) + ↑(∑' n, b n)
  -- Use Summable.map_tsum: continuous additive maps commute with tsum
  -- All ENNReal sequences are summable
  have h_sum_a : Summable a := ENNReal.summable
  have h_sum_b : Summable b := ENNReal.summable
  have h_sum_ab : Summable (fun n => a n + b n) := ENNReal.summable
  -- Construct the AddMonoidHom from ENNReal to EReal (same as in Summable.coe_ennreal)
  have h_add : ∀ x y : ENNReal, (↑(x + y) : EReal) = (↑x : EReal) + (↑y : EReal) := EReal.coe_ennreal_add
  let φ : ENNReal →+ EReal := {
    toFun := fun x => (↑x : EReal)
    map_zero' := by simp
    map_add' := h_add
  }
  have h_cont : Continuous φ := continuous_coe_ennreal_ereal
  -- Apply Summable.map_tsum to show coercion commutes with tsum
  have h_coe_tsum_a : (∑' n, ↑(a n) : EReal) = ↑(∑' n, a n : ENNReal) := by
    exact (Summable.map_tsum h_sum_a φ h_cont).symm
  have h_coe_tsum_b : (∑' n, ↑(b n) : EReal) = ↑(∑' n, b n : ENNReal) := by
    exact (Summable.map_tsum h_sum_b φ h_cont).symm
  have h_coe_tsum_sum : (∑' n, ↑(a n + b n) : EReal) = ↑(∑' n, (a n + b n) : ENNReal) := by
    exact (Summable.map_tsum h_sum_ab φ h_cont).symm
  rw [h_coe_tsum_a, h_coe_tsum_b, h_coe_tsum_sum]
  rw [← EReal.coe_ennreal_add]
  congr 1
  exact h_tsum_add.symm

/-- Helper: For non-negative real sequences, tsum addition inequality in EReal.
    If f n + g n ≤ h n pointwise, then ∑' f.toEReal + ∑' g.toEReal ≤ ∑' h.toEReal. -/
lemma EReal.tsum_add_le_of_nonneg_pointwise {f g h : ℕ → ℝ}
    (hf_nn : ∀ n, 0 ≤ f n) (hg_nn : ∀ n, 0 ≤ g n)
    (h_pw : ∀ n, f n + g n ≤ h n) :
    (∑' n, (f n).toEReal) + (∑' n, (g n).toEReal) ≤ ∑' n, (h n).toEReal := by
  -- Convert to ENNReal where we have better tsum properties
  -- For non-negative reals, x.toEReal = (ENNReal.ofReal x : EReal)
  have hf_eq : ∀ n, (f n).toEReal = (ENNReal.ofReal (f n) : EReal) := by
    intro n; simp [EReal.coe_ennreal_ofReal, max_eq_left (hf_nn n)]
  have hg_eq : ∀ n, (g n).toEReal = (ENNReal.ofReal (g n) : EReal) := by
    intro n; simp [EReal.coe_ennreal_ofReal, max_eq_left (hg_nn n)]
  have hh_eq : ∀ n, (h n).toEReal = (ENNReal.ofReal (h n) : EReal) := by
    intro n; simp [EReal.coe_ennreal_ofReal, max_eq_left (le_trans (add_nonneg (hf_nn n) (hg_nn n)) (h_pw n))]

  -- Rewrite using these equalities
  simp_rw [hf_eq, hg_eq, hh_eq]

  -- Need to show: (∑' n, ↑(ENNReal.ofReal (f n)) : EReal) + (∑' n, ↑(ENNReal.ofReal (g n)) : EReal)
  --            ≤ (∑' n, ↑(ENNReal.ofReal (h n)) : EReal)
  -- Use helper lemma to combine sums
  let a : ℕ → ENNReal := fun n => ENNReal.ofReal (f n)
  let b : ℕ → ENNReal := fun n => ENNReal.ofReal (g n)
  let c : ℕ → ENNReal := fun n => ENNReal.ofReal (h n)

  -- Combine the sums on LHS using helper lemma
  have h_combine : (∑' n, ↑(a n) : EReal) + (∑' n, ↑(b n) : EReal) = (∑' n, ↑(a n + b n) : EReal) := by
    exact EReal.tsum_add_coe_ennreal
  -- Expand a and b in the goal to match h_combine
  simp only [a, b] at *
  -- Rewrite LHS to combined form
  rw [h_combine]

  -- Now need: (∑' n, ↑(ENNReal.ofReal (f n) + ENNReal.ofReal (g n)) : EReal)
  --         ≤ (∑' n, ↑(ENNReal.ofReal (h n)) : EReal)
  have h_sum_lhs : Summable (fun n => ↑(ENNReal.ofReal (f n) + ENNReal.ofReal (g n)) : ℕ → EReal) :=
    Summable.coe_ennreal
  have h_sum_rhs : Summable (fun n => ↑(ENNReal.ofReal (h n)) : ℕ → EReal) :=
    Summable.coe_ennreal
  refine Summable.tsum_le_tsum (fun n => ?_) h_sum_lhs h_sum_rhs
  -- Pointwise inequality: ↑(ofReal (f n) + ofReal (g n)) ≤ ↑(ofReal (h n))
  rw [EReal.coe_ennreal_le_coe_ennreal_iff]
  have h_add_eq : ENNReal.ofReal (f n) + ENNReal.ofReal (g n) = ENNReal.ofReal (f n + g n) := by
    rw [ENNReal.ofReal_add (hf_nn n) (hg_nn n)]
  rw [h_add_eq]
  exact ENNReal.ofReal_le_ofReal (h_pw n)



/-- For disjoint subsets I_E, I_F of ℕ and a non-negative function f : ℕ → ℝ,
     the sum of tsums over the disjoint sets is at most the tsum over all of ℕ. -/
lemma tsum_add_tsum_le_of_disjoint_nonneg {I_E I_F : Set ℕ} (h_disj : Disjoint I_E I_F)
    (f : ℕ → ℝ) (hf_nonneg : ∀ n, 0 ≤ f n) :
    (∑' (n : I_E), (f n).toEReal) + (∑' (n : I_F), (f n).toEReal) ≤ ∑' n, (f n).toEReal := by
  -- Convert to ENNReal where we have nice lemmas
  let g : ℕ → ENNReal := fun n => (f n).toNNReal

  -- All ENNReal sequences are summable, including over subtypes
  have h_sum_E : Summable (fun n : I_E => g n.val) := ENNReal.summable
  have h_sum_F : Summable (fun n : I_F => g n.val) := ENNReal.summable
  have h_sum_all : Summable g := ENNReal.summable

  -- Use Summable.tsum_union_disjoint in ENNReal: ∑' (n : I_E ∪ I_F), g n = ∑' (n : I_E), g n + ∑' (n : I_F), g n
  let I_union : Set ℕ := I_E ∪ I_F
  have h_union_eq : (∑' (n : I_union), g n.val : ENNReal) =
      (∑' (n : I_E), g n.val : ENNReal) + (∑' (n : I_F), g n.val : ENNReal) := by
    exact Summable.tsum_union_disjoint h_disj h_sum_E h_sum_F

  -- Use monotonicity: ∑' (n : I_E ∪ I_F), g n ≤ ∑' n, g n
  -- This follows from the fact that I_union ⊆ Set.univ
  have h_mono : (∑' (n : I_union), g n.val : ENNReal) ≤ (∑' n, g n : ENNReal) := by
    -- Use ENNReal.tsum_mono_subtype with I_union ⊆ Set.univ, then collapse tsum over Set.univ
    rw [← tsum_univ g]
    exact ENNReal.tsum_mono_subtype g (Set.subset_univ I_union)

  -- Combine: ∑' I_E + ∑' I_F = ∑' (I_E ∪ I_F) ≤ ∑' ℕ in ENNReal
  have h_ineq_ennreal : (∑' (n : I_E), g n.val : ENNReal) + (∑' (n : I_F), g n.val : ENNReal) ≤
      (∑' n, g n : ENNReal) := by
    rw [← h_union_eq]
    exact h_mono

  -- Convert back to EReal using Summable.map_tsum
  -- Construct the AddMonoidHom from ENNReal to EReal
  have h_add : ∀ x y : ENNReal, (↑(x + y) : EReal) = (↑x : EReal) + (↑y : EReal) := EReal.coe_ennreal_add
  let φ : ENNReal →+ EReal := {
    toFun := fun x => (↑x : EReal)
    map_zero' := by simp
    map_add' := h_add
  }
  have h_cont : Continuous φ := continuous_coe_ennreal_ereal

  -- Key: pointwise equality (f n).toEReal = ↑(g n : ENNReal) for non-negative f n
  have h_pw : ∀ n, (f n).toEReal = ↑(g n : ENNReal) := by
    intro n
    simp only [g]
    -- (f n).toNNReal : NNReal coerces to ENNReal as ENNReal.ofReal (f n)
    have h1 : ((f n).toNNReal : ENNReal) = ENNReal.ofReal (f n) := rfl
    rw [h1, EReal.coe_ennreal_ofReal, max_eq_left (hf_nonneg n)]

  -- Convert each tsum: (∑' (n : I_E), (f n).toEReal) = ↑(∑' (n : I_E), g n.val)
  have h_coe_E : (∑' (n : I_E), (f n).toEReal) = ↑(∑' (n : I_E), g n.val : ENNReal) := by
    simp_rw [h_pw]
    exact (Summable.map_tsum h_sum_E φ h_cont).symm

  have h_coe_F : (∑' (n : I_F), (f n).toEReal) = ↑(∑' (n : I_F), g n.val : ENNReal) := by
    simp_rw [h_pw]
    exact (Summable.map_tsum h_sum_F φ h_cont).symm

  have h_coe_all : (∑' n, (f n).toEReal) = ↑(∑' n, g n : ENNReal) := by
    simp_rw [h_pw]
    exact (Summable.map_tsum h_sum_all φ h_cont).symm

  -- Apply the inequality in EReal
  rw [h_coe_E, h_coe_F, h_coe_all]
  -- Need: ↑(∑' I_E) + ↑(∑' I_F) ≤ ↑(∑' ℕ)
  -- Use EReal.coe_ennreal_le_coe_ennreal_iff and the ENNReal inequality
  rw [← EReal.coe_ennreal_add]
  rw [EReal.coe_ennreal_le_coe_ennreal_iff]
  exact h_ineq_ennreal

-- ========================================================================
-- End of Helpers for lemma 1.2.5
-- ========================================================================

/-- Lemma 1.2.5 (Finite additivity for separated sets).
    If E and F are separated (dist(E,F) > 0), then m*(E ∪ F) = m*(E) + m*(F).

    Proof strategy (from textbook):
    1. Direction ≤: Use subadditivity
    2. Direction ≥: Show m*(E ∪ F) ≥ m*(E) + m*(F)
       - If m*(E ∪ F) = ⊤, trivial
       - If m*(E ∪ F) < ⊤:
         * Get epsilon-close cover of E ∪ F
         * Refine cover so all boxes have diameter < dist(E,F)
         * Partition boxes into E-intersecting and F-intersecting (disjoint by geometric separation)
         * Sum volumes separately: m*(E) + m*(F) ≤ sum of refined cover ≤ m*(E ∪ F) + ε
         * Take ε → 0 to conclude
-/
theorem Lebesgue_outer_measure.union_of_separated {d:ℕ} (hd: 0 < d) {E F : Set (EuclideanSpace' d)}
    (hsep: set_dist E F > 0) :
    Lebesgue_outer_measure (E ∪ F) = Lebesgue_outer_measure E + Lebesgue_outer_measure F := by

  -- Direction 1: m*(E ∪ F) ≤ m*(E) + m*(F) [Subadditivity]
  have h_le : Lebesgue_outer_measure (E ∪ F) ≤ Lebesgue_outer_measure E + Lebesgue_outer_measure F := by
    -- Use finite_union_le for two sets
    let E' : Fin 2 → Set (EuclideanSpace' d) := ![E, F]
    have h_union : E ∪ F = ⋃ i, E' i := by
      simp only [E']
      ext x
      simp only [Set.mem_union, Set.mem_iUnion]
      constructor
      · intro hx
        cases hx with
        | inl hE => exact ⟨0, hE⟩
        | inr hF => exact ⟨1, hF⟩
      · intro ⟨i, hi⟩
        fin_cases i
        · left; exact hi
        · right; exact hi
    have h_sum : ∑ i : Fin 2, Lebesgue_outer_measure (E' i) =
        Lebesgue_outer_measure E + Lebesgue_outer_measure F := by
      simp only [Fin.sum_univ_two, E', Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h_union, ← h_sum]
    exact finite_union_le E'

  -- Direction 2: m*(E ∪ F) ≥ m*(E) + m*(F) [MAIN WORK]
  have h_ge : Lebesgue_outer_measure E + Lebesgue_outer_measure F ≤ Lebesgue_outer_measure (E ∪ F) := by
    -- Case 1: If m*(E ∪ F) = ⊤, then the inequality holds trivially
    by_cases h_inf : Lebesgue_outer_measure (E ∪ F) = ⊤
    · simp [h_inf]

    -- Case 2: m*(E ∪ F) < ⊤
    · -- For any ε > 0, we'll show m*(E) + m*(F) ≤ m*(E ∪ F) + ε
      -- Taking ε → 0 gives the result

      -- Proof: Show that for all ε > 0, m*(E) + m*(F) ≤ m*(E ∪ F) + ε
      -- This implies m*(E) + m*(F) ≤ m*(E ∪ F)
      have h_eps : ∀ (ε : ℝ), 0 < ε → Lebesgue_outer_measure E + Lebesgue_outer_measure F ≤
          Lebesgue_outer_measure (E ∪ F) + (ε : EReal) := by
        intro ε hε_real

        -- Get epsilon-close cover of E ∪ F
        have ⟨S, hS_cover, hS_vol⟩ := exists_cover_close hd (E ∪ F) ε hε_real h_inf

        -- Choose r with 0 < r < dist(E,F)
        have hr : ∃ r, 0 < r ∧ r < set_dist E F := by
          use set_dist E F / 2
          constructor
          · linarith
          · linarith
        obtain ⟨r, hr_pos, hr_lt⟩ := hr

        -- For each box S(n), subdivide k(n) = (S n).iter_count r times
        let k : ℕ → ℕ := fun n => (S n).iter_count r

        -- All refined boxes have diameter < r < set_dist E F
        have h_diam : ∀ n, ∀ B' ∈ Box.subdivide_iter (S n) (k n), B'.diameter < r := by
          intro n B' hB'
          by_cases hnonempty : (S n).toSet.Nonempty
          · exact Box.diameter_lt_of_iter_count (S n) hnonempty r hr_pos B' hB'
          · -- Empty box case: iter_count = 0 when diameter ≤ 0, so subdivide_iter = {S n}
            have h_empty : (S n).toSet = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
            have h_diam_zero : (S n).diameter = 0 := Box.diameter_of_empty (S n) h_empty
            -- iter_count = 0 since diameter = 0 ≤ 0
            have h_k_zero : k n = 0 := by
              simp only [k, Box.iter_count, h_diam_zero, le_refl, ↓reduceIte]
            -- So subdivide_iter (S n) 0 = {S n}, meaning B' = S n
            rw [h_k_zero, Box.subdivide_iter_zero, Finset.mem_singleton] at hB'
            rw [hB', h_diam_zero]
            exact hr_pos

        -- Partition: for each n, split subdivisions into E-intersecting and F-intersecting
        -- Use classical decidability for the filter predicate
        haveI : ∀ (B' : Box d), Decidable ((B'.toSet ∩ E).Nonempty) := fun _ => Classical.dec _
        haveI : ∀ (B' : Box d), Decidable ((B'.toSet ∩ F).Nonempty) := fun _ => Classical.dec _
        let I_E_n : ℕ → Finset (Box d) := fun n =>
          (Box.subdivide_iter (S n) (k n)).filter (fun B' => (B'.toSet ∩ E).Nonempty)
        let I_F_n : ℕ → Finset (Box d) := fun n =>
          (Box.subdivide_iter (S n) (k n)).filter (fun B' => (B'.toSet ∩ F).Nonempty)

        -- Disjointness at each level n: no box intersects both E and F
        have h_disj_n : ∀ n, Disjoint (I_E_n n) (I_F_n n) := by
          intro n
          rw [Finset.disjoint_filter]
          intro B' hB'_sub hB'_E hB'_F
          -- B' intersects both E and F, but diameter < r < set_dist E F: contradiction
          have h_small : B'.diameter < set_dist E F := by
            calc B'.diameter < r := h_diam n B' hB'_sub
            _ < set_dist E F := hr_lt
          exact Box.not_intersects_both_of_diameter_lt B' E F h_small ⟨hB'_E, hB'_F⟩

        -- E is covered by the E-intersecting subdivisions
        have hE_cover : E ⊆ ⋃ n, ⋃ B' ∈ I_E_n n, B'.toSet := by
          intro x hxE
          have hx_union : x ∈ E ∪ F := Set.mem_union_left F hxE
          obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hS_cover hx_union)
          obtain ⟨B', hB'_mem, hx_B'⟩ := Box.subdivide_iter_covers (S n) (k n) x hn
          have hB'_in_IE : B' ∈ I_E_n n := by
            rw [Finset.mem_filter]
            exact ⟨hB'_mem, ⟨x, hx_B', hxE⟩⟩
          simp only [Set.mem_iUnion]
          exact ⟨n, ⟨B', ⟨hB'_in_IE, hx_B'⟩⟩⟩

        -- F is covered by the F-intersecting subdivisions
        have hF_cover : F ⊆ ⋃ n, ⋃ B' ∈ I_F_n n, B'.toSet := by
          intro x hxF
          have hx_union : x ∈ E ∪ F := Set.mem_union_right E hxF
          obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hS_cover hx_union)
          obtain ⟨B', hB'_mem, hx_B'⟩ := Box.subdivide_iter_covers (S n) (k n) x hn
          have hB'_in_IF : B' ∈ I_F_n n := by
            rw [Finset.mem_filter]
            exact ⟨hB'_mem, ⟨x, hx_B', hxF⟩⟩
          simp only [Set.mem_iUnion]
          exact ⟨n, ⟨B', ⟨hB'_in_IF, hx_B'⟩⟩⟩

        -- Volume bounds: m*(E) ≤ sum over E-intersecting boxes
        have hE_bound : Lebesgue_outer_measure E ≤ ∑' n, (∑ B' ∈ I_E_n n, B'.volume).toEReal :=
          le_of_finset_cover hd E I_E_n hE_cover

        have hF_bound : Lebesgue_outer_measure F ≤ ∑' n, (∑ B' ∈ I_F_n n, B'.volume).toEReal :=
          le_of_finset_cover hd F I_F_n hF_cover

        -- Key: disjoint partition means ∑ I_E_n + ∑ I_F_n ≤ ∑ all subdivisions
        have h_sum_le : ∀ n, (∑ B' ∈ I_E_n n, B'.volume) + (∑ B' ∈ I_F_n n, B'.volume)
            ≤ ∑ B' ∈ Box.subdivide_iter (S n) (k n), B'.volume := by
          intro n
          -- Step 1: ∑ A + ∑ B = ∑ (A ∪ B) for disjoint sets
          rw [← Finset.sum_union (h_disj_n n)]
          -- Step 2: A ∪ B ⊆ subdivide_iter since both are filters of it
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · -- Union of filters ⊆ original set
            intro B' hB'
            rw [Finset.mem_union] at hB'
            cases hB' with
            | inl h => exact Finset.filter_subset _ _ h
            | inr h => exact Finset.filter_subset _ _ h
          · -- Volumes are non-negative
            intro B' _ _
            unfold Box.volume
            apply Finset.prod_nonneg
            intro i _
            unfold BoundedInterval.length
            exact le_max_right _ _

        -- Volume equality: sum over subdivisions = original volume
        have h_vol_eq : ∀ n, (S n).toSet.Nonempty →
            (∑ B' ∈ Box.subdivide_iter (S n) (k n), B'.volume) = (S n).volume := by
          intro n hn
          exact Box.volume_subdivide_iter (S n) hn (k n)

        -- Final calculation: combine bounds
        calc Lebesgue_outer_measure E + Lebesgue_outer_measure F
            ≤ (∑' n, (∑ B' ∈ I_E_n n, B'.volume).toEReal) +
              (∑' n, (∑ B' ∈ I_F_n n, B'.volume).toEReal) :=
                add_le_add hE_bound hF_bound
          _ ≤ ∑' n, (S n).volume.toEReal := by
              -- Convert to ENNReal where we have better tsum properties
              -- Key fact: for non-negative reals, x.toEReal = (x.toNNReal : ENNReal).toEReal
              -- Step 1: Show pointwise (∑ I_E_n) + (∑ I_F_n) ≤ vol(S n)
              have h_pw_le : ∀ n, (∑ B' ∈ I_E_n n, B'.volume) + (∑ B' ∈ I_F_n n, B'.volume) ≤ (S n).volume := by
                intro n
                calc (∑ B' ∈ I_E_n n, B'.volume) + (∑ B' ∈ I_F_n n, B'.volume)
                    ≤ ∑ B' ∈ Box.subdivide_iter (S n) (k n), B'.volume := h_sum_le n
                  _ ≤ (S n).volume := by
                    by_cases hn : (S n).toSet.Nonempty
                    · exact le_of_eq (h_vol_eq n hn)
                    · -- Empty box: volume = 0, and sum over subdivisions ≤ 0 = vol
                      have hempty : (S n).toSet = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
                      have hvol_zero : (S n).volume = 0 := Box.volume_eq_zero_of_empty (S n) hempty
                      rw [hvol_zero]
                      -- subdivide_iter of empty box = {S n} with volume 0
                      have hk_zero : k n = 0 := by
                        simp only [k, Box.iter_count]
                        have hdiam : (S n).diameter = 0 := Box.diameter_of_empty (S n) hempty
                        simp only [hdiam, le_refl, ↓reduceIte]
                      rw [hk_zero, Box.subdivide_iter_zero, Finset.sum_singleton, hvol_zero]

              -- Step 2: Apply helper lemma for tsum inequality in EReal
              have h_E_nonneg : ∀ n, 0 ≤ ∑ B' ∈ I_E_n n, B'.volume := by
                intro n; apply Finset.sum_nonneg; intro B' _; exact Box.volume_nonneg B'
              have h_F_nonneg : ∀ n, 0 ≤ ∑ B' ∈ I_F_n n, B'.volume := by
                intro n; apply Finset.sum_nonneg; intro B' _; exact Box.volume_nonneg B'

              -- Apply the helper lemma
              exact EReal.tsum_add_le_of_nonneg_pointwise h_E_nonneg h_F_nonneg h_pw_le
          _ ≤ Lebesgue_outer_measure (E ∪ F) + (ε : EReal) := hS_vol

      -- From h_eps, conclude the inequality holds
      exact EReal.le_of_forall_pos_le_add' h_eps

  -- Combine both directions
  exact le_antisymm h_le h_ge

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
