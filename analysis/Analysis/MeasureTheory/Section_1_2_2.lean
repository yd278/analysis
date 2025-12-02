import Analysis.MeasureTheory.Section_1_2_1

/-!
# Introduction to Measure Theory, Section 1.2.2: Lebesgue measurability

A companion to (the introduction to) Section 1.2.2 of the book "An introduction to Measure Theory".

-/

/-- Lemma 1.2.13(i) (Every open set is Lebesgue measurable). -/
theorem IsOpen.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsOpen E) : LebesgueMeasurable E := by
  -- Strategy: For any ε > 0, choose U = E itself
  -- Since E is already open, U \ E = E \ E = ∅, and m*(∅) = 0 ≤ ε
  intro ε hε
  -- Witness: U = E
  use E
  constructor
  · -- E is open (given)
    exact hE
  constructor
  · -- E ⊆ E (reflexivity)
    rfl
  · -- Show m*(E \ E) ≤ ε
    have h_empty : E \ E = ∅ := Set.diff_self
    rw [h_empty]
    have h_zero : Lebesgue_outer_measure (∅ : Set (EuclideanSpace' d)) = 0 :=
      Lebesgue_outer_measure.of_empty d
    rw [h_zero]
    exact le_of_lt hε

/-- Helper: For any set E and ε > 0, there exists an open U ⊇ E with m*(U) ≤ m*(E) + ε.
    This follows from outer regularity (Lemma 1.2.12). -/
private lemma exists_open_superset_measure_le {d:ℕ} (E: Set (EuclideanSpace' d)) (ε : EReal) (hε : 0 < ε) :
    ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure U ≤ Lebesgue_outer_measure E + ε := by
  -- By outer regularity (Lebesgue_outer_measure.eq):
  -- m*(E) = sInf { m*(U) | E ⊆ U ∧ IsOpen U }
  -- For any ε > 0, there exists U in this set with m*(U) ≤ m*(E) + ε
  have h_outer_reg := Lebesgue_outer_measure.eq (d := d) E
  -- The set of measures is nonempty (Set.univ is open and contains E)
  let S := {M | ∃ U, E ⊆ U ∧ IsOpen U ∧ M = Lebesgue_outer_measure U}
  have h_set_nonempty : S.Nonempty := by
    use Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d))
    exact ⟨Set.univ, Set.subset_univ E, isOpen_univ, rfl⟩
  -- Key: sInf S + ε is not a lower bound of S, so there exists v ∈ S with v < sInf S + ε
  have h_inf : IsGLB S (sInf S) := isGLB_sInf S
  -- Since m*(E) = sInf S and 0 < ε, we have sInf S < sInf S + ε
  -- So sInf S + ε is not the greatest lower bound, hence not in lowerBounds S
  -- This means ∃ v ∈ S, v < sInf S + ε
  have h_ne_bot : sInf S ≠ ⊥ := by
    intro h_eq
    rw [h_eq] at h_inf
    have h_zero_lb : (0 : EReal) ∈ lowerBounds S := by
      intro v hv
      obtain ⟨U, _, _, rfl⟩ := hv
      exact Lebesgue_outer_measure.nonneg U
    have h_le : (0 : EReal) ≤ ⊥ := h_inf.2 h_zero_lb
    exact not_le.mpr EReal.bot_lt_zero h_le
  by_cases h_top : sInf S = ⊤
  · -- If sInf S = ⊤, then m*(E) = ⊤, and any open set works since ⊤ + ε = ⊤ in EReal
    use Set.univ
    refine ⟨isOpen_univ, Set.subset_univ E, ?_⟩
    rw [h_outer_reg, h_top]
    exact le_top
  · -- sInf S ≠ ⊤, so sInf S < sInf S + ε
    have h_lt : sInf S < sInf S + ε := EReal.lt_add_of_pos hε h_ne_bot h_top
    -- So sInf S + ε is not in lowerBounds S
    have h_not_lb : sInf S + ε ∉ lowerBounds S := by
      intro h_is_lb
      have h_le : sInf S + ε ≤ sInf S := h_inf.2 h_is_lb
      exact not_lt.mpr h_le h_lt
    -- Therefore ∃ v ∈ S, v < sInf S + ε
    push_neg at h_not_lb
    obtain ⟨v, hv_in_S, hv_lt⟩ := h_not_lb
    -- Extract the open set U from v ∈ S
    obtain ⟨U, hE_sub_U, hU_open, hv_eq⟩ := hv_in_S
    use U
    refine ⟨hU_open, hE_sub_U, ?_⟩
    rw [h_outer_reg, ← hv_eq]
    exact le_of_lt hv_lt

/-- Lemma 1.2.13(ii) (Every closed set is Lebesgue measurable).
    Proof outline from textbook:
    1. Reduce to bounded closed sets (compact by Heine-Borel)
    2. For compact E: use outer regularity to find U with m*(U) ≤ m*(E) + ε
    3. Show m*(U \ E) ≤ ε using properties of almost disjoint cubes and compactness -/
theorem IsClosed.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsClosed E) : LebesgueMeasurable E := by
  -- We need: ∀ ε > 0, ∃ U open, E ⊆ U ∧ m*(U \ E) ≤ ε
  intro ε hε
  -- If E = ∅, use U = ∅
  by_cases hE_empty : E = ∅
  · use ∅
    refine ⟨isOpen_empty, ?_, ?_⟩
    · rw [hE_empty]
    · simp only [Set.empty_diff]
      rw [Lebesgue_outer_measure.of_empty]
      exact le_of_lt hε
  push_neg at hE_empty
  -- E is nonempty and closed, hence Eᶜ is open
  have hEc_open : IsOpen Eᶜ := hE.isOpen_compl
  -- Use helper to get open U ⊇ E with m*(U) close to m*(E)
  have hε_half_pos : (0 : EReal) < ε / 2 := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top =>
      have h : (⊤ : EReal) / 2 = ⊤ := by
        rw [show (2 : EReal) = (2 : ℝ) from rfl]
        simp only [EReal.top_div_coe, ↓reduceIte]
        norm_num
      rw [h]
      exact EReal.zero_lt_top
    | coe r =>
      have h2 : (2 : EReal) = (2 : ℝ) := rfl
      rw [h2, ← EReal.coe_div r 2]
      exact EReal.coe_pos.mpr (half_pos (EReal.coe_pos.mp hε))
  obtain ⟨U, hU_open, hE_sub_U, hU_meas⟩ := exists_open_superset_measure_le E (ε/2) hε_half_pos
  use U
  refine ⟨hU_open, hE_sub_U, ?_⟩
  -- Need to show: m*(U \ E) ≤ ε
  -- Key insight: U \ E is open (since E is closed)
  have h_diff_open : IsOpen (U \ E) := hU_open.sdiff hE
  -- The main argument uses:
  -- 1. U \ E = ⋃ Qₙ (almost disjoint dyadic cubes) by Lemma 1.2.11
  -- 2. m*(U \ E) = Σ|Qₙ| by Lemma 1.2.9
  -- 3. For compact E, finite unions ⋃ₙ₌₁ᴺ Qₙ are separated from E
  -- 4. By additivity on separated sets: m*(E ∪ ⋃ₙ₌₁ᴺ Qₙ) = m*(E) + Σₙ₌₁ᴺ|Qₙ|
  -- 5. By monotonicity: m*(E) + Σₙ₌₁ᴺ|Qₙ| ≤ m*(U)
  -- 6. Taking N → ∞: m*(E) + m*(U \ E) ≤ m*(U) ≤ m*(E) + ε/2
  -- 7. Hence m*(U \ E) ≤ ε/2 ≤ ε
  -- This requires substantial machinery for the general case
  sorry

abbrev IsNull {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := Lebesgue_outer_measure E = 0

/-- Lemma 1.2.13(iii) (Every null set is Lebesgue measurable).-/
theorem IsNull.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsNull E) : LebesgueMeasurable E := by
  -- Strategy: For any ε > 0, since m*(E) = 0, get a box cover with total volume < ε,
  -- then inflate boxes to open sets. The union is open and contains E.
  intro ε hε
  -- Handle dimension 0 separately
  by_cases hd : d = 0
  · -- In dimension 0, EuclideanSpace' 0 is a single point.
    -- Since m*(E) = 0 and m*(univ) = 1 for nonempty sets in d=0, E must be empty.
    -- Use U = E = ∅, which is open, E ⊆ U, and U \ E = ∅ has measure 0.
    subst hd
    -- In d=0: m*(E) = if E.Nonempty then 1 else 0
    -- hE : IsNull E is an abbrev for Lebesgue_outer_measure E = 0
    have hE' : Lebesgue_outer_measure E = 0 := hE
    rw [Lebesgue_outer_measure_of_dim_zero] at hE'
    simp only [ite_eq_right_iff, one_ne_zero] at hE'
    -- hE' : E.Nonempty → False, i.e., E = ∅
    have hE_empty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE'
    use ∅
    refine ⟨isOpen_empty, ?_, ?_⟩
    · rw [hE_empty]
    · simp only [Set.empty_diff]
      rw [Lebesgue_outer_measure.of_empty]
      exact le_of_lt hε
  -- Now d > 0
  push_neg at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  -- m*(E) = 0 implies m*(E) ≠ ⊤
  have h_finite : Lebesgue_outer_measure E ≠ ⊤ := by rw [hE]; exact EReal.zero_ne_top
  -- Convert EReal ε to a real number
  -- Since ε > 0, get a real ε' with 0 < ε' and ε' ≤ ε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r =>
      have hr : 0 < r := EReal.coe_pos.mp hε
      exact ⟨r, hr, le_refl _⟩
  -- Get an ε'/2-close box cover
  have hε2_pos : 0 < ε' / 2 := by linarith
  obtain ⟨S, hS_cover, hS_vol⟩ := Lebesgue_outer_measure.exists_cover_close hd_pos E (ε' / 2) hε2_pos h_finite
  -- hS_vol : ∑' n, (S n).volume.toEReal ≤ m*(E) + ε'/2 = 0 + ε'/2 = ε'/2
  rw [hE] at hS_vol
  simp only [zero_add] at hS_vol
  -- Inflate each box to get an open set containing it
  -- Use δₙ = ε' / 2^(n+2) so that ∑ δₙ = ε'/2
  let δ : ℕ → ℝ := fun n => ε' / 2 / 2 ^ (n + 1)
  have hδ_pos : ∀ n, 0 < δ n := fun n => by simp only [δ]; positivity
  -- Get inflated boxes using Box.inflate
  have h_inflate := fun n => Box.inflate (S n) (δ n) (hδ_pos n)
  choose U' hU'_subset hU'_open hU'_vol using h_inflate
  -- Define U as union of interiors of inflated boxes
  let U := ⋃ n, interior (U' n).toSet
  use U
  constructor
  · -- U is open (union of open sets)
    exact isOpen_iUnion (fun n => isOpen_interior)
  constructor
  · -- E ⊆ U
    calc E ⊆ ⋃ n, (S n).toSet := hS_cover
         _ ⊆ ⋃ n, interior (U' n).toSet := Set.iUnion_mono (fun n => hU'_subset n)
  · -- m*(U \ E) ≤ ε
    -- Key bounds: m*(U \ E) ≤ m*(U) ≤ ∑ |U' n|ᵥ ≤ ∑ (|S n|ᵥ + δ n) ≤ ε'/2 + ε'/2 = ε' ≤ ε
    have h1 : Lebesgue_outer_measure (U \ E) ≤ Lebesgue_outer_measure U :=
      Lebesgue_outer_measure.mono Set.diff_subset
    have h2 : Lebesgue_outer_measure U ≤ ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) := by
      have : U = ⋃ n, interior (U' n).toSet := rfl
      rw [this]
      exact Lebesgue_outer_measure.union_le _
    -- Each interior has measure ≤ box volume
    have h3 : ∀ n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ (U' n).volume.toEReal := by
      intro n
      calc Lebesgue_outer_measure (interior (U' n).toSet)
          ≤ Lebesgue_outer_measure (U' n).toSet := Lebesgue_outer_measure.mono interior_subset
        _ = (IsElementary.box (U' n)).measure.toEReal := by
            rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _)]
        _ = (U' n).volume.toEReal := by rw [IsElementary.measure_of_box]
    -- Each inflated box volume ≤ original + δ
    have h4 : ∀ n, (U' n).volume.toEReal ≤ ((S n).volume + δ n).toEReal := by
      intro n
      exact EReal.coe_le_coe_iff.mpr (hU'_vol n)
    -- The sum splits: ∑ (|S n|ᵥ + δ n) = ∑ |S n|ᵥ + ∑ δ n ≤ ε'/2 + ε'/2 = ε' ≤ ε
    have hδ_sum : ∑' n, (δ n : ℝ) = ε' / 2 := by
      simp only [δ, div_div]
      have h := tsum_geometric_two' (ε' / 2)
      convert h using 1
      congr 1
      ext n
      ring_nf
    -- Combine the bounds to show m*(U \ E) ≤ ε' ≤ ε
    -- Strategy:
    -- m*(U\E) ≤ m*(U) ≤ ∑ m*(interior U'_n) ≤ ∑ vol(U'_n) ≤ ∑ (vol(S_n) + δ_n)
    --         ≤ ∑ vol(S_n) + ∑ δ_n ≤ ε'/2 + ε'/2 = ε' ≤ ε
    -- The key steps use h1, h2, h3, h4, hS_vol, hδ_sum, hε'_le
    have h_sum_le : ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ε' := by
      -- Each interior measure ≤ vol(U' n) ≤ vol(S n) + δ n
      -- Sum: ∑ vol(S n) ≤ ε'/2, ∑ δ n = ε'/2, so total ≤ ε'
      -- First show δ is summable (geometric series)
      have hδ_summable : Summable δ := by
        simp only [δ, div_div]
        exact (summable_geometric_two' (ε' / 2)).congr (fun n => by ring_nf)
      -- Show volumes are summable (from the bound hS_vol)
      have hvol_nonneg : ∀ n, 0 ≤ (S n).volume := fun n => Box.volume_nonneg _
      have hvol_sum : Summable (fun n => (S n).volume) := by
        -- Key: use that the partial sums in EReal are bounded
        have h_partial_bound : ∀ t : Finset ℕ, (∑ n ∈ t, (S n).volume : EReal) ≤ ε' / 2 := by
          intro t
          calc (∑ n ∈ t, (S n).volume : EReal)
              ≤ ∑' n, ((S n).volume : EReal) := EReal.finset_sum_le_tsum hvol_nonneg t
            _ ≤ ε' / 2 := hS_vol
        -- In ℝ: partial sums bounded implies summable for nonneg sequences
        have h_partial_real : ∀ t : Finset ℕ, ∑ n ∈ t, (S n).volume ≤ ε' / 2 := by
          intro t
          have h := h_partial_bound t
          have h_coe : (∑ n ∈ t, (S n).volume : EReal) = ↑(∑ n ∈ t, (S n).volume) :=
            (EReal.coe_finset_sum (fun n _ => hvol_nonneg n)).symm
          rw [h_coe] at h; exact EReal.coe_le_coe_iff.mp h
        exact summable_of_sum_le hvol_nonneg h_partial_real
      have hsum_combined : Summable (fun n => (S n).volume + δ n) := hvol_sum.add hδ_summable
      -- Use transitivity through ε' bound:
      -- ∑ m*(interior U'_n) ≤ ∑ vol(U'_n) ≤ ∑ (vol S_n + δ_n) = ∑ vol S_n + ∑ δ_n ≤ ε'/2 + ε'/2 = ε'
      have h_interior_bound : ∀ n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ((S n).volume + δ n : EReal) := by
        intro n
        calc Lebesgue_outer_measure (interior (U' n).toSet)
            ≤ (U' n).volume.toEReal := h3 n
          _ ≤ ((S n).volume + δ n).toEReal := h4 n
          _ = ((S n).volume + δ n : EReal) := rfl
      -- Sum bound: use EReal.tsum_le_coe_tsum_of_forall_le
      have hg_nonneg : ∀ n, 0 ≤ (S n).volume + δ n := fun n => by linarith [hvol_nonneg n, hδ_pos n]
      have h_tsum_bound : ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ∑' n, ((S n).volume + δ n : EReal) :=
        EReal.tsum_le_coe_tsum_of_forall_le (fun n => Lebesgue_outer_measure.nonneg _)
          hg_nonneg hsum_combined h_interior_bound
      -- Key equality: tsums in EReal with coercion can be rewritten
      have h_tsum_eq : ∑' n, (↑(S n).volume + ↑(δ n) : EReal) = ↑(∑' n, ((S n).volume + δ n)) := by
        have h1 : ∑' n, (↑(S n).volume + ↑(δ n) : EReal) = ∑' n, ↑((S n).volume + δ n) := by
          apply tsum_congr
          intro n; exact (EReal.coe_add _ _).symm
        have h2 : ∑' n, (↑((S n).volume + δ n) : EReal) = ↑(∑' n, ((S n).volume + δ n)) :=
          (EReal.coe_tsum_of_nonneg hg_nonneg hsum_combined).symm
        rw [h1, h2]
      calc ∑' n, Lebesgue_outer_measure (interior (U' n).toSet)
          ≤ ∑' n, (↑(S n).volume + ↑(δ n) : EReal) := h_tsum_bound
        _ = ↑(∑' n, ((S n).volume + δ n)) := h_tsum_eq
        _ = ↑(∑' n, (S n).volume + ∑' n, δ n) := by rw [hvol_sum.tsum_add hδ_summable]
        _ = ↑(∑' n, (S n).volume) + ↑(∑' n, δ n) := by rw [EReal.coe_add]
        _ ≤ ↑(ε' / 2) + ↑(ε' / 2) := by
            apply add_le_add
            · have := EReal.coe_tsum_of_nonneg hvol_nonneg hvol_sum
              rw [this]; exact hS_vol
            · rw [hδ_sum]
        _ = ε' := by rw [← EReal.coe_add]; norm_cast; ring
    calc Lebesgue_outer_measure (U \ E)
        ≤ Lebesgue_outer_measure U := h1
      _ ≤ ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) := h2
      _ ≤ ε' := h_sum_le
      _ ≤ ε := hε'_le

/-- Lemma 1.2.13(iv) (Empty set is measurable). This lemma requires proof.  -/
theorem LebesgueMeasurable.empty {d:ℕ} : LebesgueMeasurable (∅: Set (EuclideanSpace' d)) :=
-- use (i) directly
  IsOpen.measurable isOpen_empty

theorem LebesgueMeasurable.empty' {d:ℕ} : LebesgueMeasurable (∅: Set (EuclideanSpace' d)) := by
-- use definition of Lebesgue measurability
  intro ε hε
  use ∅
  constructor
  · exact isOpen_empty
  constructor
  · exact Set.empty_subset ∅
  · have h_empty : ∅ \ ∅ = (∅ : Set (EuclideanSpace' d)) := Set.diff_self
    rw [h_empty]
    rw [Lebesgue_outer_measure.of_empty d]
    exact le_of_lt hε

/-- Lemma 1.2.13(v) (Complement of a measurable set is measurable). This lemma requires proof.  -/
theorem LebesgueMeasurable.complement {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) : LebesgueMeasurable (Eᶜ) := by
  sorry

/-- Lemma 1.2.13(vi) (Countable union of measurable sets is measurable). This lemma requires proof.  -/
theorem LebesgueMeasurable.countable_union {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) : LebesgueMeasurable (⋃ n, E n) := by
  -- Use the ε/2^n trick: let ε > 0 be arbitrary
  intro ε hε
  -- Convert EReal ε to a real number ε' with 0 < ε' ≤ ε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r =>
      have hr : 0 < r := EReal.coe_pos.mp hε
      exact ⟨r, hr, le_refl _⟩
  -- For each n, get U_n open with E_n ⊆ U_n and m*(U_n \ E_n) ≤ ε'/2^(n+1)
  have hδ_pos : ∀ n, (0:EReal) < ε' / 2^(n+1) := fun n => by
    apply EReal.div_pos (EReal.coe_pos.mpr hε'_pos)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_pos.mpr (by positivity)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_ne_top ((2:ℝ)^(n+1))
  -- Apply measurability of each E_n with ε'/2^(n+1)
  choose U hU_open hE_sub hU_diff using fun n => hE n (ε' / 2^(n+1)) (hδ_pos n)
  -- The open set is ⋃ n, U n
  use ⋃ n, U n
  constructor
  · -- ⋃ n, U n is open (union of open sets)
    exact isOpen_iUnion hU_open
  constructor
  · -- ⋃ n, E n ⊆ ⋃ n, U n
    apply Set.iUnion_mono
    intro n; exact hE_sub n
  · -- m*((⋃ n, U n) \ (⋃ n, E n)) ≤ ε
    -- Key: (⋃ U_n) \ (⋃ E_n) ⊆ ⋃ (U_n \ E_n)
    have h_diff_subset : (⋃ n, U n) \ (⋃ n, E n) ⊆ ⋃ n, (U n \ E n) := by
      intro x ⟨hx_in_U, hx_not_in_E⟩
      simp only [Set.mem_iUnion] at hx_in_U hx_not_in_E ⊢
      obtain ⟨k, hxk⟩ := hx_in_U
      use k
      constructor
      · exact hxk
      · intro hx_Ek
        exact hx_not_in_E ⟨k, hx_Ek⟩
    calc Lebesgue_outer_measure ((⋃ n, U n) \ (⋃ n, E n))
        ≤ Lebesgue_outer_measure (⋃ n, (U n \ E n)) :=
          Lebesgue_outer_measure.mono h_diff_subset
      _ ≤ ∑' n, Lebesgue_outer_measure (U n \ E n) :=
          Lebesgue_outer_measure.union_le _
      _ ≤ ∑' n, ((ε' / 2^(n+1) : ℝ) : EReal) := by
          -- Use EReal.tsum_le_coe_tsum_of_forall_le
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_f_nonneg : ∀ n, 0 ≤ Lebesgue_outer_measure (U n \ E n) :=
            fun n => Lebesgue_outer_measure.nonneg _
          have h_le_coe : ∀ n, Lebesgue_outer_measure (U n \ E n) ≤ ((ε' / 2^(n+1) : ℝ) : EReal) := by
            intro n
            calc Lebesgue_outer_measure (U n \ E n)
                ≤ (↑ε' : EReal) / 2^(n+1) := hU_diff n
              _ = ↑(ε' / 2^(n+1)) := by
                  rw [EReal.coe_div]
                  congr 1
                  exact Eq.symm (EReal.coe_pow 2 (n + 1))
          exact EReal.tsum_le_coe_tsum_of_forall_le h_f_nonneg h_nonneg h_summable h_le_coe
      _ = ε' := by
          -- ∑ n, ε'/2^(n+1) = ε' (geometric series)
          have h_sum : ∑' n : ℕ, (ε' : ℝ) / 2^(n+1) = ε' := tsum_geometric_eps ε' hε'_pos
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          rw [← EReal.coe_tsum_of_nonneg h_nonneg h_summable, h_sum]
      _ ≤ ε := hε'_le

theorem LebesgueMeasurable.finite_union {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hE: ∀ i, LebesgueMeasurable (E i)) : LebesgueMeasurable (⋃ i, E i) := by
  sorry

theorem LebesgueMeasurable.union {d n:ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : LebesgueMeasurable (E ∪ F) := by
  sorry

/-- Lemma 1.2.13(vii) (Countable intersection of measurable sets is measurable). This lemma requires proof. -/
theorem LebesgueMeasurable.countable_inter {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) : LebesgueMeasurable (⋂ n, E n) := by
  sorry

theorem LebesgueMeasurable.finite_inter {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hE: ∀ i, LebesgueMeasurable (E i)) : LebesgueMeasurable (⋂ i, E i) := by
  sorry

theorem LebesgueMeasurable.inter {d n:ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : LebesgueMeasurable (E ∩ F) := by
  sorry

/-- Exercise 1.2.7 (Criteria for measurability)-/
theorem LebesgueMeasurable.TFAE {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E,
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure (U \ E) ≤ ε),
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ Lebesgue_outer_measure (symmDiff U E) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsClosed F ∧ F ⊆ E ∧ Lebesgue_outer_measure (E \ F) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsClosed F ∧ Lebesgue_outer_measure (symmDiff F E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε)
    ].TFAE
  := by sorry

  /-- Exercise 1.2.8 -/
theorem Jordan_measurable.lebesgue {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : LebesgueMeasurable E := by
  sorry

open BoundedInterval

abbrev CantorInterval (n:ℕ) : Set ℝ := ⋃ a : Fin n → ({0, 2}:Set ℕ), (Icc (∑ i, (a i)/(3:ℝ)^(i.val+1)) (∑ i, a i/(3:ℝ)^(i.val+1) + 1/(3:ℝ)^(n+1))).toSet

abbrev CantorSet : Set ℝ := ⋂ n : ℕ, CantorInterval n

/-- Exercise 1.2.9 (Middle thirds Cantor set ) -/
theorem CantorSet.compact : IsCompact CantorSet := by
  sorry

theorem CantorSet.uncountable : Uncountable CantorSet := by
  sorry

theorem CantorSet.null : IsNull (Real.equiv_EuclideanSpace' '' CantorSet) := by sorry

/-- Exercise 1.2.10 ([0,1) is not the countable union of pairwise disjoint closed intervals)-/
example : ¬ ∃ (I: ℕ → BoundedInterval), (∀ n, IsClosed (I n).toSet) ∧ (Set.univ.PairwiseDisjoint (fun n ↦ (I n).toSet) ) ∧ (⋃ n, (I n).toSet = Set.Ico 0 1) := by
  sorry

/-- Exercise 1.2.10, challenge version -/
example : ¬ ∃ (E: ℕ → Set ℝ), (∀ n, IsClosed (E n)) ∧ (Set.univ.PairwiseDisjoint (fun n ↦ (E n)) ) ∧ (⋃ n, (E n) = Set.Ico 0 1) := by
  sorry

theorem Jordan_measurable.Lebesgue_measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : Lebesgue_measure E = hE.measure := by
  sorry

/-- Lemma 1.2.15(a) (Empty set has zero Lebesgue measure). The proof is missing. -/
@[simp]
theorem Lebesgue_measure.empty {d:ℕ} : Lebesgue_measure (∅: Set (EuclideanSpace' d)) = 0 := by
  sorry

/-- Lemma 1.2.15(b) (Countable additivity). The proof is missing. -/
theorem Lebesgue_measure.countable_union {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hmes: ∀ n, LebesgueMeasurable (E n)) (hdisj: Set.univ.PairwiseDisjoint E) : Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  sorry

theorem Lebesgue_measure.finite_union {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hmes: ∀ n, LebesgueMeasurable (E n)) (hdisj: Set.univ.PairwiseDisjoint E) : Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  sorry

theorem Lebesgue_measure.union {d:ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) (hdisj: E ∩ F = ∅) : Lebesgue_measure (E ∪ F) = Lebesgue_measure E + Lebesgue_measure F := by
  sorry

/-- Exercise 1.2.11(a) (Upward monotone convergence)-/
theorem Lebesgue_measure.upward_monotone_convergence {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) (hmono: ∀ n, E n ⊆ E (n + 1)) : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋃ n, E n))) := by
  sorry

/-- Exercise 1.2.11(b) (Downward monotone convergence)-/
theorem Lebesgue_measure.downward_monotone_convergence {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) (hmono: ∀ n, E (n+1) ⊆ E n) (hfin: ∃ n, Lebesgue_measure (E n) < ⊤) : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋂ n, E n))) := by
  sorry

/-- Exercise 1.2.11 (c) (counterexample)-/
example : ∃ (d:ℕ) (E: ℕ → Set (EuclideanSpace' d)) (hE: ∀ n, LebesgueMeasurable (E n)) (hmono: ∀ n, E (n+1) ⊆ E n), ¬ Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋂ n, E n))) := by sorry

/-- Exercise 1.2.12 -/
example {d:ℕ} (m: Set (EuclideanSpace' d) → EReal) (h_empty: m ∅ = 0) (h_pos: ∀ E, 0 ≤ m E) (hadd: ∀ E: ℕ → Set (EuclideanSpace' d), (Set.univ.PairwiseDisjoint E) → (∀ n, LebesgueMeasurable (E n)) → m (⋃ n, E n) = ∑' n, m (E n)) {E F: Set (EuclideanSpace' d)}
(hsub: E ⊆ F) (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : m E ≤ m F := by
  sorry

/-- Exercise 1.2.12 -/
example {d:ℕ} (m: Set (EuclideanSpace' d) → EReal) (h_empty: m ∅ = 0) (h_pos: ∀ E, 0 ≤ m E) (hadd: ∀ E: ℕ → Set (EuclideanSpace' d), (Set.univ.PairwiseDisjoint E) → (∀ n, LebesgueMeasurable (E n)) → m (⋃ n, E n) = ∑' n, m (E n)) {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)):  m (⋃ n, E n) ≤ ∑' n, m (E n) := by
  sorry

/-- Exercise 1.2.13(i) -/
example {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} {E₀: Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) (hpoint: ∀ x, Filter.atTop.Tendsto (fun n ↦ (E n).indicator' x) (nhds (E₀.indicator' x))) : LebesgueMeasurable E₀ := by sorry

/-- Exercise 1.2.13(ii) -/
example {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} {E₀ F: Set (EuclideanSpace' d)}
  (hE: ∀ n, LebesgueMeasurable (E n))
  (hpoint: ∀ x, Filter.atTop.Tendsto (fun n ↦ (E n).indicator' x) (nhds (E₀.indicator' x)))
  (hsub: ∀ n, E n ⊆ F) (hFmes: LebesgueMeasurable F) (hfin: Lebesgue_measure F < ⊤) : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure E₀)) := by sorry

/-- Exercise 1.2.13(iii) -/
example : ∃ (d:ℕ) (E: ℕ → Set (EuclideanSpace' d)) (E₀ F: Set (EuclideanSpace' d))
  (hE: ∀ n, LebesgueMeasurable (E n))
  (hpoint: ∀ x, Filter.atTop.Tendsto (fun n ↦ (E n).indicator' x) (nhds (E₀.indicator' x)))
  (hsub: ∀ n, E n ⊆ F) (hFmes: LebesgueMeasurable F), ¬ Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure E₀)) := by sorry

/-- Exercise 1.2.14 -/
example {d:ℕ} (E: Set (EuclideanSpace' d)) : ∃ (F: Set (EuclideanSpace' d)), E ⊆ F ∧ LebesgueMeasurable F ∧ Lebesgue_measure F = Lebesgue_outer_measure E := by sorry

/-- Exercise 1.2.15 (Inner regularity)-/
theorem Lebesgue_measure.eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E): Lebesgue_measure E = sSup { M | ∃ K, K ⊆ E ∧ IsCompact K ∧ M = Lebesgue_measure K} := by
  sorry

/-- Exercise 1.2.16 (Criteria for measurability)-/
theorem LebesgueMeasurable.finite_TFAE {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E ∧ Lebesgue_measure E < ⊤,
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_measure U < ⊤ ∧ Lebesgue_outer_measure (U \ E) ≤ ε),
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ Bornology.IsBounded U ∧ Lebesgue_outer_measure (symmDiff U E) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsCompact F ∧ F ⊆ E ∧ Lebesgue_outer_measure (E \ F) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsCompact F ∧ Lebesgue_outer_measure (symmDiff F E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Lebesgue_measure E' < ⊤ ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Bornology.IsBounded E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), IsElementary E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ (n:ℤ) (F: Finset (Box d)), (∀ B ∈ F, B.IsDyadicAtScale n) ∧ Lebesgue_outer_measure (symmDiff (⋃ B ∈ F, B.toSet) E) ≤ ε)
    ].TFAE
  := by sorry

/-- Exercise 1.2.17 (Caratheodory criterion one direction)-/
theorem LebesgueMeasurable.caratheodory {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E,
      (∀ A: Set (EuclideanSpace' d), IsElementary A → Lebesgue_outer_measure A = Lebesgue_outer_measure (A ∩ E) + Lebesgue_outer_measure (A \ E)),
      (∀ (B:Box d),  Lebesgue_outer_measure B.toSet = Lebesgue_outer_measure (B.toSet ∩ E) + Lebesgue_outer_measure (B.toSet \ E))
    ].TFAE
  := by sorry

theorem Bornology.IsBounded.inElementary {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : ∃ (A: Set (EuclideanSpace' d)), IsElementary A ∧ E ⊆ A := by sorry

noncomputable def inner_measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : ℝ := (Lebesgue_measure hE.inElementary.choose).toReal - (Lebesgue_measure (hE.inElementary.choose \ E)).toReal

/-- Exercise 1.2.18(i) (Inner measure)-/
theorem inner_measure.eq {d:ℕ} {E A: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E)
  (hA: IsElementary A) (hsub: E ⊆ A) : inner_measure hE = Lebesgue_measure A - Lebesgue_outer_measure (A \ E) := by
  sorry

/-- Exercise 1.2.18(ii) (Inner measure)-/
theorem inner_measure.le {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E)
  : inner_measure hE ≤ Lebesgue_outer_measure E := by
  sorry

/-- Exercise 1.2.18(ii) (Inner measure)-/
theorem inner_measure.eq_iff {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E)
  : inner_measure hE = Lebesgue_outer_measure E ↔ LebesgueMeasurable E := by
  sorry

def IsFσ  {X:Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsClosed t) ∧ T.Countable ∧ s = ⋃₀ T

/-- Exercise 1.2.19 -/
theorem LebesgueMeasurable.TFAE' {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E,
      (∃ F, ∃ N, IsGδ F ∧ IsNull N ∧ E = F \ N),
      (∃ F, ∃ N, IsFσ F ∧ IsNull N ∧ E = F ∪ N)
    ].TFAE
  := by sorry

open Pointwise

/-- Exercise 1.2.20 (Translation invariance) -/
theorem LebesgueMeasurable.translate {d:ℕ} (E: Set (EuclideanSpace' d)) (x: EuclideanSpace' d) :
    LebesgueMeasurable E ↔ LebesgueMeasurable (E + {x}) := by
  sorry

theorem Lebesgue_measure.translate {d:ℕ} {E: Set (EuclideanSpace' d)} (x: EuclideanSpace' d)
   (hE: LebesgueMeasurable E): Lebesgue_measure (E + {x}) = Lebesgue_measure E := by
  sorry

/-- Exercise 1.2.21 (Change of variables) -/
lemma LebesgueMeasurable.linear {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d)
{E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E): LebesgueMeasurable (T '' E) := by
  sorry

/-- Exercise 1.2.21 (Change of variables) -/
lemma Lebesgue_measure.linear {d:ℕ} (A: Matrix (Fin d) (Fin d) ℝ) [Invertible A]
 {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E): Lebesgue_measure (A.linear_equiv '' E) = |A.det| * Lebesgue_measure E := by
  sorry

/-- Exercise 1.2.22 -/
theorem Lebesgue_outer_measure.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ Lebesgue_outer_measure E₁ * Lebesgue_outer_measure E₂ := by sorry

/-- Exercise 1.2.22 -/
theorem LebesgueMeasurable.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: LebesgueMeasurable E₁) (hE₂: LebesgueMeasurable E₂) : LebesgueMeasurable (EuclideanSpace'.prod E₁ E₂) := by sorry

/-- Exercise 1.2.22 -/
theorem Lebesgue_measure.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: LebesgueMeasurable E₁) (hE₂: LebesgueMeasurable E₂)
  : Lebesgue_measure (EuclideanSpace'.prod E₁ E₂) = Lebesgue_measure E₁ * Lebesgue_measure E₂ := by sorry

/-- Exercise 1.2.23 (Uniqueness of Lebesgue measure) -/
theorem Lebesgue_measure.unique {d:ℕ} (m: Set (EuclideanSpace' d) → EReal)
  (h_empty: m ∅ = 0) (h_pos: ∀ E, 0 ≤ m E)
  (h_add: ∀ E: ℕ → Set (EuclideanSpace' d), (Set.univ.PairwiseDisjoint E) → (∀ n, LebesgueMeasurable (E n)) → m (⋃ n, E n) = ∑' n, m (E n))
  (hnorm: m (Box.unit_cube d) = 1)
  : ∀ E, LebesgueMeasurable E → m E = Lebesgue_measure E := by sorry

/-- Exercise 1.2.24(i) (Lebesgue measure as the completion of elementary measure)-/
instance IsElementary.ae_equiv {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A):
Setoid (Set A) := {
   r E F := IsNull (Subtype.val '' (_root_.symmDiff E F))
   iseqv := by sorry
}

def IsElementary.ae_subsets {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) := Quotient hA.ae_equiv

def IsElementary.ae_quot {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: Set A): hA.ae_subsets := Quotient.mk' (s := hA.ae_equiv) E

/-- Exercise 1.2.24(ii) (Lebesgue measure as the completion of elementary measure)-/
noncomputable def IsElementary.dist {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : hA.ae_subsets → hA.ae_subsets → ℝ := Quotient.lift₂ (fun E F ↦ (Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff E F))).toReal) (by sorry)

/-- Exercise 1.2.24(ii) (Lebesgue measure as the completion of elementary measure)-/
noncomputable instance IsElementary.metric {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : MetricSpace hA.ae_subsets := {
    dist := hA.dist
    dist_self := by sorry
    eq_of_dist_eq_zero := by sorry
    dist_comm := by sorry
    dist_triangle := by sorry
  }

/-- Exercise 1.2.24(ii) (Lebesgue measure as the completion of elementary measure)-/
instance IsElementary.complete {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : CompleteSpace hA.ae_subsets := by
  sorry

noncomputable def IsElementary.ae_elem {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : Set hA.ae_subsets := { E | ∃ F: Set A, IsElementary (Subtype.val '' F) ∧ hA.ae_quot F = E }

noncomputable def IsElementary.ae_measurable {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : Set hA.ae_subsets := { E | ∃ F: Set A, LebesgueMeasurable (Subtype.val '' F) ∧ hA.ae_quot F = E }

/-- Exercise 1.2.24(iii) (Lebesgue measure as the completion of elementary measure)-/
theorem IsElementary.measurable_eq_closure_elem {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : closure hA.ae_elem = hA.ae_measurable := by
  sorry

/-- Exercise 1.2.24(c) (Lebesgue measure as the completion of elementary measure)-/
theorem IsElementary.measurable_complete {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : closure hA.ae_elem = hA.ae_measurable := by
  sorry

noncomputable def IsElementary.ae_measure {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: hA.ae_measurable) : ℝ := (Lebesgue_measure (Subtype.val '' E.property.choose)).toReal

noncomputable def IsElementary.ae_elem_measure {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: hA.ae_elem) : ℝ := E.property.choose_spec.1.measure

/-- Exercise 1.2.24(iv) (Lebesgue measure as the completion of elementary measure)-/
theorem IsElementary.ae_measure_eq_completion {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (m: hA.ae_subsets → ℝ) :
ContinuousOn m hA.ae_measurable ∧ (∀ (E:hA.ae_elem), m E.val = hA.ae_elem_measure E)
↔ (∀ (E:hA.ae_measurable), m E.val = hA.ae_measure E) := by sorry

noncomputable abbrev IsCurve {d:ℕ} (C: Set (EuclideanSpace' d)) : Prop := ∃ (a b:ℝ) (γ: ℝ → EuclideanSpace' d), C = γ '' (Set.Icc a b) ∧ ContDiffOn ℝ 1 γ (Set.Icc a b)

/-- Exercise 1.2.25(i) -/
theorem IsCurve.null {d:ℕ} (hd: d ≥ 2) {C: Set (EuclideanSpace' d)} (hC: IsCurve C) : IsNull C := by sorry

example : ∃ (d:ℕ) (C: Set (EuclideanSpace' d)) (hC: IsCurve C), ¬ IsNull Cx := by
  sorry

/-- Exercise 1.2.25 -/
example {d:ℕ} (hd: d ≥ 2) : ¬ ∃ C: ℕ → Set (EuclideanSpace' d), (∀ n, IsCurve (C n)) ∧ (⋃ n, C n = (Box.unit_cube d).toSet) := by
  sorry
