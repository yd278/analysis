import Analysis.MeasureTheory.Section_1_1_3

/-!
# Introduction to Measure Theory, Section 1.2: Lebesgue measure

A companion to (the introduction to) Section 1.2 of the book "An introduction to Measure Theory".

-/

open BoundedInterval

/-- Exercise 1.2.1 -/
example : ∃ E: ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
  (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n)))
  ∧ ¬ JordanMeasurable (⋃ n, Real.equiv_EuclideanSpace' '' (E n)) := by
  sorry

/-- Exercise 1.2.1 -/
example : ∃ E: ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
  (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n)))
  ∧ ¬ JordanMeasurable (⋂ n, Real.equiv_EuclideanSpace' '' (E n)) := by
  sorry

/-- Exercise 1.2.2 -/
example : ∃ f: ℕ → ℝ → ℝ, ∃ F: ℝ → ℝ, ∃ M, ∀ n, ∀ x ∈ Set.Icc 0 1, |f n x| ≤ M ∧
    (∀ x ∈ Set.Icc 0 1, Filter.atTop.Tendsto (fun n ↦ f n x) (nhds (F x))) ∧
    (∀ n, RiemannIntegrableOn (f n) (Icc 0 1)) ∧
    ¬ RiemannIntegrableOn F (Icc 0 1) := by
  sorry

/-- Exercise 1.2.2 -/
def Ex_1_2_2b : Decidable ( ∀ f: ℕ → ℝ → ℝ, ∀ F: ℝ → ℝ, (∃ M, ∀ n, ∀ x ∈ Set.Icc 0 1, |f n x| ≤ M) → (∀ x ∈ Set.Icc 0 1, TendstoUniformly f F Filter.atTop) → (∀ n, RiemannIntegrableOn (f n) (Icc 0 1)) → RiemannIntegrableOn F (Icc 0 1) ) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`, depending on whether you believe the given statement to be true or false.
  sorry

theorem Jordan_outer_eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Jordan_outer_measure E = sInf (((fun S: Finset (Box d) ↦ ∑ B ∈ S, |B|ᵥ)) '' { S | E ⊆ ⋃ B ∈ S, B.toSet }) := by
  -- Strategy: Show equality via two inequalities (le_antisymm)
  apply le_antisymm

  -- Part 1 (≤): Jordan_outer_measure E ≤ sInf of box covers
  · -- For any box cover S, show Jordan_outer_measure E ≤ S.sum volume, then take infimum
    apply le_csInf
    -- Show the set of box cover sums is nonempty
    · obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
      obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
      use ∑ B ∈ T, |B|ᵥ
      use T
      simp
      intro a ha
      have : a ∈ A := hE_sub_A ha
      rw [hA_eq] at this
      exact this
    -- Show Jordan_outer_measure E is a lower bound for all box cover sums
    · intro m hm
      obtain ⟨S, hS_cover, rfl⟩ := hm
      -- The union ⋃ B ∈ S is elementary
      classical
      -- Map S : Finset (Box d) to a finset of sets
      let S_sets : Finset (Set (EuclideanSpace' d)) := S.image (fun B => B.toSet)
      have hS_elem : ∀ E ∈ S_sets, IsElementary E := by
        intro E hE
        simp [S_sets] at hE
        obtain ⟨B, _, rfl⟩ := hE
        exact IsElementary.box B
      -- Apply IsElementary.union' to show the union is elementary
      have h_union_eq : ⋃ E ∈ S_sets, E = ⋃ B ∈ S, B.toSet := by simp [S_sets]
      have hA_elem : IsElementary (⋃ B ∈ S, B.toSet) := by
        rw [←h_union_eq]
        exact IsElementary.union' hS_elem
      -- E ⊆ ⋃ B ∈ S, so Jordan_outer_measure E ≤ hA_elem.measure
      have h_outer_le : Jordan_outer_measure E ≤ hA_elem.measure := by
        unfold Jordan_outer_measure
        apply csInf_le
        · use 0; intro m' hm'; obtain ⟨_, hB, _, rfl⟩ := hm'; exact IsElementary.measure_nonneg hB
        · use ⋃ B ∈ S, B.toSet, hA_elem, hS_cover
      -- hA_elem.measure ≤ ∑ B ∈ S, |B|ᵥ by subadditivity (IsElementary.measure_of_union')
      have h_sub : hA_elem.measure ≤ ∑ B ∈ S, |B|ᵥ := by
        -- Apply IsElementary.measure_of_union' to get subadditivity
        have h1 := IsElementary.measure_of_union' hS_elem
        -- Show hA_elem.measure = (IsElementary.union' hS_elem).measure
        have h_eq : hA_elem.measure = (IsElementary.union' hS_elem).measure := by
          apply IsElementary.measure_eq_of_set_eq
          exact h_union_eq.symm
        -- Convert the sum over S_sets to sum over S
        -- Technical lemma: sum reindexing via Finset.sum_attach and Finset.sum_image
        have h2 : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ B ∈ S, |B|ᵥ := by
          -- Define a helper function to detach measure from proof
          let vol (E : Set (EuclideanSpace' d)) := if h : IsElementary E then h.measure else 0

          -- 1. Show RHS equals sum over S'
          let S' := S.filter (fun B => B.toSet.Nonempty)
          have h_rhs : ∑ B ∈ S, |B|ᵥ = ∑ B ∈ S', |B|ᵥ := by
             rw [←Finset.sum_filter_add_sum_filter_not S (fun B => B.toSet.Nonempty) (fun B => |B|ᵥ)]
             suffices ∑ B ∈ S.filter (fun B => ¬B.toSet.Nonempty), |B|ᵥ = 0 by simp [this, S']
             apply Finset.sum_eq_zero
             intro B hB
             rw [Finset.mem_filter] at hB
             exact Box.volume_eq_zero_of_empty B (Set.not_nonempty_iff_eq_empty.mp hB.2)
          rw [h_rhs]

          -- 2. Simplify LHS to use vol and sum over sets
          have h_lhs : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ E ∈ S_sets, vol E := by
            -- Congruence to vol
            have h_congr : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ E : S_sets, vol E.val := by
              apply Finset.sum_congr rfl
              intro E _
              dsimp [vol]
              rw [dif_pos (hS_elem E.val E.property)]
            rw [h_congr]
            -- Subtype sum to set sum
            change ∑ E ∈ S_sets.attach, vol E.val = ∑ E ∈ S_sets, vol E
            rw [Finset.sum_attach S_sets]
          rw [h_lhs]

          -- 3. Restrict set sum to non-empty sets
          let S_sets' := S'.image Box.toSet
          have h_subset : S_sets' ⊆ S_sets := Finset.image_subset_image (Finset.filter_subset _ _)

          have h_sets_eq : ∑ E ∈ S_sets, vol E = ∑ E ∈ S_sets', vol E := by
             rw [←Finset.sum_sdiff h_subset]
             suffices ∑ E ∈ S_sets \ S_sets', vol E = 0 by simp [this]
             apply Finset.sum_eq_zero
             intro E hE
             rw [Finset.mem_sdiff] at hE
             have hE_empty : E = ∅ := by
               obtain ⟨h_in, h_notin⟩ := hE
               rw [Finset.mem_image] at h_in
               obtain ⟨B, hB, rfl⟩ := h_in
               by_contra h_non
               apply h_notin
               simp [S_sets', S']
               use B
               simp [hB]
               rw [Set.nonempty_iff_ne_empty]
               exact h_non
             dsimp [vol]
             rw [hE_empty]
             rw [dif_pos (IsElementary.empty d)]
             exact IsElementary.measure_of_empty d
          rw [h_sets_eq]

          -- 4. Use sum_image
          rw [Finset.sum_image]
          · -- Match terms
            apply Finset.sum_congr rfl
            intro B hB
            dsimp [vol]
            rw [dif_pos (IsElementary.box B)]
            exact IsElementary.measure_of_box B
          · -- Injectivity
            intro B₁ hB₁ B₂ hB₂ h_eq
            simp [S'] at hB₁ hB₂
            -- Use helper lemma: Box.toSet is injective for non-empty boxes
            exact Box.toSet_injective_of_nonempty hB₁.2 hB₂.2 h_eq
        calc hA_elem.measure
          _ = (IsElementary.union' hS_elem).measure := h_eq
          _ ≤ ∑ E : S_sets, (hS_elem E.val E.property).measure := h1
          _ = ∑ B ∈ S, |B|ᵥ := h2
      linarith

  -- Part 2 (≥): sInf of box covers ≤ Jordan_outer_measure E
  · -- For any elementary A ⊇ E, show sInf(box covers) ≤ hA.measure
    unfold Jordan_outer_measure
    apply le_csInf
    -- Show the set of elementary cover measures is nonempty
    · obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
      use hA.measure
      use A, hA, hE_sub_A
    -- Show sInf(box covers) is a lower bound for all elementary cover measures
    · intro m hm
      obtain ⟨A, hA, hE_sub_A, rfl⟩ := hm
      -- Get partition T of A
      obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
      -- T is a box cover: E ⊆ A = ⋃ B ∈ T
      have hT_cover : E ⊆ ⋃ B ∈ T, B.toSet := hA_eq ▸ hE_sub_A
      -- T.sum volume = hA.measure
      have hT_sum : ∑ B ∈ T, |B|ᵥ = hA.measure := by
        symm; exact hA.measure_eq hT_disj hA_eq
      -- sInf(box covers) ≤ ∑ B ∈ T, |B|ᵥ (since T is a box cover)
      have h_inf_le : sInf (((fun S: Finset (Box d) ↦ ∑ B ∈ S, |B|ᵥ)) '' { S | E ⊆ ⋃ B ∈ S, B.toSet }) ≤ ∑ B ∈ T, |B|ᵥ := by
        apply csInf_le
        -- Show box covers set is bounded below
        · use 0
          intro m' hm'
          obtain ⟨S, _, rfl⟩ := hm'
          apply Finset.sum_nonneg
          intro B _
          rw [Box.volume]
          apply Finset.prod_nonneg
          intro i _
          rw [BoundedInterval.length]
          exact le_max_right _ _
        -- ∑ B ∈ T, |B|ᵥ is in the box covers set
        · show ∑ B ∈ T, |B|ᵥ ∈ (fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet}
          simp
          exact ⟨T, hT_cover, rfl⟩
      -- Combine: sInf(box covers) ≤ ∑ B ∈ T, |B|ᵥ = hA.measure
      rw [←hT_sum]; exact h_inf_le

noncomputable def Lebesgue_outer_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : EReal :=
  sInf (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet })

/-- Coercion ℝ → EReal preserves infimums for nonempty bounded-below sets -/
lemma EReal.sInf_image_coe {s : Set ℝ} (hs : s.Nonempty) (h_bdd : BddBelow s) :
    sInf ((fun x : ℝ => (x : EReal)) '' s) = ↑(sInf s) := by
  -- Strategy: Show both ≤ directions using sInf properties
  apply le_antisymm

  -- Part 1: sInf(↑''s) ≤ ↑(sInf s)
  · -- Key: sInf(↑''s) is a lower bound for ↑''s, so sInf(↑''s) ≤ ↑x for all x ∈ s
    -- We want to show this implies sInf(↑''s) ≤ ↑(sInf s)
    -- Case analysis on whether sInf(↑''s) is ⊥ or a real
    by_cases h_bot : sInf ((fun y : ℝ => (y : EReal)) '' s) = ⊥
    · rw [h_bot]; exact bot_le
    · -- sInf(↑''s) is bounded below (since s is), so it's not ⊥ or ⊤
      -- We have: ∀ x ∈ s, sInf(↑''s) ≤ ↑x
      have h_le_all : ∀ x ∈ s, sInf ((fun y : ℝ => (y : EReal)) '' s) ≤ ↑x := by
        intro x hx; apply sInf_le; exact ⟨x, hx, rfl⟩
      -- Since s is bounded below, there exists m such that m ≤ x for all x ∈ s
      -- This means ↑m is a lower bound for ↑''s, so ↑m ≤ sInf(↑''s)
      -- Combined with sInf(↑''s) ≤ ↑x for all x, we get that sInf(↑''s) is in [↑m, ↑x₀]
      -- where x₀ ∈ s, hence sInf(↑''s) must be a casted real
      -- Then we can extract r := (sInf(↑''s)).toReal and show r ≤ sInf s
      obtain ⟨m, hm⟩ := h_bdd
      have h_bdd_below : (m : EReal) ≤ sInf ((fun y : ℝ => (y : EReal)) '' s) := by
        apply le_sInf
        intro b hb
        obtain ⟨x, hx, rfl⟩ := hb
        exact EReal.coe_le_coe_iff.mpr (hm hx)
      -- Now sInf(↑''s) ∈ [↑m, ↑x₀], so it's a casted real
      -- We want: sInf(↑''s) ≤ ↑(sInf s)
      -- Strategy: Show sInf(↑''s) ≤ ↑x for all x ∈ s, then take inf over x
      -- Apply le_csInf: to show a ≤ sInf s, prove a is a lower bound for s
      obtain ⟨x₀, hx₀⟩ := hs
      have h_le_x0 : sInf ((fun y : ℝ => (y : EReal)) '' s) ≤ ↑x₀ := h_le_all x₀ hx₀
      -- sInf(↑''s) is in [↑m, ↑x₀], so it must be a casted real
      have h_exists_r : ∃ r : ℝ, sInf ((fun y : ℝ => (y : EReal)) '' s) = ↑r := by
        -- Use that sInf(↑''s) is bounded: ↑m ≤ sInf(↑''s) ≤ ↑x₀
        -- If sInf(↑''s) = ⊤, then ↑x₀ ≥ ⊤, contradicting that x₀ is real
        by_cases h_top : sInf ((fun y : ℝ => (y : EReal)) '' s) = ⊤
        · -- Get contradiction: ↑x₀ ≥ ⊤
          have : (x₀ : EReal) ≥ ⊤ := by rw [←h_top]; exact h_le_x0
          simp at this
        · -- sInf(↑''s) is not ⊥ (from h_bot) and not ⊤ (from h_top)
          -- So it must be a casted real
          -- Use EReal trichotomy: either ⊥, ⊤, or casted real
          have h_cases := EReal.def (sInf ((fun y : ℝ => (y : EReal)) '' s))
          cases h_cases with
          | inl h => obtain ⟨r, hr⟩ := h; exact ⟨r, hr.symm⟩
          | inr h => cases h with
            | inl h_eq_top => exact absurd h_eq_top h_top
            | inr h_eq_bot => exact absurd h_eq_bot h_bot
      obtain ⟨r, hr⟩ := h_exists_r
      rw [hr]
      -- Now show: ↑r ≤ ↑(sInf s), i.e., r ≤ sInf s
      apply EReal.coe_le_coe_iff.mpr
      -- Show r ≤ sInf s by showing r is a lower bound for s
      have hs' : s.Nonempty := ⟨x₀, hx₀⟩
      apply le_csInf hs'
      intro x hx
      -- Show r ≤ x for all x ∈ s
      -- We have ↑r = sInf(↑''s) ≤ ↑x
      have : (r : EReal) ≤ ↑x := by rw [←hr]; exact h_le_all x hx
      exact EReal.coe_le_coe_iff.mp this

  -- Part 2: ↑(sInf s) ≤ sInf(↑''s)
  -- Show that ↑(sInf s) is a lower bound for ↑''s
  · apply le_sInf
    intro b hb
    obtain ⟨x, hx_in_s, rfl⟩ := hb
    -- Show: ↑(sInf s) ≤ ↑x
    apply EReal.coe_le_coe_iff.mpr
    -- Show: sInf s ≤ x (true since x ∈ s and sInf s is a lower bound)
    exact csInf_le h_bdd hx_in_s

/-- When enumerating a finset to a sequence padded with empty boxes,
    the infinite sum of volumes equals the finite sum -/
lemma tsum_volume_finset_eq {d : ℕ} (hd : 0 < d) (S : Finset (Box d)) :
    let S_list := S.toList
    let zero_box : Box d := ⟨fun i => if i.val = 0 then ∅ else BoundedInterval.Icc 0 0⟩
    let S_seq : ℕ → Box d := fun n =>
      if h : n < S_list.length then S_list.get ⟨n, h⟩ else zero_box
    ∑' n, (S_seq n).volume.toEReal = (∑ B ∈ S, |B|ᵥ).toEReal := by
  -- Strategy: zero_box has volume 0 (first side is empty), so tsum = sum over finite range
  -- Then relate finite range sum to finset sum via list enumeration
  intro S_list zero_box S_seq

  -- Step 1: Show zero_box has volume 0
  have h_zero_vol : |zero_box|ᵥ = 0 := by
    unfold Box.volume zero_box
    simp only
    -- The first side (index 0) is empty, so product is 0
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hd⟩ : Fin d))
    simp only [ite_true]
    simp [BoundedInterval.length]

  -- Step 2: Use tsum_eq_sum to convert infinite sum to finite sum
  have h_tsum_eq : ∑' n, (S_seq n).volume.toEReal = ∑ n ∈ Finset.range S_list.length, (S_seq n).volume.toEReal := by
    apply tsum_eq_sum
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    unfold S_seq
    rw [dif_neg (not_lt_of_ge hn)]
    simp [h_zero_vol]

  -- Step 3: Relate finset.range sum to finset S sum
  rw [h_tsum_eq]
  suffices h : (∑ n ∈ Finset.range S_list.length, (S_seq n).volume) = (∑ B ∈ S, |B|ᵥ) by
    calc ∑ n ∈ Finset.range S_list.length, (S_seq n).volume.toEReal
        = ∑ n ∈ Finset.range S_list.length, ((S_seq n).volume : EReal) := rfl
      _ = (∑ n ∈ Finset.range S_list.length, (S_seq n).volume : ℝ).toEReal := by
        -- Coercion ℝ → EReal commutes with Finset.sum
        -- This follows from EReal.coe_add: (x + y : EReal) = (x : EReal) + (y : EReal)
        -- Prove by induction: empty sum is 0, and for cons, use EReal.coe_add and induction hypothesis
        refine Finset.cons_induction (by simp) ?_ (Finset.range S_list.length)
        intro a s ha ih
        rw [Finset.sum_cons ha]
        conv_rhs => rw [Finset.sum_cons ha, EReal.coe_add]
        -- Now: ↑(S_seq a).volume + ∑ x ∈ s, ↑(S_seq x).volume = ↑(S_seq a).volume + ↑(∑ x ∈ s, (S_seq x).volume)
        -- Use ih: ∑ x ∈ s, ↑(S_seq x).volume = ↑(∑ x ∈ s, (S_seq x).volume)
        rw [ih]
      _ = (∑ B ∈ S, |B|ᵥ).toEReal := by rw [h]

  -- Prove: ∑ n ∈ Finset.range S_list.length, (S_seq n).volume = ∑ B ∈ S, |B|ᵥ
  -- Use Finset.sum_bij to establish bijection between indices and finset elements
  -- sum_bij: (i : α → β) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, g (i a) = f a)
  --          (hg : ∀ b ∈ t, ∃ a ∈ s, i a = b) (hh : ∀ a₁ a₂ ∈ s, i a₁ = i a₂ → a₁ = a₂)
  refine Finset.sum_bij (fun n hn => S_list.get ⟨n, Finset.mem_range.mp hn⟩) ?_ ?_ ?_ ?_
  · -- hi: Image is in S
    intro n hn
    have hn_lt := Finset.mem_range.mp hn
    have : S_list.get ⟨n, hn_lt⟩ ∈ S_list := List.get_mem S_list ⟨n, hn_lt⟩
    exact Finset.mem_toList.mp this
  · -- i_inj: Injectivity
    intro n₁ hn₁ n₂ hn₂ heq
    have hn₁_lt := Finset.mem_range.mp hn₁
    have hn₂_lt := Finset.mem_range.mp hn₂
    -- List.get is injective when the list has no duplicates (which holds for Finset.toList)
    -- From heq: S_list[n₁] = S_list[n₂], and S_list.Nodup, deduce n₁ = n₂
    have h_nodup : S_list.Nodup := Finset.nodup_toList S
    -- Simplify heq to get S_list.get ⟨n₁, hn₁_lt⟩ = S_list.get ⟨n₂, hn₂_lt⟩
    have h_get_eq : S_list.get ⟨n₁, hn₁_lt⟩ = S_list.get ⟨n₂, hn₂_lt⟩ := by
      simp at heq
      exact heq
    -- Use nodup to show the indices are equal
    -- List.nodup_iff_injective_get: Nodup l ↔ Function.Injective l.get
    have h_inj : Function.Injective S_list.get := List.nodup_iff_injective_get.mp h_nodup
    -- Apply injectivity: S_list.get ⟨n₁, hn₁_lt⟩ = S_list.get ⟨n₂, hn₂_lt⟩ implies ⟨n₁, hn₁_lt⟩ = ⟨n₂, hn₂_lt⟩
    have h_idx_eq : (⟨n₁, hn₁_lt⟩ : Fin S_list.length) = ⟨n₂, hn₂_lt⟩ := h_inj h_get_eq
    exact congrArg Fin.val h_idx_eq
  · -- i_surj: Surjectivity
    intro b hb
    obtain ⟨i, hi⟩ := List.get_of_mem (Finset.mem_toList.mpr hb)
    -- hi : S.toList.get i = b, and S_list = S.toList, so S_list.get i = b
    -- We need to show (fun n hn ↦ S_list.get ⟨n, ⋯⟩) i.val ... = b
    -- Since i : Fin S_list.length, we have S_list.get ⟨i.val, i.isLt⟩ = S_list.get i = b
    have h_eq : (fun n hn => S_list.get ⟨n, Finset.mem_range.mp hn⟩) i.val (Finset.mem_range.mpr i.isLt) = b := by
      simp
      -- S_list = S.toList, so S_list.get i = S.toList.get i = b
      rw [←hi]
      rfl
    exact ⟨i.val, Finset.mem_range.mpr i.isLt, h_eq⟩
  · -- h: Function preserves summand
    intro n hn
    have hn_lt := Finset.mem_range.mp hn
    simp only [S_seq, dif_pos hn_lt]


theorem Lebesgue_outer_measure_le_Jordan {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Lebesgue_outer_measure E ≤ Jordan_outer_measure E := by
  -- Strategy: Use Jordan_outer_eq to rewrite Jordan outer measure as infimum over finite box covers.
  -- Then apply le_csInf: show Lebesgue outer measure is a lower bound for all finite cover sums.
  -- For any finite cover S : Finset (Box d), convert it to countable sequence S_seq : ℕ → Box d
  -- (enumerate S, pad with zero-volume boxes). Show:
  --   1. E ⊆ ⋃ n, (S_seq n).toSet (covering preserved)
  --   2. ∑' n, (S_seq n).volume.toEReal = ∑ B ∈ S, |B|ᵥ (via tsum_eq_sum)
  --   3. Apply infimum property: Lebesgue ≤ tsum = finite sum

  -- For d = 0: Fin 0 is empty, so ∏ over Fin 0 = 1 for any box
  -- However, Box.toSet for d=0 is Set.univ.pi over empty index set = singleton {default}

  -- Check if we need special handling for d = 0
  by_cases hd : d = 0
  · subst hd
    -- Challenge: Cannot use Box.volume_eq_zero_of_empty because:
    --   - That lemma requires B.toSet = ∅
    --   - But for d=0, Set.univ.pi over Fin 0 is NEVER empty (always {default})
    sorry

  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd

  -- Rewrite Jordan outer measure using Jordan_outer_eq
  rw [Jordan_outer_eq hE]
  unfold Lebesgue_outer_measure

  -- Show sInf (countable covers) ≤ (finite cover sum : EReal) for all finite covers
  -- This implies sInf (countable) ≤ sInf (finite)
  have h_le : ∀ m ∈ (fun S ↦ (∑ B ∈ S, |B|ᵥ : ℝ)) '' {S | E ⊆ ⋃ B ∈ S, B.toSet},
      sInf (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet }) ≤ (m : EReal) := by
    intro m hm
    obtain ⟨S, hS_cover, rfl⟩ := hm

    -- Convert finite cover S to countable sequence S_seq
    classical
    let S_list := S.toList
    let zero_box : Box d := ⟨fun i => if i.val = 0 then ∅ else BoundedInterval.Icc 0 0⟩
    have h_card_eq : S_list.length = S.card := Finset.length_toList S
    let S_seq : ℕ → Box d := fun n =>
      if h : n < S_list.length then S_list.get ⟨n, h⟩ else zero_box

    -- Step 1: Covering is preserved
    have h_cover : E ⊆ ⋃ n, (S_seq n).toSet := by
      intro x hx
      -- Need to show: x ∈ ⋃ n, (S_seq n).toSet, i.e., ∃ n, x ∈ (S_seq n).toSet
      simp only [Set.mem_iUnion]
      -- hS_cover : E ⊆ ⋃ B ∈ S, B.toSet, so x is in some box B ∈ S
      have : x ∈ ⋃ B ∈ S, B.toSet := hS_cover hx
      simp only [Set.mem_iUnion] at this
      obtain ⟨B, hB_in_S, hx_in_B⟩ := this
      -- Since B ∈ S, it appears in S_list at some index
      have hB_in_list : B ∈ S_list := Finset.mem_toList.mpr hB_in_S
      -- Get the index i where S_list contains B
      obtain ⟨i, hi_eq⟩ := List.get_of_mem hB_in_list
      -- Provide i.val as the witness
      use i.val
      -- S_seq i.val = S_list.get ⟨i.val, i.isLt⟩ = B by hi_eq
      simp only [S_seq]
      have hi_val_lt : i.val < S_list.length := i.isLt
      rw [dif_pos hi_val_lt]
      -- Show ⟨i.val, hi_val_lt⟩ = i so we can use hi_eq
      have : (⟨i.val, hi_val_lt⟩ : Fin S_list.length) = i := Fin.ext rfl
      rw [this, hi_eq]
      exact hx_in_B

    -- Step 2: Sum equality via tsum_eq_sum
    have h_sum_eq : ∑' n, (S_seq n).volume.toEReal = (∑ B ∈ S, |B|ᵥ).toEReal := by
      exact tsum_volume_finset_eq hd_pos S

    -- Step 3: Apply infimum property
    calc sInf (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet })
        ≤ ∑' n, (S_seq n).volume.toEReal := by
            apply sInf_le
            use S_seq
            exact ⟨h_cover, rfl⟩
        _ = (∑ B ∈ S, |B|ᵥ).toEReal := h_sum_eq

  -- Use h_le to show sInf (countable) ≤ sInf (finite)
  -- We have: ∀ m ∈ finite_set, Lebesgue_sInf ≤ ↑m
  -- We need to show: Lebesgue_sInf ≤ ↑(sInf finite_set)
  -- Since finite_set is nonempty and sInf finite_set is the greatest lower bound,
  -- it suffices to show Lebesgue_sInf ≤ ↑m for all m in finite_set
  have h_nonempty : ((fun S ↦ (∑ B ∈ S, |B|ᵥ : ℝ)) '' {S | E ⊆ ⋃ B ∈ S, B.toSet}).Nonempty := by
    obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
    obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
    use (∑ B ∈ T, |B|ᵥ : ℝ)
    use T
    simp
    intro a ha
    have : a ∈ A := hE_sub_A ha
    rw [hA_eq] at this
    exact this
  -- The goal is to show: Lebesgue_sInf ≤ ↑(sInf(finite))
  -- We have h_le showing: ∀ m ∈ finite_set, Lebesgue_sInf ≤ ↑m
  -- Key insight: ↑(sInf finite_set) = sInf (↑ '' finite_set) (monotone coercion preserves sInf)
  -- Then use le_sInf: if a ≤ b for all b ∈ s, then a ≤ sInf s

  -- First, show that sInf(countable) ≤ sInf(↑ '' finite_set)
  have h_le_coe : sInf (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet })
      ≤ sInf ((fun m : ℝ => (m : EReal)) '' ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet})) := by
    apply le_sInf
    intro b hb
    obtain ⟨m, hm_in, rfl⟩ := hb
    exact h_le m hm_in

  -- Now show that sInf(↑ '' finite_set) = ↑(sInf finite_set) and apply h_le_coe
  -- The set of volumes is bounded below by 0
  have h_bdd : BddBelow ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet}) := by
    use 0
    intro m hm
    obtain ⟨S, _, rfl⟩ := hm
    apply Finset.sum_nonneg
    intro B _
    -- Box volume is a product of interval lengths, which are nonnegative by definition
    simp only [Box.volume]
    apply Finset.prod_nonneg
    intro i _
    simp [BoundedInterval.length]

  -- Apply transitivity: Lebesgue_sInf ≤ sInf(↑ '' finite) = ↑(sInf finite)
  calc sInf (((fun S: ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet })
      ≤ sInf ((fun m : ℝ => (m : EReal)) '' ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet})) := h_le_coe
      _ = ↑(sInf ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet})) := by
          -- Use helper lemma: EReal.sInf_image_coe
          exact EReal.sInf_image_coe h_nonempty h_bdd

/-- Example 1.2.1.  With the junk value conventions of this companion, the Jordan outer measure of the rationals is zero rather than infinite (I think). -/
example {R:ℝ} (hR: 0 < R) : Jordan_outer_measure (Real.equiv_EuclideanSpace' '' (Set.Icc (-R) R ∩ Set.range (fun q:ℚ ↦ (q:ℝ)))) = 2*R := by
  sorry

theorem Countable.Lebesgue_measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: E.Countable) : Lebesgue_outer_measure E = 0 := by
  sorry

example {R:ℝ} (hR: 0 < R) : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' (Set.Icc (-R) R ∩ Set.range (fun q:ℚ ↦ (q:ℝ)))) = 0 := by
  sorry

example {R:ℝ} (hR: 0 < R) : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' (Set.range (fun q:ℚ ↦ (q:ℝ)))) = 0 := by
  sorry

def LebesgueMeasurable {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop :=
  ∀ ε > 0, ∃ U: Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure (U \ E) ≤ ε

noncomputable def Lebesgue_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : EReal := Lebesgue_outer_measure E
