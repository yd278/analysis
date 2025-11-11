import Analysis.MeasureTheory.Notation
import Analysis.Section_9_1

/-!
# Introduction to Measure Theory, Section 1.1.1: Elementary measure

A companion to Section 1.1.1 of the book "An introduction to Measure Theory".

-/

/- Definition 1.1.1.  (Intervals) We use the same formalization of intervals used in
Chapter 11 of "Analysis I".  Following the usual Lean preference to admit `junk` values,
we allow for the possibility that `b < a`. -/
inductive BoundedInterval where
  | Ioo (a b:ℝ) : BoundedInterval
  | Icc (a b:ℝ) : BoundedInterval
  | Ioc (a b:ℝ) : BoundedInterval
  | Ico (a b:ℝ) : BoundedInterval

open BoundedInterval

@[coe]
def BoundedInterval.toSet (I: BoundedInterval) : Set ℝ := match I with
  | Ioo a b => .Ioo a b
  | Icc a b => .Icc a b
  | Ioc a b => .Ioc a b
  | Ico a b => .Ico a b

instance BoundedInterval.inst_coeSet : Coe BoundedInterval (Set ℝ) where
  coe := toSet

instance BoundedInterval.instEmpty : EmptyCollection BoundedInterval where
  emptyCollection := Ioo 0 0

@[simp]
theorem BoundedInterval.coe_empty : ((∅ : BoundedInterval):Set ℝ) = ∅ := by
  simp [toSet]

open Classical in
/-- This is to make Finsets of BoundedIntervals work properly -/
noncomputable instance BoundedInterval.decidableEq : DecidableEq BoundedInterval := instDecidableEqOfLawfulBEq

@[simp]
theorem BoundedInterval.set_Ioo (a b:ℝ) : (Ioo a b : Set ℝ) = .Ioo a b := by rfl

@[simp]
theorem BoundedInterval.set_Icc (a b:ℝ) : (Icc a b : Set ℝ) = .Icc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ioc (a b:ℝ) : (Ioc a b : Set ℝ) = .Ioc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ico (a b:ℝ) : (Ico a b : Set ℝ) = .Ico a b := by rfl

/-- Some helpful general lemmas about BoundedInterval -/
theorem Bornology.IsBounded.of_boundedInterval (I: BoundedInterval) : Bornology.IsBounded (I:Set ℝ) := by
  cases I with
  | Ioo a b =>
    simp [set_Ioo]
    exact Metric.isBounded_Ioo a b
  | Icc a b =>
    simp [set_Icc]
    exact Metric.isBounded_Icc a b
  | Ioc a b =>
    simp [set_Ioc]
    exact Metric.isBounded_Ioc a b
  | Ico a b =>
    simp [set_Ico]
    exact Metric.isBounded_Ico a b

/-- Helper lemma for BoundedInterval.ordConnected_iff:
If x < sSup X, then there exists z ∈ X with x < z -/
theorem exists_gt_of_lt_csSup {X : Set ℝ} (hBddAbove : BddAbove X) (hNonempty : X.Nonempty)
    (hLowerBound : ∃ y ∈ X, y ∈ lowerBounds (upperBounds X)) (x : ℝ) (hx : x < sSup X) :
    ∃ z ∈ X, x < z := by
  by_contra! h
  have : sSup X ≤ x := by
    have hx_upper : x ∈ upperBounds X := fun z hz => h z hz
    have h_bdd_below_upper : BddBelow (upperBounds X) := by
      obtain ⟨y, hy, hy_lower⟩ := hLowerBound
      exact ⟨y, hy_lower⟩
    rw [← csInf_upperBounds_eq_csSup hBddAbove hNonempty]
    exact csInf_le h_bdd_below_upper hx_upper
  linarith [this]

/-- If sInf X < x, then there exists w ∈ X with w ≤ x -/
theorem exists_le_of_lt_csInf {X : Set ℝ} (hBddBelow : BddBelow X) (hNonempty : X.Nonempty)
    (hUpperBound : ∃ y ∈ X, y ∈ upperBounds (lowerBounds X)) (x : ℝ) (hx : sInf X < x) :
    ∃ w ∈ X, w ≤ x := by
  by_contra! h
  have : x ≤ sInf X := by
    have hx_lower : x ∈ lowerBounds X := fun u hu => le_of_lt (h u hu)
    have h_bdd_above_lower : BddAbove (lowerBounds X) := by
      obtain ⟨y, hy, hy_upper⟩ := hUpperBound
      exact ⟨y, hy_upper⟩
    rw [← csSup_lowerBounds_eq_csInf hBddBelow hNonempty]
    exact le_csSup h_bdd_above_lower hx_lower
  linarith [this]

/-- Show x < b when b = sSup X and b ∉ X -/
theorem lt_sSup_of_ne_sSup {X : Set ℝ} {x b : ℝ} (_hBddAbove : BddAbove X) (_hb : b = sSup X)
    (hb_notin : b ∉ X) (hx : x ∈ X) (hx_le_b : x ≤ b) : x < b := by
  by_contra! h
  have : x = b := le_antisymm hx_le_b h
  rw [this] at hx
  exact hb_notin hx

/-- Show a < x when a = sInf X and a ∉ X -/
theorem sInf_lt_of_ne_sInf {X : Set ℝ} {a x : ℝ} (_hBddBelow : BddBelow X) (_ha : a = sInf X)
    (ha_notin : a ∉ X) (hx : x ∈ X) (ha_le_x : a ≤ x) : a < x := by
  by_contra! h
  have : x = a := le_antisymm h ha_le_x
  rw [this] at hx
  exact ha_notin hx

/-- Use order-connectedness to show x ∈ X when x ∈ [w, z] and w, z ∈ X -/
theorem mem_of_mem_Icc_ordConnected {X : Set ℝ}
    (hOrdConn : ∀ ⦃x : ℝ⦄, x ∈ X → ∀ ⦃y : ℝ⦄, y ∈ X → Set.Icc x y ⊆ X) {x w z : ℝ}
    (hw : w ∈ X) (hz : z ∈ X) (hx : x ∈ Set.Icc w z) : x ∈ X :=
  hOrdConn hw hz hx

theorem BoundedInterval.ordConnected_iff (X:Set ℝ) : Bornology.IsBounded X ∧ X.OrdConnected ↔ ∃ I: BoundedInterval, X = I := by
  constructor
  · -- Non-trivial direction: if X is bounded and order-connected, then X = I for some BoundedInterval I
    -- Strategy:
    -- 1. Handle the empty case: If X = ∅, use Ioo 0 0 (the empty interval representation)
    -- 2. For non-empty X:
    --    a. Use boundedness to show X has infimum and supremum (bounded sets in ℝ are bounded above and below)
    --    b. Extract endpoints: a = sInf X, b = sSup X
    --    c. Determine interval type based on endpoint membership:
    --       - If a ∈ X ∧ b ∈ X → use Icc a b
    --       - If a ∈ X ∧ b ∉ X → use Ico a b
    --       - If a ∉ X ∧ b ∈ X → use Ioc a b
    --       - If a ∉ X ∧ b ∉ X → use Ioo a b
    --    d. Show X equals the constructed interval:
    --       - X ⊆ interval: Use that a = sInf X and b = sSup X
    --       - interval ⊆ X: Use order-connectedness (if x, y ∈ X, then [x, y] ⊆ X)
    intro ⟨hBounded, hOrdConn⟩
    by_cases hEmpty : X = ∅
    · -- Step 1: Empty case
      use Ioo 0 0
      simp [set_Ioo]
      exact hEmpty
    · -- Step 2: Non-empty case
      have hNonempty : X.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
      -- Step 2a: Get boundedness above and below
      -- Use that bounded sets in ℝ are contained in some Icc, which gives bounds directly
      rw [Chapter9.isBounded_def] at hBounded
      obtain ⟨M, hM_pos, hX_subset⟩ := hBounded
      have hBddBelow : BddBelow X := ⟨-M, fun x hx => (hX_subset hx).1⟩
      have hBddAbove : BddAbove X := ⟨M, fun x hx => (hX_subset hx).2⟩
      -- Step 2b: Extract endpoints
      set a := sInf X
      set b := sSup X
      -- Step 2c: Determine interval type based on endpoint membership
      by_cases ha : a ∈ X
      · by_cases hb : b ∈ X
        · -- Case: a ∈ X ∧ b ∈ X → use Icc a b
          use Icc a b
          simp [set_Icc]
          ext x
          constructor
          · -- X ⊆ Icc a b
            intro hx
            simp [Set.mem_Icc]
            exact ⟨csInf_le hBddBelow hx, le_csSup hBddAbove hx⟩
          · -- Icc a b ⊆ X
            intro hx
            simp [Set.mem_Icc] at hx
            rw [Set.ordConnected_def] at hOrdConn
            have hIcc_subset : Set.Icc a b ⊆ X := hOrdConn ha hb
            exact hIcc_subset hx
        · -- Case: a ∈ X ∧ b ∉ X → use Ico a b
          use Ico a b
          simp [set_Ico]
          ext x
          constructor
          · -- X ⊆ Ico a b
            intro hx
            simp [Set.mem_Ico]
            constructor
            · exact csInf_le hBddBelow hx
            · exact lt_sSup_of_ne_sSup hBddAbove rfl hb hx (le_csSup hBddAbove hx)
          · -- Ico a b ⊆ X
            intro hx
            simp [Set.mem_Ico] at hx
            rw [Set.ordConnected_def] at hOrdConn
            -- Since x < b = sSup X, there exists z ∈ X with x < z
            have h_exists_z : ∃ z ∈ X, x < z :=
              exists_gt_of_lt_csSup hBddAbove hNonempty ⟨a, ha, by
                intro u hu
                simp [upperBounds] at hu
                exact hu ha⟩ x (by rw [←show b = sSup X from rfl]; exact hx.2)
            obtain ⟨z, hz, hxz⟩ := h_exists_z
            -- Now x ∈ [a, z] ⊆ X
            exact mem_of_mem_Icc_ordConnected hOrdConn ha hz ⟨hx.1, le_of_lt hxz⟩
      · by_cases hb : b ∈ X
        · -- Case: a ∉ X ∧ b ∈ X → use Ioc a b
          use Ioc a b
          simp [set_Ioc]
          ext x
          constructor
          · -- X ⊆ Ioc a b
            intro hx
            simp [Set.mem_Ioc]
            constructor
            · exact sInf_lt_of_ne_sInf hBddBelow rfl ha hx (csInf_le hBddBelow hx)
            · exact le_csSup hBddAbove hx
          · -- Ioc a b ⊆ X
            intro hx
            simp [Set.mem_Ioc] at hx
            rw [Set.ordConnected_def] at hOrdConn
            by_cases hx_eq_b : x = b
            · rw [hx_eq_b]; exact hb
            · -- x < b, use b as z and find w ≤ x
              have hx_lt_b : x < b := Ne.lt_of_le hx_eq_b hx.2
              -- Find w ∈ X with w ≤ x, then use [w, b]
              have h_exists_w : ∃ w ∈ X, w ≤ x :=
                exists_le_of_lt_csInf hBddBelow hNonempty ⟨b, hb, by
                  intro u hu
                  simp [lowerBounds] at hu
                  exact hu hb⟩ x (by rw [←show a = sInf X from rfl]; exact hx.1)
              obtain ⟨w, hw, hwx⟩ := h_exists_w
              -- x ∈ [w, b] ⊆ X
              exact mem_of_mem_Icc_ordConnected hOrdConn hw hb ⟨hwx, hx.2⟩
        · -- Case: a ∉ X ∧ b ∉ X → use Ioo a b
          use Ioo a b
          simp [set_Ioo]
          ext x
          constructor
          · -- X ⊆ Ioo a b
            intro hx
            simp [Set.mem_Ioo]
            constructor
            · exact sInf_lt_of_ne_sInf hBddBelow rfl ha hx (csInf_le hBddBelow hx)
            · exact lt_sSup_of_ne_sSup hBddAbove rfl hb hx (le_csSup hBddAbove hx)
          · -- Ioo a b ⊆ X
            intro hx
            simp [Set.mem_Ioo] at hx
            rw [Set.ordConnected_def] at hOrdConn
            -- Find z ∈ X with x < z and w ∈ X with w ≤ x, then use [w, z]
            have h_exists_z : ∃ z ∈ X, x < z :=
              exists_gt_of_lt_csSup hBddAbove hNonempty (by
                obtain ⟨y, hy⟩ := hNonempty
                use y, hy
                intro u hu
                simp [upperBounds] at hu
                exact hu hy) x (by rw [←show b = sSup X from rfl]; exact hx.2)
            obtain ⟨z, hz, hxz⟩ := h_exists_z
            have h_exists_w : ∃ w ∈ X, w ≤ x :=
              exists_le_of_lt_csInf hBddBelow hNonempty (by
                obtain ⟨y, hy⟩ := hNonempty
                use y, hy
                intro u hu
                simp [lowerBounds] at hu
                exact hu hy) x (by rw [←show a = sInf X from rfl]; exact hx.1)
            obtain ⟨w, hw, hwx⟩ := h_exists_w
            -- x ∈ [w, z] ⊆ X
            exact mem_of_mem_Icc_ordConnected hOrdConn hw hz ⟨hwx, le_of_lt hxz⟩
  · -- Trivial direction: if X = I for some BoundedInterval I, then X is bounded and order-connected
    intro ⟨I, hX⟩
    have hX' : X = (I : Set ℝ) := hX
    constructor
    · -- Show X is bounded
      rw [hX']
      exact Bornology.IsBounded.of_boundedInterval I
    · -- Show X is order-connected: by case analysis on the four interval types,
      -- using `Set.ordConnected_def` and proving that for any `x, y` in the interval
      -- and `z` in `[x, y]`, we have `z` in the interval
      rw [hX']
      cases I with
      | Ioo a b =>
        simp [set_Ioo]
        rw [Set.ordConnected_def]
        intro x hx y hy z hz
        simp [Set.mem_Ioo] at hx hy hz
        simp [Set.mem_Ioo]
        constructor
        · exact lt_of_lt_of_le hx.1 (hz.1)
        · exact lt_of_le_of_lt (hz.2) hy.2
      | Icc a b =>
        simp [set_Icc]
        rw [Set.ordConnected_def]
        intro x hx y hy z hz
        simp [Set.mem_Icc] at hx hy hz
        simp [Set.mem_Icc]
        constructor
        · exact le_trans hx.1 hz.1
        · exact le_trans hz.2 hy.2
      | Ioc a b =>
        simp [set_Ioc]
        rw [Set.ordConnected_def]
        intro x hx y hy z hz
        simp [Set.mem_Ioc] at hx hy hz
        simp [Set.mem_Ioc]
        constructor
        · exact lt_of_lt_of_le hx.1 hz.1
        · exact le_trans hz.2 hy.2
      | Ico a b =>
        simp [set_Ico]
        rw [Set.ordConnected_def]
        intro x hx y hy z hz
        simp [Set.mem_Ico] at hx hy hz
        simp [Set.mem_Ico]
        constructor
        · exact le_trans hx.1 hz.1
        · exact lt_of_le_of_lt hz.2 hy.2

theorem BoundedInterval.inter (I J: BoundedInterval) : ∃ K : BoundedInterval, (I:Set ℝ) ∩ (J:Set ℝ) = (K:Set ℝ) := by
  sorry

noncomputable instance BoundedInterval.instInter : Inter BoundedInterval where
  inter I J := (inter I J).choose

@[simp]
theorem BoundedInterval.inter_eq (I J: BoundedInterval) : (I ∩ J : BoundedInterval) = (I:Set ℝ) ∩ (J:Set ℝ)  :=
  (inter I J).choose_spec.symm

instance BoundedInterval.instMembership : Membership ℝ BoundedInterval where
  mem I x := x ∈ (I:Set ℝ)

@[simp]
theorem BoundedInterval.mem_iff (I: BoundedInterval) (x:ℝ) :
  x ∈ I ↔ x ∈ (I:Set ℝ) := by rfl

instance BoundedInterval.instSubset : HasSubset BoundedInterval where
  Subset I J := ∀ x, x ∈ I → x ∈ J

@[simp]
theorem BoundedInterval.subset_iff (I J: BoundedInterval) :
  I ⊆ J ↔ (I:Set ℝ) ⊆ (J:Set ℝ) := by rfl

abbrev BoundedInterval.a (I: BoundedInterval) : ℝ := match I with
  | Ioo a _ => a
  | Icc a _ => a
  | Ioc a _ => a
  | Ico a _ => a

abbrev BoundedInterval.b (I: BoundedInterval) : ℝ := match I with
  | Ioo _ b => b
  | Icc _ b => b
  | Ioc _ b => b
  | Ico _ b => b

theorem BoundedInterval.subset_Icc (I: BoundedInterval) : I ⊆ Icc I.a I.b := match I with
  | Ioo _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Icc _ _ => by simp [subset_iff]
  | Ioc _ _ => by simp [subset_iff, Set.Ioc_subset_Icc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ico_subset_Icc_self]

theorem BoundedInterval.Ioo_subset (I: BoundedInterval) : Ioo I.a I.b ⊆ I := match I with
  | Ioo _ _ => by simp [subset_iff]
  | Icc _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Ioc _ _ => by simp [subset_iff, Set.Ioo_subset_Ioc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ioo_subset_Ico_self]

/-- Definition 1.1.1 (boxes) -/
abbrev BoundedInterval.length (I: BoundedInterval) : ℝ := max (I.b - I.a) 0

/-- Using ||ₗ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ₗ" : term => `(BoundedInterval.length $a)

@[ext]
structure Box (d:ℕ) where
  side : Fin d → BoundedInterval

@[coe]
abbrev Box.toSet {d:ℕ} (B: Box d) : Set (EuclideanSpace' d) :=
  Set.univ.pi (fun i ↦ ↑(B.side i))

instance Box.inst_coeSet {d:ℕ} : Coe (Box d) (Set (EuclideanSpace' d)) where
  coe := toSet

@[coe]
abbrev BoundedInterval.toBox (I: BoundedInterval) : Box 1 where
  side := fun _ ↦ I

instance BoundedInterval.inst_coeBox : Coe (BoundedInterval) (Box 1) where
  coe := toBox

@[simp]
theorem BoundedInterval.toBox_inj {I J: BoundedInterval} : (I:Box 1) = (J:Box 1) ↔ I = J := by
  refine' ⟨fun h => _, fun h => h ▸ rfl⟩
  have : (I:Box 1).side 0 = (J:Box 1).side 0 := by rw [h]
  exact this

@[simp]
theorem BoundedInterval.coe_of_box (I:BoundedInterval) : (I:Box 1).toSet = Real.equiv_EuclideanSpace' '' I.toSet := by
  ext x
  simp [Box.toSet]; rw [Set.mem_pi]; constructor
  . intro h; use x 0; simp [h 0]
    ext ⟨ i, hi ⟩; have : i=0 := by omega
    subst this; simp
  rintro ⟨ y, hy, rfl ⟩ ⟨ i, hi ⟩ _
  have : i=0 := by omega
  grind

/-- Definition 1.1.1 (boxes)-/
abbrev Box.volume {d:ℕ} (B: Box d) : ℝ := ∏ i, |B.side i|ₗ

/-- Using ||ᵥ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ᵥ" : term => `(Box.volume $a)

@[simp]
theorem Box.volume_of_interval (I:BoundedInterval) : |(I:Box 1)|ᵥ = |I|ₗ := by
  simp [Box.volume]

abbrev IsElementary {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := ∃ S : Finset (Box d), E = ⋃ B ∈ S, ↑B

theorem IsElementary.box {d:ℕ} (B: Box d) : IsElementary B.toSet := by sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.union {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E ∪ F) := by
  sorry

lemma IsElementary.union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, IsElementary E) : IsElementary (⋃ E ∈ S, E) := by sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.inter {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E ∩ F) := by
  sorry

theorem IsElementary.empty (d:ℕ) : IsElementary (∅: Set (EuclideanSpace' d)) := by
  sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.sdiff {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E \ F) := by
  sorry

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.symmDiff {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (symmDiff E F) := by
  sorry

open Pointwise

/-- Exercise 1.1.1 (Boolean closure) -/
theorem IsElementary.translate {d:ℕ} {E: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (x: EuclideanSpace' d) : IsElementary (E + {x}) := by
  sorry

/-- A sublemma for proving Lemma 1.1.2(i).  It is a geometrically obvious fact but surprisingly annoying to prove formally. -/
theorem BoundedInterval.partition (S: Finset BoundedInterval) : ∃ T: Finset BoundedInterval, T.toSet.PairwiseDisjoint BoundedInterval.toSet ∧ ∀ I ∈ S, ∃ U : Set T, I = ⋃ J ∈ U, J.val.toSet := by
  let endpoints : Finset ℝ := S.image BoundedInterval.a ∪ S.image BoundedInterval.b
  have ha_mem {I:BoundedInterval} (hI: I ∈ S) : I.a ∈ endpoints := by grind
  have hb_mem {I:BoundedInterval} (hI: I ∈ S) : I.b ∈ endpoints := by grind
  let k := endpoints.card
  let sorted : Fin k ≃o endpoints := endpoints.orderIsoOfFin (by rfl)
  let a : ℕ → ℝ := fun n ↦ if h:n < k then sorted ⟨n,h⟩ else 0  -- 0 is a junk value
  let T := Finset.univ.image (fun x:endpoints ↦ Icc x x)
    ∪ (Finset.range (k-1)).image (fun n ↦ Ioo (a n) (a (n+1)))
  refine' ⟨T,_,_⟩
  . rw [Set.pairwiseDisjoint_iff]
    intro I hI J hJ hIJ
    have := hIJ.some_mem
    simp_all [T]
    obtain ⟨ x, hx, rfl ⟩ | ⟨ n, hn, rfl ⟩ := hI
      <;> obtain ⟨ y, hy, rfl ⟩ | ⟨ m, hm, rfl ⟩ := hJ
      <;> simp at this
    . rw [show x=y by grind]
    . rw [this.1] at this
      set n := sorted.symm ⟨ x, hx ⟩
      have hax : x = sorted n := by simp [n]
      obtain ⟨ n, hn ⟩ := n
      simp [a, show m < k by omega, show m+1 < k by omega, hax] at this
      omega
    . rw [this.2] at this
      set m := sorted.symm ⟨ y, hy ⟩
      have hay : y = sorted m := by simp [m]
      obtain ⟨ m, hm ⟩ := m
      simp [a, show n < k by omega, show n+1 < k by omega, hay] at this
      omega
    have h1 : a n < a (m+1) := this.1.1.trans this.2.2
    have h2 : a m < a (n+1) := this.2.1.trans this.1.2
    simp [a, show n < k by omega, show n+1 < k by omega,
          show m < k by omega, show m+1 < k by omega] at h1 h2
    rw [show n=m by omega]
  intro I hI
  use {J | J.val ⊆ I }
  ext x; simp; constructor
  . intro hx
    by_cases hend : x ∈ endpoints
    . use Icc x x; simp [T, hx, hend]
    let n := sorted.symm ⟨ I.a, ha_mem hI ⟩
    let m := sorted.symm ⟨ I.b, hb_mem hI ⟩
    have hnI : I.a = sorted n := by simp [n]
    have hmI : I.b = sorted m := by simp [m]
    obtain ⟨ m, hm ⟩ := m; obtain ⟨ n, hn ⟩ := n
    apply I.subset_Icc at hx
    simp [hnI, hmI] at hx
    obtain ⟨ hx1, hx2 ⟩ := hx
    have H : ∃ m, x ≤ a m := by use m; grind
    let r := Nat.find H
    have hrm : r ≤ m := by convert Nat.find_min' H _; grind
    have hr : r < k := by linarith
    have hxr : x ≤ sorted ⟨ r, hr ⟩ := by convert Nat.find_spec H; grind
    have hnr : n < r := by
      by_contra!
      replace : (sorted ⟨r, hr⟩).val ≤ (sorted ⟨n, hn⟩).val := by simp [this]
      simp [show x = sorted ⟨ n, hn ⟩ by order] at hend
    refine' ⟨ Ioo (sorted ⟨ r-1, by omega ⟩) (sorted ⟨ r, hr ⟩), _ , _, _ ⟩
    . apply Set.Subset.trans _ I.Ioo_subset
      simp [hnI, hmI]
      apply Set.Ioo_subset_Ioo <;> simp <;> omega
    . simp [T]; refine' ⟨ r-1, by omega, _ ⟩
      simp [a, show r-1 < k by omega, show r < k by omega, show r-1+1=r by omega]
    simp
    have h1 : x ≠ sorted ⟨ r, hr ⟩ := by by_contra!; simp [this] at hend
    have h3 : sorted ⟨ r-1, by omega ⟩ < x := by
      by_contra!
      convert Nat.find_min H (show r-1 < r by omega) _
      simp [a, show r-1 < k by omega, this]
    grind
  grind

/-- Lemma 1.1.2(i) -/
theorem Box.partition {d:ℕ} (S: Finset (Box d)) : ∃ T: Finset (Box d), T.toSet.PairwiseDisjoint Box.toSet ∧ ∀ I ∈ S, ∃ U : Set T, I = ⋃ J ∈ U, J.val.toSet := by
  choose T hTdisj hT using BoundedInterval.partition
  let J : Fin d → Finset BoundedInterval := fun i ↦ T (S.image (fun B ↦ B.side i))
  have hJdisj (i:Fin d) : (J i).toSet.PairwiseDisjoint BoundedInterval.toSet :=
    hTdisj (S.image (fun B ↦ B.side i))
  have hJ (i:Fin d) {B: Box d} (hB: B ∈ S) : ∃ U : Set (J i), B.side i = ⋃ K ∈ U, K.val.toSet := by
    apply hT (S.image (fun B ↦ B.side i)) (B.side i); simp; use B
  classical
  refine' ⟨ (Finset.univ.pi J).image (fun I ↦ ⟨ fun i ↦ I i (by simp) ⟩ ) , _, _ ⟩
  . rw [Set.pairwiseDisjoint_iff]
    intro B₁ hB₁ B₂ hB₂ hB₁B₂; simp at hB₁ hB₂
    obtain ⟨ J₁, hJ₁, rfl ⟩ := hB₁
    obtain ⟨ J₂, hJ₂, rfl ⟩ := hB₂
    ext i; simp
    have := hB₁B₂.some_mem
    simp [Box.toSet] at this
    rw [Set.mem_pi, Set.mem_pi] at this
    obtain ⟨ h₁, h₂ ⟩ := this
    specialize hJdisj i; rw [Set.pairwiseDisjoint_iff] at hJdisj
    apply_rules [hJdisj, Set.nonempty_of_mem (x := (hB₁B₂.some i))]
    grind
  intro B hB
  choose U hU using hJ
  use {B' | ∀ i, ∃ hi : B'.val.side i ∈ J i, ⟨ _, hi ⟩ ∈ U i hB}
  ext; simp [Box.toSet]; rw [Set.mem_pi]
  conv => lhs; intro i _; rw [hU i hB]
  conv => rhs; congr; intro a; rhs; rw [Set.mem_pi]
  simp; constructor
  . intro h; choose I hI using h
    refine' ⟨ ⟨ I ⟩, ⟨ ⟨ fun i _ ↦ I i, _⟩, _ ⟩, _ ⟩ <;> grind
  rintro ⟨ B', ⟨ h1, h2 ⟩, h3 ⟩ i; use B'.side i
  aesop

theorem IsElementary.partition {d:ℕ} {E: Set (EuclideanSpace' d)}
(hE: IsElementary E) : ∃ T: Finset (Box d), T.toSet.PairwiseDisjoint Box.toSet ∧ E = ⋃ J ∈ T, J.toSet := by
  obtain ⟨ S, rfl ⟩ := hE
  have ⟨ T', hT', hST' ⟩ := Box.partition S
  choose U hU using hST'
  conv => rhs; ext T; rhs; lhs; rhs; ext B; rhs; ext h; rw [hU B h]
  classical
  use T'.filter (fun J ↦ ∃ B, ∃ h:B ∈ S, J ∈ Subtype.val '' (U B h))
  simp; split_ands
  . apply hT'.subset; intro _; simp; tauto
  ext; simp; grind

/-- Helper lemma for Lemma 1.1.2(ii) -/
theorem BoundedInterval.sample_finite (I : BoundedInterval) {N:ℕ} (hN: N ≠ 0):
  Finite ↥(I.toSet ∩ (Set.range (fun n:ℤ ↦ (N:ℝ)⁻¹*n))) := by
  sorry

/-- Exercise for Lemma 1.1.2(ii) -/
theorem BoundedInterval.length_eq (I : BoundedInterval) :
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)⁻¹ * Nat.card ↥(I.toSet ∩ (Set.range (fun n:ℤ ↦ (N:ℝ)⁻¹*n))))
  (nhds |I|ₗ) := by
  sorry

def Box.sample_congr {d:ℕ} (B:Box d) (N:ℕ) :
↥(B.toSet ∩ (Set.range (fun (n:Fin d → ℤ) i ↦ (N:ℝ)⁻¹*(n i)))) ≃ ((i : Fin d) → ↑(↑(B.side i) ∩ Set.range fun n:ℤ ↦ (N:ℝ)⁻¹ * ↑n)) := {
    toFun x i := by
      obtain ⟨ x, hx ⟩ := x; refine ⟨ x i, ?_ ⟩
      simp [Box.toSet] at hx; rw [Set.mem_pi] at hx
      grind
    invFun x := by
      refine ⟨ fun i ↦ x i, ?_ ⟩
      simp [Box.toSet]; rw [Set.mem_pi]; split_ands
      . grind
      have h (i:Fin d) : ∃ y:ℤ, (N:ℝ)⁻¹ * y = x i := by
        obtain ⟨ x, hx ⟩ := x i; simp at hx; grind
      choose y hy using h; use y; simp [hy]
    left_inv x := by grind
    right_inv x := by aesop
  }

/-- Helper lemma for Lemma 1.1.2(ii) -/
theorem Box.sample_finite {d:ℕ} (B: Box d) {N:ℕ} (hN: N ≠ 0):
  Finite ↥(B.toSet ∩ (Set.range (fun (n:Fin d → ℤ) i ↦ (N:ℝ)⁻¹*(n i)))) := by
    rw [Equiv.finite_iff (B.sample_congr N)]
    apply @Pi.finite _ _ _ (fun i ↦ (B.side i).sample_finite hN)

/-- Helper lemma for Lemma 1.1.2(ii) -/
theorem Box.vol_eq {d:ℕ} (B: Box d):
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)^(-d:ℝ) * Nat.card ↥(B.toSet ∩ (Set.range (fun (n:Fin d → ℤ) i ↦ (N:ℝ)⁻¹*(n i)))))
  (nhds |B|ᵥ) := by
  simp [Box.volume]
  have : ∀ i ∈ Finset.univ, Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)⁻¹ * Nat.card ↥((B.side i).toSet ∩ Set.range ((fun n:ℤ ↦ (N:ℝ)⁻¹*n)))) (nhds |B.side i|ₗ) := fun i _ ↦ (B.side i).length_eq
  convert tendsto_finset_prod Finset.univ this with N
  simp [Finset.prod_mul_distrib]; left
  norm_cast; simp_rw [←Nat.card_coe_set_eq, ←Nat.card_pi]
  apply Nat.card_congr (B.sample_congr N)


/-- Lemma 1.1.2(ii), helper lemma -/
theorem Box.sum_vol_eq {d:ℕ} {T: Finset (Box d)}
 (hT: T.toSet.PairwiseDisjoint Box.toSet) :
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)^(-d:ℝ) * Nat.card ↥((⋃ B ∈ T, B.toSet) ∩ (Set.range (fun (n:Fin d → ℤ) i ↦ (N:ℝ)⁻¹*(n i)))))
  (nhds (∑ B ∈ T, |B|ᵥ)) := by
  apply (tendsto_finset_sum T (fun B _ ↦ B.vol_eq)).congr'
  rw [Filter.EventuallyEq, Filter.eventually_atTop]; use 1; intro N hN
  symm; convert Finset.mul_sum _ _ _
  convert Nat.cast_sum _ _
  rw [←Finset.sum_coe_sort, ←@Nat.card_sigma _ _ _ ?_]
  . exact Nat.card_congr {
      toFun x := by
        obtain ⟨ x, hx ⟩ := x
        simp at hx
        have hB := hx.1.choose_spec
        refine ⟨ ⟨ hx.1.choose, hB.1 ⟩, ⟨ x, ?_⟩ ⟩
        simp_all
      invFun x := by
        obtain ⟨ ⟨ B, hB ⟩, ⟨ x, hx ⟩ ⟩ := x
        refine ⟨ x, ?_ ⟩
        simp_all; aesop
      left_inv x := by grind
      right_inv x := by
        obtain ⟨ ⟨ B, hB ⟩, ⟨ x, hxB⟩ ⟩ := x
        simp at hxB
        have : ∃ B ∈ T, x ∈ B.toSet := by use B; tauto
        have h : this.choose = B := by
          have h := this.choose_spec
          apply hT.elim h.1 hB
          rw [Set.not_disjoint_iff]; grind
        simp [h, ←eq_cast_iff_heq]
    }
  intro ⟨ B, _ ⟩; convert B.sample_finite ?_
  omega

/-- Lemma 1.1.2(ii) -/
theorem Box.measure_uniq {d:ℕ} {T₁ T₂: Finset (Box d)}
 (hT₁: T₁.toSet.PairwiseDisjoint Box.toSet)
 (hT₂: T₂.toSet.PairwiseDisjoint Box.toSet)
 (heq: ⋃ B ∈ T₁, B.toSet = ⋃ B ∈ T₂, B.toSet) :
 ∑ B ∈ T₁, |B|ᵥ = ∑ B ∈ T₂, |B|ᵥ := by
  apply tendsto_nhds_unique _ (Box.sum_vol_eq hT₂)
  rw [←heq]
  exact Box.sum_vol_eq hT₁

noncomputable abbrev IsElementary.measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) : ℝ
  := ∑ B ∈ hE.partition.choose, |B|ᵥ

theorem IsElementary.measure_eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E)
  {T: Finset (Box d)} (hT: T.toSet.PairwiseDisjoint Box.toSet)
  (heq : E = ⋃ B ∈ T, B.toSet):
  hE.measure = ∑ B ∈ T, |B|ᵥ := by
  apply Box.measure_uniq hE.partition.choose_spec.1 hT _
  rw [←heq, ←hE.partition.choose_spec.2]

/-- Exercise 1.1.2: give an alternate proof of this proposition by showing that
the two partitions `T₁`, `T₂` admit a mutual refinement into boxes arising from
taking Cartesian products of elements from finite collections of disjoint intervals. -/
theorem Box.measure_uniq' {d:ℕ} {T₁ T₂: Finset (Box d)}
 (hT₁: T₁.toSet.PairwiseDisjoint Box.toSet)
 (hT₂: T₂.toSet.PairwiseDisjoint Box.toSet)
 (heq: ⋃ B ∈ T₁, B.toSet = ⋃ B ∈ T₂, B.toSet) :
 ∑ B ∈ T₁, |B|ᵥ = ∑ B ∈ T₂, |B|ᵥ := by
 sorry

example :
  let E : Set (EuclideanSpace' 1) := Real.equiv_EuclideanSpace' '' ((Set.Ioo 1 2) ∪ (Set.Icc 3 6))
  ∃ hE : IsElementary E, hE.measure = 4 := by
  extract_lets E
  classical
  let T : Finset (Box 1) := {(BoundedInterval.Ioo 1 2:Box 1), (BoundedInterval.Icc 3 6:Box 1)}
  have hET : E = ⋃ B ∈ T, B.toSet := by
    simp [E, T, Set.image_union]
  let hE : IsElementary E := ⟨ T, hET⟩
  use hE
  rw [hE.measure_eq _ hET]
  . rw [Finset.sum_pair]
    . norm_num
    by_contra!; simp [-Box.mk.injEq] at this
  rw [Set.pairwiseDisjoint_iff]
  simp [T]; split_ands <;> intro ⟨ x, hx ⟩ <;> grind

lemma IsElementary.measure_nonneg {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) :
  0 ≤ hE.measure := by
  sorry

lemma IsElementary.measure_of_disjUnion {d:ℕ} {E F: Set (EuclideanSpace' d)}
(hE: IsElementary E) (hF: IsElementary F) (hdisj: Disjoint E F):
  (hE.union hF).measure = hE.measure + hF.measure := by
  sorry

lemma IsElementary.measure_of_disjUnion' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, IsElementary E) (hdisj: S.toSet.PairwiseDisjoint id):
  (IsElementary.union' hE).measure = ∑ E:S, (hE E.val E.property).measure := by
  sorry

@[simp]
lemma IsElementary.measure_of_empty (d:ℕ) : (IsElementary.empty d).measure = 0 := by
  sorry

@[simp]
lemma IsElementary.measure_of_box {d:ℕ} (B: Box d) : (IsElementary.box B).measure = |B|ᵥ := by
  sorry

lemma IsElementary.measure_mono  {d:ℕ} {E F: Set (EuclideanSpace' d)}
(hE: IsElementary E) (hF: IsElementary F) (hcont: E ⊆ F):
  hE.measure ≤ hF.measure := by
  sorry

lemma IsElementary.measure_of_union {d:ℕ} {E F: Set (EuclideanSpace' d)}
(hE: IsElementary E) (hF: IsElementary F):
  (hE.union hF).measure ≤ hE.measure + hF.measure := by
  sorry

lemma IsElementary.measure_of_union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, IsElementary E) :
  (IsElementary.union' hE).measure ≤ ∑ E:S, (hE E.val E.property).measure := by
  sorry

lemma IsElementary.measure_of_translate {d:ℕ} {E: Set (EuclideanSpace' d)}
(hE: IsElementary E) (x: EuclideanSpace' d):
  (hE.translate x).measure ≤ hE.measure := by
  sorry

/-- Exercise 1.1.3 (uniqueness of elementary measure) -/
theorem IsElementary.measure_uniq {d:ℕ} {m': (E: Set (EuclideanSpace' d)) → (IsElementary E) → ℝ}
  (hnonneg: ∀ E: Set (EuclideanSpace' d), ∀ hE: IsElementary E, m' E hE ≥ 0)
  (hadd: ∀ E F: Set (EuclideanSpace' d), ∀ (hE: IsElementary E) (hF: IsElementary F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans: ∀ E: Set (EuclideanSpace' d), ∀ (hE: IsElementary E) (x: EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE) : ∃ c, c ≥ 0 ∧ ∀ E: Set (EuclideanSpace' d), ∀ hE: IsElementary E, m' E hE = c * hE.measure := by
    sorry

abbrev Box.unit_cube (d:ℕ) : Box d := { side := fun _ ↦ BoundedInterval.Ioc 0 1}

theorem IsElementary.measure_uniq' {d:ℕ} {m': (E: Set (EuclideanSpace' d)) → (IsElementary E) → ℝ}
  (hnonneg: ∀ E: Set (EuclideanSpace' d), ∀ hE: IsElementary E, m' E hE ≥ 0)
  (hadd: ∀ E F: Set (EuclideanSpace' d), ∀ (hE: IsElementary E) (hF: IsElementary F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans: ∀ E: Set (EuclideanSpace' d), ∀ (hE: IsElementary E) (x: EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE)
  (hcube : m' (Box.unit_cube d) (IsElementary.box _) = 1) :
  ∀ E: Set (EuclideanSpace' d), ∀ hE: IsElementary E, m' E hE = hE.measure := by
    sorry

abbrev Box.prod {d₁ d₂:ℕ} (B₁: Box d₁) (B₂: Box d₂) : Box (d₁ + d₂) where
  side i := by
    obtain ⟨ i, hi ⟩ := i
    exact if h : i < d₁ then B₁.side ⟨i, h⟩ else (B₂.side ⟨i - d₁, by omega⟩)

/-- Exercise 1.1.4 -/
theorem IsElementary.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: IsElementary E₁) (hE₂: IsElementary E₂) : IsElementary (EuclideanSpace'.prod E₁ E₂) := by sorry

theorem IsElementary.measure_of_prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: IsElementary E₁) (hE₂: IsElementary E₂)
  : (hE₁.prod hE₂).measure = hE₁.measure * hE₂.measure := by sorry
