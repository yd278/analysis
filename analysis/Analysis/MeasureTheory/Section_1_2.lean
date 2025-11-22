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

-- Helper lemma: extract endpoints from Icc equality
private lemma Icc_eq_endpoints {a₁ b₁ a₂ b₂ : ℝ}
    (h : Set.Icc a₁ b₁ = Set.Icc a₂ b₂) (ha₁b₁ : a₁ ≤ b₁) (ha₂b₂ : a₂ ≤ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · have h₁ : a₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
    rw [h] at h₁; simp [Set.mem_Icc] at h₁
    have h₂ : a₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
    rw [← h] at h₂; simp [Set.mem_Icc] at h₂
    linarith
  · have h₁ : b₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
    rw [h] at h₁; simp [Set.mem_Icc] at h₁
    have h₂ : b₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
    rw [← h] at h₂; simp [Set.mem_Icc] at h₂
    linarith

-- Helper lemma: Ioo cannot equal Icc
private lemma Ioo_ne_Icc {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ < b₁) (ha₂b₂ : a₂ ≤ b₂) :
    Set.Ioo a₁ b₁ ≠ Set.Icc a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [closure_Ioo ha₁b₁.ne, isClosed_Icc.closure_eq] at h_cl
  obtain ⟨ha, hb⟩ := Icc_eq_endpoints h_cl (le_of_lt ha₁b₁) ha₂b₂
  have : a₂ ∉ Set.Ioo a₁ b₁ := by simp [Set.mem_Ioo]; intro; linarith
  have : a₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
  rw [← h] at this
  contradiction

-- Helper lemma: Ioo cannot equal Ioc
private lemma Ioo_ne_Ioc {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ < b₁) (ha₂b₂ : a₂ < b₂) :
    Set.Ioo a₁ b₁ ≠ Set.Ioc a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [closure_Ioo ha₁b₁.ne, closure_Ioc ha₂b₂.ne] at h_cl
  obtain ⟨_, hb⟩ := Icc_eq_endpoints h_cl (le_of_lt ha₁b₁) (le_of_lt ha₂b₂)
  have : b₂ ∈ Set.Ioc a₂ b₂ := ⟨ha₂b₂, le_refl b₂⟩
  rw [← h] at this
  simp [Set.mem_Ioo] at this
  linarith

-- Helper lemma: Ioo cannot equal Ico
private lemma Ioo_ne_Ico {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ < b₁) (ha₂b₂ : a₂ < b₂) :
    Set.Ioo a₁ b₁ ≠ Set.Ico a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [closure_Ioo ha₁b₁.ne, closure_Ico ha₂b₂.ne] at h_cl
  obtain ⟨ha, _⟩ := Icc_eq_endpoints h_cl (le_of_lt ha₁b₁) (le_of_lt ha₂b₂)
  have : a₂ ∈ Set.Ico a₂ b₂ := ⟨le_refl a₂, ha₂b₂⟩
  rw [← h] at this
  simp [Set.mem_Ioo] at this
  linarith

-- Helper lemma: Ioc cannot equal Ico
private lemma Ioc_ne_Ico {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ < b₁) (ha₂b₂ : a₂ < b₂) :
    Set.Ioc a₁ b₁ ≠ Set.Ico a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [closure_Ioc ha₁b₁.ne, closure_Ico ha₂b₂.ne] at h_cl
  obtain ⟨_, hb⟩ := Icc_eq_endpoints h_cl (le_of_lt ha₁b₁) (le_of_lt ha₂b₂)
  have : b₁ ∈ Set.Ioc a₁ b₁ := ⟨ha₁b₁, le_refl b₁⟩
  rw [h] at this
  simp [Set.mem_Ico] at this
  linarith

-- Helper lemma: Icc cannot equal Ioc
private lemma Icc_ne_Ioc {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ ≤ b₁) (ha₂b₂ : a₂ < b₂) :
    Set.Icc a₁ b₁ ≠ Set.Ioc a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [isClosed_Icc.closure_eq, closure_Ioc ha₂b₂.ne] at h_cl
  obtain ⟨ha, _⟩ := Icc_eq_endpoints h_cl ha₁b₁ (le_of_lt ha₂b₂)
  have : a₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
  rw [h] at this
  simp [Set.mem_Ioc] at this
  linarith

-- Helper lemma: Icc cannot equal Ico
private lemma Icc_ne_Ico {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ ≤ b₁) (ha₂b₂ : a₂ < b₂) :
    Set.Icc a₁ b₁ ≠ Set.Ico a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [isClosed_Icc.closure_eq, closure_Ico ha₂b₂.ne] at h_cl
  obtain ⟨_, hb⟩ := Icc_eq_endpoints h_cl ha₁b₁ (le_of_lt ha₂b₂)
  have : b₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
  rw [h] at this
  simp [Set.mem_Ico] at this
  linarith

-- First prove that BoundedInterval.toSet is injective for non-empty intervals
lemma BoundedInterval.toSet_injective_of_nonempty {I J : BoundedInterval}
    (hI : I.toSet.Nonempty) (hJ : J.toSet.Nonempty) (h_eq : I.toSet = J.toSet) :
    I = J := by
  -- Case analysis on both intervals (16 cases total)
  cases I with
  | Ioo a₁ b₁ =>
    cases J with
    | Ioo a₂ b₂ =>
      -- Ioo a₁ b₁ = Ioo a₂ b₂: use that Set.Ioo is injective
      have : Set.Ioo a₁ b₁ = Set.Ioo a₂ b₂ := h_eq
      -- For non-empty open intervals, closures are equal closed intervals
      have h_closure : closure (Set.Ioo a₁ b₁) = closure (Set.Ioo a₂ b₂) := by
        rw [this]
      -- Closure of nonempty Ioo a b is Icc a b (when a < b)
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ < b₁ := hx.1.trans hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ < b₂ := hy.1.trans hy.2
      -- Use closure_Ioo from mathlib
      rw [closure_Ioo ha₁b₁.ne, closure_Ioo ha₂b₂.ne] at h_closure
      -- Now Set.Icc a₁ b₁ = Set.Icc a₂ b₂ implies a₁ = a₂ and b₁ = b₂
      have ha : a₁ = a₂ := by
        -- Show a₁ ≤ a₂ and a₂ ≤ a₁
        have h₁ : a₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁.le]
        rw [h_closure] at h₁
        simp [Set.mem_Icc] at h₁
        have h₂ : a₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂.le]
        rw [← h_closure] at h₂
        simp [Set.mem_Icc] at h₂
        linarith
      have hb : b₁ = b₂ := by
        -- Show b₁ ≤ b₂ and b₂ ≤ b₁
        have h₁ : b₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁.le]
        rw [h_closure] at h₁
        simp [Set.mem_Icc] at h₁
        have h₂ : b₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂.le]
        rw [← h_closure] at h₂
        simp [Set.mem_Icc] at h₂
        linarith
      rw [ha, hb]
    | Icc a₂ b₂ =>
      -- Ioo vs Icc: Use helper lemma
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ < b₁ := hx.1.trans hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ ≤ b₂ := hy.1.trans hy.2
      exact absurd h_eq (Ioo_ne_Icc ha₁b₁ ha₂b₂)
    | Ioc a₂ b₂ =>
      -- Ioo vs Ioc: Use helper lemma
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ < b₁ := hx.1.trans hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ < b₂ := hy.1.trans_le hy.2
      exact absurd h_eq (Ioo_ne_Ioc ha₁b₁ ha₂b₂)
    | Ico a₂ b₂ =>
      -- Ioo vs Ico: Use helper lemma
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ < b₁ := hx.1.trans hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ < b₂ := hy.1.trans_lt hy.2
      exact absurd h_eq (Ioo_ne_Ico ha₁b₁ ha₂b₂)
  | Icc a₁ b₁ =>
    cases J with
    | Ioo a₂ b₂ =>
      -- Icc vs Ioo: Use helper lemma (symmetric)
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ ≤ b₁ := hx.1.trans hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ < b₂ := hy.1.trans hy.2
      exact absurd h_eq.symm (Ioo_ne_Icc ha₂b₂ ha₁b₁)
    | Icc a₂ b₂ =>
      -- Icc a₁ b₁ = Icc a₂ b₂: directly use set equality (Icc is already closed)
      have : Set.Icc a₁ b₁ = Set.Icc a₂ b₂ := h_eq
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ ≤ b₁ := hx.1.trans hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ ≤ b₂ := hy.1.trans hy.2
      -- Extract endpoints using membership
      have ha : a₁ = a₂ := by
        have h₁ : a₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
        rw [this] at h₁; simp [Set.mem_Icc] at h₁
        have h₂ : a₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
        rw [← this] at h₂; simp [Set.mem_Icc] at h₂
        linarith
      have hb : b₁ = b₂ := by
        have h₁ : b₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
        rw [this] at h₁; simp [Set.mem_Icc] at h₁
        have h₂ : b₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
        rw [← this] at h₂; simp [Set.mem_Icc] at h₂
        linarith
      rw [ha, hb]
    | Ioc a₂ b₂ =>
      -- Icc vs Ioc: Use helper lemma
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ ≤ b₁ := hx.1.trans hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ < b₂ := hy.1.trans_le hy.2
      exact absurd h_eq (Icc_ne_Ioc ha₁b₁ ha₂b₂)
    | Ico a₂ b₂ =>
      -- Icc vs Ico: Use helper lemma
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ ≤ b₁ := hx.1.trans hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ < b₂ := hy.1.trans_lt hy.2
      exact absurd h_eq (Icc_ne_Ico ha₁b₁ ha₂b₂)
  | Ioc a₁ b₁ =>
    cases J with
    | Ioo a₂ b₂ =>
      -- Ioc vs Ioo: Use helper lemma (symmetric)
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ < b₁ := hx.1.trans_le hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ < b₂ := hy.1.trans hy.2
      exact absurd h_eq.symm (Ioo_ne_Ioc ha₂b₂ ha₁b₁)
    | Icc a₂ b₂ =>
      -- Ioc vs Icc: Use helper lemma (symmetric)
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ < b₁ := hx.1.trans_le hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ ≤ b₂ := hy.1.trans hy.2
      exact absurd h_eq.symm (Icc_ne_Ioc ha₂b₂ ha₁b₁)
    | Ioc a₂ b₂ =>
      -- Ioc a₁ b₁ = Ioc a₂ b₂: use closure like Ioo
      have : Set.Ioc a₁ b₁ = Set.Ioc a₂ b₂ := h_eq
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ < b₁ := hx.1.trans_le hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ < b₂ := hy.1.trans_le hy.2
      -- Closure of Ioc a b is Icc a b (for a < b)
      have h_closure : closure (Set.Ioc a₁ b₁) = closure (Set.Ioc a₂ b₂) := by rw [this]
      rw [closure_Ioc ha₁b₁.ne, closure_Ioc ha₂b₂.ne] at h_closure
      -- Now use Icc equality to extract endpoints
      have ha : a₁ = a₂ := by
        have h₁ : a₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁.le]
        rw [h_closure] at h₁; simp [Set.mem_Icc] at h₁
        have h₂ : a₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂.le]
        rw [← h_closure] at h₂; simp [Set.mem_Icc] at h₂
        linarith
      have hb : b₁ = b₂ := by
        have h₁ : b₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁.le]
        rw [h_closure] at h₁; simp [Set.mem_Icc] at h₁
        have h₂ : b₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂.le]
        rw [← h_closure] at h₂; simp [Set.mem_Icc] at h₂
        linarith
      rw [ha, hb]
    | Ico a₂ b₂ =>
      -- Ioc vs Ico: Use helper lemma
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ < b₁ := hx.1.trans_le hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ < b₂ := hy.1.trans_lt hy.2
      exact absurd h_eq (Ioc_ne_Ico ha₁b₁ ha₂b₂)
  | Ico a₁ b₁ =>
    cases J with
    | Ioo a₂ b₂ =>
      -- Ico vs Ioo: Use helper lemma (symmetric)
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ < b₁ := hx.1.trans_lt hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ < b₂ := hy.1.trans hy.2
      exact absurd h_eq.symm (Ioo_ne_Ico ha₂b₂ ha₁b₁)
    | Icc a₂ b₂ =>
      -- Ico vs Icc: Use helper lemma (symmetric)
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ < b₁ := hx.1.trans_lt hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ ≤ b₂ := hy.1.trans hy.2
      exact absurd h_eq.symm (Icc_ne_Ico ha₂b₂ ha₁b₁)
    | Ioc a₂ b₂ =>
      -- Ico vs Ioc: Use helper lemma (symmetric)
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ < b₁ := hx.1.trans_lt hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ < b₂ := hy.1.trans_le hy.2
      exact absurd h_eq.symm (Ioc_ne_Ico ha₂b₂ ha₁b₁)
    | Ico a₂ b₂ =>
      -- Ico a₁ b₁ = Ico a₂ b₂: use closure like Ioo
      have : Set.Ico a₁ b₁ = Set.Ico a₂ b₂ := h_eq
      obtain ⟨x, hx⟩ := hI
      simp [BoundedInterval.toSet] at hx
      have ha₁b₁ : a₁ < b₁ := hx.1.trans_lt hx.2
      obtain ⟨y, hy⟩ := hJ
      simp [BoundedInterval.toSet] at hy
      have ha₂b₂ : a₂ < b₂ := hy.1.trans_lt hy.2
      -- Closure of Ico a b is Icc a b (for a < b)
      have h_closure : closure (Set.Ico a₁ b₁) = closure (Set.Ico a₂ b₂) := by rw [this]
      rw [closure_Ico ha₁b₁.ne, closure_Ico ha₂b₂.ne] at h_closure
      -- Now use Icc equality to extract endpoints
      have ha : a₁ = a₂ := by
        have h₁ : a₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁.le]
        rw [h_closure] at h₁; simp [Set.mem_Icc] at h₁
        have h₂ : a₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂.le]
        rw [← h_closure] at h₂; simp [Set.mem_Icc] at h₂
        linarith
      have hb : b₁ = b₂ := by
        have h₁ : b₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁.le]
        rw [h_closure] at h₁; simp [Set.mem_Icc] at h₁
        have h₂ : b₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂.le]
        rw [← h_closure] at h₂; simp [Set.mem_Icc] at h₂
        linarith
      rw [ha, hb]

-- Helper lemma: Box.toSet is injective on non-empty boxes
lemma Box.toSet_injective_of_nonempty {d:ℕ} {B₁ B₂ : Box d}
    (h₁ : B₁.toSet.Nonempty) (h₂ : B₂.toSet.Nonempty) (h_eq : B₁.toSet = B₂.toSet) :
    B₁ = B₂ := by
  -- Use Box extensionality: boxes are equal if their sides are equal
  ext i
  -- From B₁.toSet = B₂.toSet, extract that B₁.side i = B₂.side i
  -- B.toSet = Set.univ.pi (fun i => (B.side i).toSet)
  -- So if the pi sets are equal, each coordinate set must be equal
  have h_side : (B₁.side i).toSet = (B₂.side i).toSet := by
    -- Use Set extensionality: show x ∈ B₁.side i ↔ x ∈ B₂.side i for all x
    ext x
    -- Get a witness function from the nonempty hypothesis
    obtain ⟨f, hf⟩ := h₁
    -- hf : f ∈ Set.univ.pi (fun j => (B₁.side j).toSet)
    simp [Box.toSet] at hf
    -- Construct a test function that equals x at coordinate i, and equals f elsewhere
    let g : Fin d → ℝ := fun j => if j = i then x else f j
    -- Show: x ∈ B₁.side i ↔ x ∈ B₂.side i
    constructor
    · intro hx
      -- g ∈ B₁.toSet because g i = x ∈ B₁.side i and g j = f j ∈ B₁.side j for j ≠ i
      have hg₁ : g ∈ B₁.toSet := by
        simp [Box.toSet, g]
        intro j _
        by_cases h : j = i
        · simp [h, hx]
        · simp [h, hf j (Set.mem_univ j)]
      -- By h_eq, g ∈ B₂.toSet
      rw [h_eq] at hg₁
      -- So g i ∈ B₂.side i, which is x
      simp [Box.toSet] at hg₁
      have := hg₁ i (Set.mem_univ i)
      simp [g] at this
      exact this
    · intro hx
      -- Symmetric argument
      obtain ⟨f₂, hf₂⟩ := h₂
      simp [Box.toSet] at hf₂
      let g₂ : Fin d → ℝ := fun j => if j = i then x else f₂ j
      have hg₂ : g₂ ∈ B₂.toSet := by
        simp [Box.toSet, g₂]
        intro j _
        by_cases h : j = i
        · simp [h, hx]
        · simp [h, hf₂ j (Set.mem_univ j)]
      rw [← h_eq] at hg₂
      simp [Box.toSet] at hg₂
      have := hg₂ i (Set.mem_univ i)
      simp [g₂] at this
      exact this
  -- Now use BoundedInterval injectivity
  have h_sides_nonempty : (B₁.side i).toSet.Nonempty ∧ (B₂.side i).toSet.Nonempty := by
    constructor
    · -- B₁.side i is nonempty because B₁.toSet is nonempty
      obtain ⟨f, hf⟩ := h₁
      simp [Box.toSet] at hf
      exact ⟨f i, hf i (Set.mem_univ i)⟩
    · -- B₂.side i is nonempty because B₂.toSet is nonempty
      obtain ⟨f, hf⟩ := h₂
      simp [Box.toSet] at hf
      exact ⟨f i, hf i (Set.mem_univ i)⟩
  exact BoundedInterval.toSet_injective_of_nonempty h_sides_nonempty.1 h_sides_nonempty.2 h_side

-- theorem Jordan_inner_eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Jordan_inner_measure E = sInf (((fun S: Finset (Box d) ↦ S.sum Box.volume)) '' { S | E ⊆ ⋃ B ∈ S, B.toSet }) := by
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

theorem Lebesgue_outer_measure_le_Jordan {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Lebesgue_outer_measure E ≤ Jordan_outer_measure E := by
  sorry

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
