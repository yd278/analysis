import Analysis.MeasureTheory.Section_1_2_1

/-!
# Introduction to Measure Theory, Section 1.2.2: Lebesgue measurability

A companion to (the introduction to) Section 1.2.2 of the book "An introduction to Measure Theory".

-/

/-- Lemma 1.2.13(i) (Every open set is Lebesgue measurable). This lemma requires proof. -/
theorem IsOpen.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsOpen E) : Lebesgue_measurable E := by
  sorry

/-- Lemma 1.2.13(ii) (Every closed set is Lebesgue measurable). This lemma requires proof. -/
theorem IsClosed.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsClosed E) : Lebesgue_measurable E := by
  sorry

abbrev IsNull {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := Lebesgue_outer_measure E = 0

/-- Lemma 1.2.13(iii) (Every null set is Lebesgue measurable).  This lemma requires proof. -/
theorem IsNull.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsNull E) : Lebesgue_measurable E := by
  sorry

/-- Lemma 1.2.13(iv) (Empty set is measurable). This lemma requires proof.  -/
theorem Lebesgue_measurable.empty {d:ℕ} : Lebesgue_measurable (∅: Set (EuclideanSpace' d)) := by
  sorry

/-- Lemma 1.2.13(v) (Complement of a measurable set is measurable). This lemma requires proof.  -/
theorem Lebesgue_measurable.complement {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Lebesgue_measurable E) : Lebesgue_measurable (Eᶜ) := by
  sorry

/-- Lemma 1.2.13(vi) (Countable union of measurable sets is measurable). This lemma requires proof.  -/
theorem Lebesgue_measurable.countable_union {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, Lebesgue_measurable (E n)) : Lebesgue_measurable (⋃ n, E n) := by
  sorry

theorem Lebesgue_measurable.finite_union {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hE: ∀ i, Lebesgue_measurable (E i)) : Lebesgue_measurable (⋃ i, E i) := by
  sorry

theorem Lebesgue_measurable.union {d n:ℕ} {E F: Set (EuclideanSpace' d)} (hE: Lebesgue_measurable E) (hF: Lebesgue_measurable F) : Lebesgue_measurable (E ∪ F) := by
  sorry

/-- Lemma 1.2.13(vii) (Countable intersection of measurable sets is measurable). This lemma requires proof. -/
theorem Lebesgue_measurable.countable_inter {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, Lebesgue_measurable (E n)) : Lebesgue_measurable (⋂ n, E n) := by
  sorry

theorem Lebesgue_measurable.finite_inter {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hE: ∀ i, Lebesgue_measurable (E i)) : Lebesgue_measurable (⋂ i, E i) := by
  sorry

theorem Lebesgue_measurable.inter {d n:ℕ} {E F: Set (EuclideanSpace' d)} (hE: Lebesgue_measurable E) (hF: Lebesgue_measurable F) : Lebesgue_measurable (E ∩ F) := by
  sorry

/-- Exercise 1.2.7 (Criteria for measurability)-/
theorem Lebesgue_measurable.TFAE {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      Lebesgue_measurable E,
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure (U \ E) ≤ ε),
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ Lebesgue_outer_measure (symmDiff U E) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsClosed F ∧ F ⊆ E ∧ Lebesgue_outer_measure (E \ F) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsClosed F ∧ Lebesgue_outer_measure (symmDiff F E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), Lebesgue_measurable E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε)
    ].TFAE
  := by sorry

  /-- Exercise 1.2.8 -/
theorem Jordan_measurable.lebesgue {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : Lebesgue_measurable E := by
  sorry

open BoundedInterval

abbrev CantorInterval (n:ℕ) : Set ℝ := ⋃ a : Fin n → ({0, 2}:Set ℕ), (Icc (∑ i, (a i)/(3:ℝ)^(i.val+1)) (∑ i, a i/(3:ℝ)^(i.val+1) + 1/(3:ℝ)^(n+1))).toSet

abbrev CantorSet : Set ℝ := ⋂ n : ℕ, CantorInterval n

/-- Exercise 1.2.9 (Middle thirds Cantor set ) -/
theorem CantorSet.compact : IsCompact CantorSet := by
  sorry

theorem CantorSet.uncountable : Uncountable CantorSet := by
  sorry

theorem CantorSet.null : IsNull (EuclideanSpace'.equiv_Real.symm '' CantorSet) := by sorry

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
theorem Lebesgue_measure.countable_union {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hmes: ∀ n, Lebesgue_measurable (E n)) (hdisj: Set.univ.PairwiseDisjoint E) : Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  sorry

theorem Lebesgue_measure.finite_union {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hmes: ∀ n, Lebesgue_measurable (E n)) (hdisj: Set.univ.PairwiseDisjoint E) : Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  sorry

theorem Lebesgue_measure.union {d:ℕ} {E F: Set (EuclideanSpace' d)} (hE: Lebesgue_measurable E) (hF: Lebesgue_measurable F) (hdisj: E ∩ F = ∅) : Lebesgue_measure (E ∪ F) = Lebesgue_measure E + Lebesgue_measure F := by
  sorry

/-- Exercise 1.2.11(a) (Upward monotone convergence)-/
theorem Lebesgue_measure.upward_monotone_convergence {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, Lebesgue_measurable (E n)) (hmono: ∀ n, E n ⊆ E (n + 1)) : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋃ n, E n))) := by
  sorry

/-- Exercise 1.2.11(b) (Downward monotone convergence)-/
theorem Lebesgue_measure.downward_monotone_convergence {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, Lebesgue_measurable (E n)) (hmono: ∀ n, E (n+1) ⊆ E n) (hfin: ∃ n, Lebesgue_measure (E n) < ⊤) : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋂ n, E n))) := by
  sorry

/-- Exercise 1.2.11 (c) (counterexample)-/
example : ∃ (d:ℕ) (E: ℕ → Set (EuclideanSpace' d)) (hE: ∀ n, Lebesgue_measurable (E n)) (hmono: ∀ n, E (n+1) ⊆ E n), ¬ Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋂ n, E n))) := by sorry
