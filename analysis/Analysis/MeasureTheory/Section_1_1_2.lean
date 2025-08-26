import Analysis.MeasureTheory.Section_1_1_1
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Introduction to Measure Theory, Section 1.1.2: Jordan measure

A companion to Section 1.1.2 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.1.4.  We intend these concepts to only be applied for bounded sets `E`, but
it is convenient to permit `E` to be unbounded for the purposes of making the definitions.
-/
noncomputable abbrev Jordan_inner_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : ℝ :=
  sSup { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, A ⊆ E ∧ m = hA.measure }

noncomputable abbrev Jordan_outer_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : ℝ :=
  sInf { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, E ⊆ A ∧ m = hA.measure }

noncomputable abbrev JordanMeasurable {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop :=
  Bornology.IsBounded E ∧ Jordan_inner_measure E = Jordan_outer_measure E

noncomputable abbrev JordanMeasurable.measure {d:ℕ} {E: Set (EuclideanSpace' d)} (_: JordanMeasurable E) : ℝ :=
  Jordan_inner_measure E

theorem JordanMeasurable.eq_inner {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : hE.measure = Jordan_inner_measure E := rfl

theorem JordanMeasurable.eq_outer {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : hE.measure = Jordan_outer_measure E := by grind


/-- Various preparatory lemmas for the exercises. -/
theorem IsElementary.contains_bounded {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : ∃ A: Set (EuclideanSpace' d), IsElementary A ∧ E ⊆ A := by
  sorry

theorem Jordan_inner_measure_nonneg {d:ℕ} (E: Set (EuclideanSpace' d)) : 0 ≤ Jordan_inner_measure E := by
  sorry

theorem Jordan_outer_measure_nonneg {d:ℕ} (E: Set (EuclideanSpace' d)) : 0 ≤ Jordan_outer_measure E := by
  sorry

theorem Jordan_inner_le_outer {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Jordan_inner_measure E ≤ Jordan_outer_measure E := by
  sorry

theorem le_Jordan_inner {d:ℕ} {E A: Set (EuclideanSpace' d)}
  (hA: IsElementary A) (hAE: A ⊆ E) : hA.measure ≤ Jordan_inner_measure A := by
  sorry

theorem Jordan_outer_le {d:ℕ} {E A: Set (EuclideanSpace' d)}
  (hA: IsElementary A) (hAE: E ⊆ A) : Jordan_outer_measure A ≤ hA.measure := by
  sorry

theorem Jordan_inner_le {d:ℕ} {E: Set (EuclideanSpace' d)} {m:ℝ}
  (hm: m < Jordan_inner_measure E) : ∃ A: Set (EuclideanSpace' d), ∃ hA: IsElementary A, A ⊆ E ∧ m < hA.measure := by
    sorry

theorem le_Jordan_outer {d:ℕ} {E: Set (EuclideanSpace' d)} {m:ℝ}
  (hm: Jordan_outer_measure E < m) (hbound: Bornology.IsBounded E) :
  ∃ A: Set (EuclideanSpace' d), ∃ hA: IsElementary A, E ⊆ A ∧ hA.measure < m := by
    sorry

/-- Exercise 1.1.5 -/
theorem JordanMeasurable.equiv {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
 [JordanMeasurable E,
  ∀ ε>0, ∃ A, ∃ B, ∃ hA: IsElementary A, ∃ hB: IsElementary B,
    A ⊆ E ∧ E ⊆ B ∧ (hB.sdiff hA).measure ≤ ε,
  ∀ ε>0, ∃ A, ∃ hA: IsElementary A, Jordan_outer_measure (symmDiff E A) ≤ ε].TFAE := by
  sorry

theorem IsElementary.jordanMeasurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) : JordanMeasurable E := by
  sorry

theorem JordanMeasurable.mes_of_elementary {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) : hE.jordanMeasurable.measure = hE.measure := by
  sorry

theorem JordanMeasurable.empty (d:ℕ) : JordanMeasurable (∅: Set (EuclideanSpace' d)) := by
  sorry

@[simp]
theorem JordanMeasurable.mes_of_empty (d:ℕ) : (JordanMeasurable.empty d).measure = 0 := by
  sorry


/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.union {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (E ∪ F) := by
  sorry

lemma JordanMeasurable.union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, JordanMeasurable E) : JordanMeasurable (⋃ E ∈ S, E) := by sorry

/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.inter {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (E ∩ F) := by
  sorry

/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.sdiff {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (E \ F) := by
  sorry

/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.symmDiff {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (symmDiff E F) := by
  sorry

/-- Exercise 1.1.6 (ii) (non-negativity) -/
theorem JordanMeasurable.nonneg {d:ℕ} {E : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) : 0 ≤ hE.measure := by
  sorry

/-- Exercise 1.1.6 (iii) (finite additivity) -/
theorem JordanMeasurable.mes_of_disjUnion {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) (hEF: Disjoint E F)
  : (hE.union hF).measure = hE.measure + hF.measure := by
  sorry

/-- Exercise 1.1.6 (iii) (finite additivity) -/
lemma JordanMeasurable.measure_of_disjUnion' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, JordanMeasurable E) (hdisj: S.toSet.PairwiseDisjoint id):
  (JordanMeasurable.union' hE).measure = ∑ E:S, (hE E.val E.property).measure := by
  sorry

/-- Exercise 1.1.6 (iv) (monotonicity) -/
theorem JordanMeasurable.mono {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) (hEF: E ⊆ F)
  : hE.measure ≤ hF.measure := by
  sorry

/-- Exercise 1.1.6 (v) (finite subadditivity) -/
theorem JordanMeasurable.mes_of_union {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F)
  : (hE.union hF).measure ≤ hE.measure + hF.measure := by
  sorry

/-- Exercise 1.1.6 (v) (finite subadditivity) -/
lemma JordanMeasurable.measure_of_union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, JordanMeasurable E) :
  (JordanMeasurable.union' hE).measure ≤ ∑ E:S, (hE E.val E.property).measure := by
  sorry

open Pointwise

/-- Exercise 1.1.6 (vi) (translation invariance) -/
theorem JordanMeasurable.translate {d:ℕ} {E: Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (x: EuclideanSpace' d) : JordanMeasurable (E + {x}) := by
  sorry

/-- Exercise 1.1.6 (vi) (translation invariance) -/
lemma JordanMeasurable.measure_of_translate {d:ℕ} {E: Set (EuclideanSpace' d)}
(hE: JordanMeasurable E) (x: EuclideanSpace' d):
  (hE.translate x).measure ≤ hE.measure := by
  sorry

/-- Exercise 1.1.7 (i) (Regions under graphs are Jordan measurable) -/
lemma JordanMeasurable.graph {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ} (hf: ContinuousOn f B.toSet) : JordanMeasurable { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, f x ⟩ } := by
  sorry

/-- Exercise 1.1.7 (i) (Regions under graphs are Jordan measurable) -/
lemma JordanMeasurable.measure_of_graph {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ} (hf: ContinuousOn f B.toSet) : (JordanMeasurable.graph hf).measure = 0 := by
  sorry

/-- Exercise 1.1.7 (i) (Regions under graphs are Jordan measurable) -/
lemma JordanMeasurable.undergraph {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ} (hf: ContinuousOn f B.toSet) : JordanMeasurable { p | ∃ x ∈ B.toSet, ∃ t:ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } := by
  sorry

/-- Exercise 1.1.8 -/
lemma JordanMeasurable.triangle (T: Affine.Triangle ℝ (EuclideanSpace' 2)) : JordanMeasurable T.closedInterior := by
  sorry

abbrev EuclideanSpace'.plane_wedge (x y: EuclideanSpace' 2) := x 1 * y 0 - x 0 * y 1

/-- Exercise 1.1.8 -/
lemma JordanMeasurable.measure_triangle (T: Affine.Triangle ℝ (EuclideanSpace' 2)) : (JordanMeasurable.triangle T).measure = |(T.points 1 - T.points 0).plane_wedge (T.points 2 - T.points 0)| / 2 := by
  sorry

/-- Exercise 1.1.9 -/
lemma JordanMeasurable.polytope {d:ℕ} (V: Finset (EuclideanSpace' d)) : JordanMeasurable (convexHull ℝ (V.toSet)) := by
  sorry

/-- Exercise 1.1.10 (1) -/
lemma JordanMeasurable.ball {d:ℕ} (x₀: EuclideanSpace' d) {r: ℝ} (hr: 0 < r) : JordanMeasurable (Metric.ball x₀ r) := by
  sorry

/-- Exercise 1.1.10 (1) -/
lemma JordanMeasurable.closedBall {d:ℕ} (x₀: EuclideanSpace' d) {r: ℝ} (hr: 0 < r) : JordanMeasurable (Metric.closedBall x₀ r) := by
  sorry


/-- Exercise 1.1.10 (1) -/
lemma JordanMeasurable.measure_ball (d:ℕ) : ∃ c, ∀ (x₀: EuclideanSpace' d) (r: ℝ) (hr: 0 < r), (ball x₀ hr).measure = c * r^d := by sorry

lemma JordanMeasurable.measure_closedBall {d:ℕ} (x₀: EuclideanSpace' d) {r: ℝ} (hr: 0 < r), (closedBall x₀ hr).measure = (ball x₀ hr).measure := by sorry

/-- Exercise 1.1.10 (2) -/
lemma JordanMeasurable.measure_ball_le (d:ℕ) : (measure_ball d).choose ≤ 2^d := by sorry

/-- Exercise 1.1.10 (2) -/
lemma JordanMeasurable.le_measure_ball (d:ℕ) : 2^d/d.factorial ≤ (measure_ball d).choose := by sorry


