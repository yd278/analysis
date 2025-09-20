import Analysis.MeasureTheory.Section_1_1_2

/-!
# Introduction to Measure Theory, Section 1.1.3: Connections with the Riemann integral

A companion to Section 1.1.3 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.1.5.  The interval `I` should be closed, though we will not enforce this.  We also permit the length to be 0. We index the tags and deltas starting from 0 rather than 1
in the text as this is slightly more convenient in Lean. -/
@[ext]
structure TaggedPartition (I: BoundedInterval) (n:ℕ) where
  x : Fin (n+1) → ℝ
  x_tag : Fin n → ℝ
  x_start : x 0 = I.a
  x_end : x (Fin.last n) = I.b
  x_mono : StrictMono x
  x_tag_between (i: Fin n) : x i.castSucc ≤ x_tag i ∧ x_tag i ≤ x i.succ

def TaggedPartition.delta {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n) (i:Fin n): ℝ :=
 P.x i.succ - P.x i.castSucc

noncomputable def TaggedPartition.norm {I: BoundedInterval} {n:ℕ} (P: TaggedPartition I n) : ℝ := iSup P.delta

def TaggedPartition.RiemannSum {I: BoundedInterval} {n:ℕ} (f: ℝ → ℝ) (P: TaggedPartition I n) : ℝ :=
  ∑ i, f (P.x_tag i) * P.delta i

/-- `Sigma (TaggedPartition I)` is the type of all partitions of `I` with an unspecified number `n` of components.  Here we define what it means to converge to zero in this type. -/
instance TaggedPartition.nhds_zero (I: BoundedInterval) : Filter (Sigma (TaggedPartition I)) := Filter.comap (fun P ↦ P.snd.norm) (nhds 0)

def riemann_integrable_eq (f: ℝ → ℝ) (I: BoundedInterval) (R: ℝ) : Prop := (TaggedPartition.nhds_zero I).Tendsto (fun P ↦ TaggedPartition.RiemannSum f P.snd) (nhds R)

abbrev RiemannIntegrableOn (f: ℝ → ℝ) (I: BoundedInterval) : Prop := ∃ R, riemann_integrable_eq f I R

open Classical in
noncomputable def riemannIntegral (f: ℝ → ℝ) (I: BoundedInterval) : ℝ := if h:RiemannIntegrableOn f I then h.choose else 0

lemma riemann_integral_of_integrable {f:ℝ → ℝ} {I: BoundedInterval} (h: RiemannIntegrableOn f I) : riemann_integrable_eq f I (riemannIntegral f I) := by sorry

lemma riemann_integral_eq_iff_of_integrable {f:ℝ → ℝ} {I: BoundedInterval} (h: RiemannIntegrableOn f I) (R:ℝ): riemann_integrable_eq f I R ↔ R = riemannIntegral f I := by sorry

lemma riemann_integral_eq_iff {f:ℝ → ℝ} {I: BoundedInterval} (h: RiemannIntegrableOn f I) (R:ℝ): riemann_integrable_eq f I R ↔ ∀ ε>0, ∃ δ>0, ∀ n, ∀ P: TaggedPartition I n, P.norm ≤ δ → |P.RiemannSum f - R| ≤ ε := by sorry

/-- I *think* this follows from the "junk" definitions of various Mathlib operations, but needs to be checked. If not, then the above definitions need to be adjusted appropriately. -/
lemma RiemannIntegrable.of_zero_length (f: ℝ → ℝ) {I: BoundedInterval} (h: I.length = 0) : RiemannIntegrableOn f I ∧ riemannIntegral f I = 0 := by sorry

theorem RiemannIntegrable.bounded {f: ℝ → ℝ} {I: BoundedInterval} (h: RiemannIntegrableOn f I) : ∃ M, ∀ x ∈ I, |f x| ≤ M := by sorry

@[ext]
structure PiecewiseConstantFunction (I: BoundedInterval) where
  f : ℝ → ℝ
  T : Finset BoundedInterval
  c : T → ℝ
  disjoint: T.toSet.PairwiseDisjoint BoundedInterval.toSet
  cover : I.toSet = ⋃ J ∈ T, J.toSet
  const : ∀ J:T, ∀ x ∈ J.val, f x = c J

