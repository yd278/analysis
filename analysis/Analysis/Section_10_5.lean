import Mathlib.Tactic
import Analysis.Section_9_1
import Analysis.Section_10_1
import Analysis.Section_10_2

/-!
# Analysis I, Section 10.5: L'Hôpital's rule

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- L'Hôpital's rule.

-/

open Chapter9
namespace Chapter10

/-- Proposition 10.5.1 (L'Hôpital's rule, I) / Exercise 10.5.1-/
theorem _root_.Filter.Tendsto.of_div {X: Set ℝ} {f g: ℝ → ℝ} {x₀ f'x₀ g'x₀:ℝ}
  (hfx₀: f x₀ = 0) (hgx₀: g x₀ = 0) (hg_non: g'x₀ ≠ 0)
  (hf'x₀: HasDerivWithinAt f f'x₀ X x₀) (hg'x₀: HasDerivWithinAt g g'x₀ X x₀) :
  (∃ δ > 0, ∀ x ∈ X \ {x₀} ∩ Set.Ioo (x₀ - δ) (x₀ + δ), g x ≠ 0) ∧
  Filter.Tendsto (fun x ↦ f x / g x) (nhdsWithin x₀ (X \ {x₀})) (nhds (f'x₀ / g'x₀))
  := by
  sorry

/-- Proposition 10.5.2 (L'Hôpital's rule, II) -/
theorem _root_.Filter.Tendsto.of_div' {a b L:ℝ} (hab: a < b) {f g f' g': ℝ → ℝ}
  (hf: DifferentiableOn ℝ f (.Icc a b)) (hg: DifferentiableOn ℝ g (.Icc a b))
  (hf': f' = derivWithin f (.Icc a b)) (hg': g' = derivWithin g (.Icc a b))
  (hfa: f a = 0) (hga: g a = 0) (hgnon: ∀ x ∈ Set.Icc a b, g' x ≠ 0)

  (hderiv: Filter.Tendsto (fun x ↦ f' x / g' x) (nhdsWithin a (.Icc a b)) (nhds L)) :
  (∀ x ∈ Set.Ioc a b, g x ≠ 0) ∧
  Filter.Tendsto (fun x ↦ f x / g x) (nhdsWithin a (Set.Ioc a b)) (nhds L) := by
  -- This proof is written to follow the structure of the original text.
  have hfcon : ContinuousOn f (.Icc a b) := .of_differentiableOn hf
  have hgcon : ContinuousOn g (.Icc a b) := .of_differentiableOn hg
  have (x:ℝ) (hx: x ∈ Set.Ioc a b) : g x ≠ 0 := by
    by_contra this
    simp at hx
    have := HasDerivWithinAt.exist_zero hx.1 (hgcon.mono ?_) (hg.mono ?_) (by rw [hga, this])
    . obtain ⟨ y, hy, hgy ⟩ := this; simp at hy
      have : y ∈ Set.Icc a b := by simp; constructor <;> linarith
      specialize hgnon y this
      rw [DifferentiableOn.eq_1] at hf hg; specialize hg y this
      replace hg := hg.hasDerivWithinAt
      replace hg : HasDerivWithinAt g (g' y) (Set.Ioo a x) y:= by
        rw [hg']; apply hg.mono; intro z; simp; intros; constructor <;> linarith
      have hd := derivative_unique ?_ hg hgy
      . contradiction
      apply ClusterPt.mono _ ((Filter.principal_mono (s := Set.Ioo a y)).mpr  _)
      . simp [←mem_closure_iff_clusterPt, closure_Ioo (show a ≠ y by linarith), le_of_lt hy.1]
      intro _; simp; intros; refine ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩ <;> linarith
    . intro _; simp; intro h1 _; constructor <;> linarith
    intro _; simp; intros; constructor <;> linarith
  refine ⟨ this, ?_ ⟩
  rw [nhdsWithin.eq_1] at hderiv ⊢
  rw [←Convergesto.iff, Convergesto.iff_conv _ _ _]
  . intro x hx hconv
    have hxy (n:ℕ) : ∃ yn ∈ Set.Ioo a (x n), (f (x n))/(g (x n)) = f' yn / (g' yn) := by
      set h : ℝ → ℝ := fun x' ↦ (f x') * (g (x n)) - (g x') * (f (x n))
      have hdiff : DifferentiableOn ℝ h (.Icc a b) := by fun_prop
      have hcon : ContinuousOn h (.Icc a b) := by fun_prop
      specialize hx n; simp at hx
      replace hcon : ContinuousOn h (.Icc a (x n)) := by
        apply hcon.mono; intro _; simp; intros; constructor <;> linarith
      replace hdiff : DifferentiableOn ℝ h (.Ioo a (x n)) := by
        apply hdiff.mono; intro _; simp; intros; constructor <;> linarith
      have ha : h a = 0 := by simp [h, hfa, hga]
      have hb : h (x n) = 0 := by simp [h]; ring
      obtain ⟨ yn, hyn, hdh ⟩ := HasDerivWithinAt.exist_zero hx.1 hcon hdiff (by rw [ha, hb])
      use yn, hyn
      rw [DifferentiableOn.eq_1] at hf hg
      have h1 : HasDerivWithinAt f (f' yn) (.Ioo a (x n)) yn := by
        specialize hf yn (by simp at hyn ⊢; constructor <;> linarith)
        rw [hf']; apply hf.hasDerivWithinAt.mono; intro _; simp; intros; constructor <;> linarith
      have h2 : HasDerivWithinAt g (g' yn) (.Ioo a (x n)) yn := by
        specialize hg yn (by simp at hyn ⊢; constructor <;> linarith)
        rw [hg']; apply hg.hasDerivWithinAt.mono; intro _; simp; intros; constructor <;> linarith
      have h3 : HasDerivWithinAt (fun x' ↦ (f x') * (g (x n))) ((f' yn)*(g (x n))) (.Ioo a (x n)) yn :=
        h1.mul_const _
      have h4 : HasDerivWithinAt (fun x' ↦ (g x') * (f (x n))) ((g' yn)*(f (x n))) (.Ioo a (x n)) yn :=
        h2.mul_const _
      have h5 : HasDerivWithinAt h (f' yn * g (x n) - g' yn * f (x n)) (.Ioo a (x n)) yn := by
        simp [h]
        exact HasDerivWithinAt.sub h3 h4
      have h6 : f' yn * g (x n) - g' yn * f (x n) = 0 := by
        apply derivative_unique _ h5 hdh
        simp at hyn
        apply ClusterPt.mono _ ((Filter.principal_mono (s := .Ioo a yn)).mpr  _)
        . simp [←mem_closure_iff_clusterPt, closure_Ioo (show a ≠ yn by linarith), le_of_lt hyn.1]
        intro _; simp; intros; refine ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩ <;> linarith
      have h7 : g (x n) ≠ 0 := this _ (by simp [hx])
      have h8 : g' (yn) ≠ 0 := hgnon _ (by simp at hyn; constructor <;> linarith)
      field_simp; rw [mul_comm]; linarith
    set y : ℕ → ℝ := fun n ↦ (hxy n).choose
    have hy (n:ℕ) : y n ∈ Set.Ioo a (x n) := (hxy n).choose_spec.1
    have hy' (n:ℕ) : (f (x n))/(g (x n)) = f' (y n) / (g' (y n)) := (hxy n).choose_spec.2
    have hyconv : Filter.Tendsto y .atTop (nhds a) := by
      simp at hy
      apply Filter.Tendsto.squeeze tendsto_const_nhds hconv _
      all_goals intro n; linarith [hy n]
    replace hy : ∀ n, y n ∈ Set.Icc a b := by
      intro n; simp at hx hy ⊢; specialize hy n; specialize hx n; constructor <;> linarith
    simp_rw [hy' _]; apply hderiv.comp _; rw [←nhdsWithin.eq_1]
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hyconv _
    exact Filter.Eventually.of_forall hy
  simp [←closure_def', closure_Ioc (show a ≠ b by linarith), le_of_lt hab]


end Chapter10
