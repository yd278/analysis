import Mathlib.Tactic

/-!
# Analysis I, Section 10.2

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- API for Mathlib's `HasDerivWithinAt`, `derivWithin`, and `DifferentiableWithinAt`.

Note that the Mathlib conventions differ slightly from that in the text, in that differentiability is defined even at points that are not limit points of the domain; derivatives in such cases may not be unique, but `derivWithin` still selects one such derivative in such cases (or `0`, if no derivative exists).

-/


namespace Chapter10

/-- Definition 10.2.1 (Local maxima and minima).  Here we use Mathlib's `IsLocalMaxOn` type. -/
theorem IsLocalMaxOn.iff (X:Set ℝ) (f:ℝ → ℝ) (x₀:ℝ) :
  IsLocalMaxOn f X x₀ ↔
  ∃ δ > 0, IsMaxOn f (X ∩ Set.Ioo (x₀ - δ) (x₀ + δ)) x₀ := by
  simp [isMaxOn_iff, IsLocalMaxOn, IsMaxFilter, nhdsWithin.eq_1, Filter.eventually_inf_principal, Metric.eventually_nhds_iff, Real.dist_eq, abs_sub_lt_iff ]
  apply exists_congr; intro ε
  apply and_congr_right; intro hε
  apply forall_congr'; intro x
  constructor
  . intro h hx hxm hxp
    exact h (by linarith) (by linarith) hx
  intro h hxm hxp hx
  exact h hx (by linarith) (by linarith)

theorem IsLocalMinOn.iff (X:Set ℝ) (f:ℝ → ℝ) (x₀:ℝ) :
  IsLocalMinOn f X x₀ ↔
  ∃ δ > 0, IsMinOn f (X ∩ Set.Ioo (x₀ - δ) (x₀ + δ)) x₀ := by
  simp [isMinOn_iff, IsLocalMinOn, IsMinFilter, nhdsWithin.eq_1, Filter.eventually_inf_principal, Metric.eventually_nhds_iff, Real.dist_eq, abs_sub_lt_iff ]
  apply exists_congr; intro ε
  apply and_congr_right; intro hε
  apply forall_congr'; intro x
  constructor
  . intro h hx hxm hxp
    exact h (by linarith) (by linarith) hx
  intro h hxm hxp hx
  exact h hx (by linarith) (by linarith)


end Chapter10
