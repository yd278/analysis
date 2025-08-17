import Mathlib.Tactic

/-!
# Introduction to Measure Theory, Chapter 0: Notation

A companion to Chapter 0 of the book "An introduction to Measure Theory".
-/

/-- A version of `Set.indicator` suitable for this text. -/
noncomputable abbrev Set.indicator' {X: Type*} (E: Set X) := indicator E (fun _ ↦ (1:ℝ))

theorem Set.indicator'_apply {X: Type*} (E: Set X) (x: X) [Decidable (x ∈ E)] : indicator' E x = if x ∈ E then 1 else 0 := indicator_apply _ _ _

theorem Set.indicator'_of_mem {X: Type*} {E:Set X} {x:X} (h: x ∈ E) : indicator' E x = 1 := by
  convert indicator_of_mem h (fun _ ↦ (1:ℝ))

theorem Set.indicator'_of_notMem {X: Type*} {E:Set X} {x:X} (h: x ∉ E) : indicator' E x = 0 := by
  convert indicator_of_notMem h (fun _ ↦ (1:ℝ))

/-- A version of `EuclideanSpace` suitable for this text. -/
noncomputable abbrev EuclideanSpace' (n: ℕ) := EuclideanSpace ℝ (Fin n)

theorem EuclideanSpace'.norm_eq {n:ℕ} (x: EuclideanSpace' n) : ‖x‖ = √(∑ i, (x i)^2) := by
  convert EuclideanSpace.norm_eq x using 3 with i
  simp

infix:100 " ⬝ " => inner ℝ

theorem EuclideanSpace'.dot_apply {n:ℕ} (x y: EuclideanSpace' n) : x ⬝ y = ∑ i, (x i)*(y i) := by
  convert PiLp.inner_apply x y using 2 with i
  simp; ring

#check top_add
#check add_top
#check ENNReal.top_mul
#check ENNReal.mul_top
#check lt_top_iff_ne_top

open Filter

theorem ENNReal.upward_continuous {x y:ℕ → ENNReal} (hx: Monotone x) (hy: Monotone y)
 {x₀ y₀ : ENNReal} (hx_lim: atTop.Tendsto x (nhds x₀))
 (hy_lim: atTop.Tendsto y (nhds y₀)) :
  atTop.Tendsto (fun n ↦ x n * y n) (nhds (x₀ * y₀)) := by
  have hx_lt (n:ℕ): x n ≤ x₀ := hx.ge_of_tendsto hx_lim n
  have hy_lt (n:ℕ): y n ≤ y₀ := hy.ge_of_tendsto hy_lim n
  have zero_conv : atTop.Tendsto (fun n:ℕ ↦ (0:ENNReal)) (nhds 0) := tendsto_const_nhds
  have top_conv : atTop.Tendsto (fun n:ℕ ↦ (⊤:ENNReal)) (nhds ⊤) := tendsto_const_nhds
  obtain rfl | hx₀ := eq_zero_or_pos x₀
  . simp; convert zero_conv with n
    simp [nonpos_iff_eq_zero.mp (hx_lt n)]
  obtain rfl | hy₀ := eq_zero_or_pos y₀
  . simp; convert zero_conv with n
    simp [nonpos_iff_eq_zero.mp (hy_lt n)]
  have hx_pos : ∃ n, 0 < x n := by
    by_contra!
    have hx0 : x = 0 := by ext n; exact nonpos_iff_eq_zero.mp (this n)
    subst hx0
    have := tendsto_nhds_unique hx_lim zero_conv
    order
  choose nx hnx using hx_pos
  have hy_pos : ∃ n, 0 < y n := by
    by_contra!
    have hy0 : y = 0 := by ext n; exact nonpos_iff_eq_zero.mp (this n)
    subst hy0
    have := tendsto_nhds_unique hy_lim zero_conv
    order
  choose ny hny using hy_pos
  obtain rfl | hx₀' := eq_top_or_lt_top x₀
  . rw [top_mul (by order)]
    obtain hyn' | hyn' := eq_or_ne (y ny) ⊤
    . apply top_conv.congr'
      simp [EventuallyEq, eventually_atTop]
      use nx ⊔ ny; intro n hn; simp at hn
      symm; convert ENNReal.mul_top _
      . have := hy hn.2
        rwa [hyn', ←eq_top_iff] at this
      have := hx hn.1
      order
    have : atTop.Tendsto (fun n ↦ x n * y ny) (nhds ⊤) := by
      convert Tendsto.comp (g := fun z ↦ z * y ny) _ hx_lim
      convert (ENNReal.continuous_mul_const hyn').tendsto ⊤
      rw [top_mul (by order)]
    apply tendsto_nhds_top_mono this
    simp [EventuallyLE, eventually_atTop]
    use ny; intro n hn
    gcongr; exact hy hn
  obtain rfl | hy₀' := eq_top_or_lt_top y₀
  . rw [mul_top (by order)]
    have : atTop.Tendsto (fun n ↦ x nx * y n) (nhds ⊤) := by
      convert Tendsto.comp (g := fun z ↦ (x nx) * z) _ hy_lim
      convert (ENNReal.continuous_const_mul _).tendsto ⊤
      . rw [mul_top (by order)]
      specialize hx_lt nx
      order
    apply tendsto_nhds_top_mono this
    simp [EventuallyLE, eventually_atTop]
    use nx; intro n hn
    gcongr; exact hx hn
  set x' : ℕ → NNReal := fun n ↦ (x n).toNNReal
  set y' : ℕ → NNReal := fun n ↦ (y n).toNNReal
  set x₀' : NNReal := x₀.toNNReal
  set y₀' : NNReal := y₀.toNNReal
  have hxx₀' : x₀ = x₀' := by rw [coe_toNNReal]; order
  have hyy₀' : y₀ = y₀' := by rw [coe_toNNReal]; order
  have hxx' (n:ℕ) : x n = x' n := by rw [coe_toNNReal]; specialize hx_lt n; order
  have hyy' (n:ℕ) : y n = y' n := by rw [coe_toNNReal]; specialize hy_lt n; order
  change atTop.Tendsto (fun n ↦ x n) (nhds x₀) at hx_lim
  change atTop.Tendsto (fun n ↦ y n) (nhds y₀) at hy_lim
  simp [hxx', hyy', hxx₀', hyy₀',←coe_mul] at *
  solve_by_elim [Filter.Tendsto.mul]

example : ∃ (x y:ℕ → ENNReal) (hx: Antitone x) (hy: Antitone y)
 (x₀ y₀:ENNReal) (hx_lim: atTop.Tendsto x (nhds x₀))
 (hy_lim: atTop.Tendsto y (nhds y₀)), ¬ atTop.Tendsto (fun n ↦ x n * y n) (nhds (x₀ * y₀)) := by
 sorry

#check ENNReal.tendsto_nat_tsum

#check ENNReal.tsum_eq_iSup_sum

#check Equiv.tsum_eq
