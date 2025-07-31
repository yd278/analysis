import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_11_3

/-!
# Analysis I, Section 11.4: Basic properties of the Riemann integral

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Basic properties of the Riemann integral.

-/

namespace Chapter11
open Chapter9

/-- Theorem 11.4.1(a) / Exercise 11.4.1 -/
theorem integ_of_add {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f + g) I ∧ integ (f + g) I = integ f I + integ g I := by
  sorry

/-- Theorem 11.4.1(b) / Exercise 11.4.1 -/
theorem integ_of_smul {I: BoundedInterval} (c:ℝ) {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (c • f) I ∧ integ (c • f) I = c * integ f I := by
  sorry

theorem integ_of_neg {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (-f) I ∧ integ (-f) I = -integ f I := by
  have := integ_of_smul (-1) hf
  simpa using this

/-- Theorem 11.4.1(c) / Exercise 11.4.1 -/
theorem integ_of_sub {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f - g) I ∧ integ (f - g) I = integ f I - integ g I := by
  sorry

/-- Theorem 11.4.1(d) / Exercise 11.4.1 -/
theorem integ_of_nonneg {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) (hf_nonneg: ∀ x ∈ I, 0 ≤ f x) :
  0 ≤ integ f I := by
  sorry

/-- Theorem 11.4.1(e) / Exercise 11.4.1 -/
theorem integ_mono {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I)
  (h: MajorizesOn g f I) :
  integ f I ≤ integ g I := by
  sorry

/-- Theorem 11.4.1(f) / Exercise 11.4.1 -/
theorem integ_of_const (c:ℝ) (I: BoundedInterval) :
  IntegrableOn (fun _ ↦ c) I ∧ integ (fun _ ↦ c) I = c * |I|ₗ := by
  sorry

/-- Theorem 11.4.1(f) / Exercise 11.4.1 -/
theorem integ_of_const' {I: BoundedInterval} {f:ℝ → ℝ} (hf: ConstantOn f I) :
  IntegrableOn f I ∧ integ f I = (constant_value_on f I) * |I|ₗ := by
  sorry


open Classical in
/-- Theorem 11.4.1 (g)  / Exercise 11.4.1 -/
theorem IntegrableOn.of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  IntegrableOn (fun x ↦ if x ∈ I then f x else 0) J := by
  sorry

open Classical in
/-- Theorem 11.4.1 (g)  / Exercise 11.4.1 -/
theorem integ_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  integ (fun x ↦ if x ∈ I then f x else 0) J = integ f I := by
  sorry

/-- Theorem 11.4.1 (h) (Laws of integration) / Exercise 11.4.1 -/
theorem integ_of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: IntegrableOn f K) :
  IntegrableOn f I ∧ IntegrableOn f J ∧ integ f K = integ f I + integ f J := by
  sorry

/-- A variant of Theorem 11.4.1(h) that will be useful in later sections. -/
theorem integ_mono' {I J: BoundedInterval} (hIJ: J ⊆ I)
  {f: ℝ → ℝ} (h: IntegrableOn f I) : IntegrableOn f J := by
  sorry

/-- A further variant of Theorem 11.4.1(h) that will be useful in later sections. -/
theorem integ_eq {I J: BoundedInterval} (hIJ: J ⊆ I)
  (ha: J.a = I.a) (hb: J.b = I.b)
  {f: ℝ → ℝ} (h: IntegrableOn f I) : integ f J = integ f I := by
  sorry

/-- A handy little lemma for "epsilon of room" type arguments -/
lemma nonneg_of_le_const_mul_eps {x C:ℝ} (h: ∀ ε>0, x ≤ C * ε) : x ≤ 0 := by
  by_cases hC: C > 0
  . by_contra!
    specialize h (x/(2*C)) ( by positivity); convert_to x ≤ x/2 at h
    . field_simp; ring
    linarith
  specialize h 1 (by norm_num); simp at h hC; linarith

/-- Theorem 11.4.3 (Max and min preserve integrability)-/
theorem integ_of_max {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (max f g) I  := by
  -- This proof is written to follow the structure of the original text.
  unfold IntegrableOn at hf hg
  have hmax_bound : BddOn (max f g) I := by
    obtain ⟨ M, hM ⟩ := hf.1; obtain ⟨ M', hM' ⟩ := hg.1
    use max M M'; peel hM with x hx hM; specialize hM' _ hx
    simp only [Pi.sup_apply]
    apply abs_max_le_max_abs_abs.trans
    exact sup_le_sup hM hM'
  have lower_le_upper : 0 ≤ upper_integral (max f g) I - lower_integral (max f g) I := by linarith [lower_integral_le_upper hmax_bound]
  have (ε:ℝ) (hε: 0 < ε) : upper_integral (max f g) I - lower_integral (max f g) I ≤ 4*ε := by
    obtain ⟨ f', hf'min, hf'const, hf'int ⟩ := gt_of_lt_lower_integral hf.1 (show integ f I - ε < lower_integral f I
    by linarith)
    obtain ⟨ g', hg'min, hg'const, hg'int ⟩ := gt_of_lt_lower_integral hg.1 (show integ g I - ε < lower_integral g I by linarith)
    obtain ⟨ f'', hf''max, hf''const, hf''int ⟩ := lt_of_gt_upper_integral hf.1 (show upper_integral f I < integ f I + ε by linarith)
    obtain ⟨ g'', hg''max, hg''const, hg''int ⟩ := lt_of_gt_upper_integral hg.1 (show upper_integral g I < integ g I + ε by linarith)
    set h := (f'' - f') + (g'' - g')
    have hf'_integ := integ_of_piecewise_const hf'const
    have hg'_integ := integ_of_piecewise_const hg'const
    have hf''_integ := integ_of_piecewise_const hf''const
    have hg''_integ := integ_of_piecewise_const hg''const
    have hf''f'_integ := integ_of_sub hf''_integ.1 hf'_integ.1
    have hg''g'_integ := integ_of_sub hg''_integ.1 hg'_integ.1
    have hh_integ_eq := integ_of_add hf''f'_integ.1 hg''g'_integ.1
    have hinteg_le : integ h I ≤ 4 * ε := by linarith
    have hf''g''_const := hf''const.max hg''const
    have hf''g''_maj : MajorizesOn (max f'' g'') (max f g) I := by
      sorry
    have hf'g'_const := hf'const.max hg'const
    have hf'g'_maj : MinorizesOn (max f' g') (max f g) I := by
      sorry
    have hff'g''_ge := upper_integral_le_integ hmax_bound hf''g''_maj hf''g''_const
    have hf'g'_le := integ_le_lower_integral hmax_bound hf'g'_maj hf'g'_const
    have : MinorizesOn (max f'' g'') (max f' g' + h) I := by
      peel hf'min with x hx hf'min; specialize hg'min _ hx; specialize hf''max _ hx; specialize hg''max _ hx
      simp [h]; and_intros <;> linarith [le_max_left (f' x) (g' x), le_max_right (f' x) (g' x)]
    have hf'g'_integ := integ_of_piecewise_const hf'g'_const
    have hf''g''_integ := integ_of_piecewise_const hf''g''_const
    have hf'g'h_integ := integ_of_add hf'g'_integ.1 hh_integ_eq.1
    rw [MinorizesOn.iff] at this
    linarith [integ_mono hf''g''_integ.1 hf'g'h_integ.1 this]
  exact ⟨ hmax_bound, by linarith [nonneg_of_le_const_mul_eps this] ⟩



/-- Theorem 11.4.5 / Exercise 11.4.3.  The objective here is to create a shorter proof than the one above.-/
theorem integ_of_min {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (min f g) I  := by
  sorry

/-- Corollary 11.4.4 -/
theorem integ_of_abs {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (abs f) I := by
  have := (integ_of_const 0 I).1
  convert (integ_of_sub (integ_of_max hf this) (integ_of_min hf this)).1 using 1
  ext x; rcases le_or_gt (f x) 0 with h | h
  . simp [h]
  simp [le_of_lt h]

/-- Theorem 11.4.5 (Products preserve Riemann integrability).
It is convenient to first establish the non-negative case.-/
theorem integ_of_mul_nonneg {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I)
  (hf_nonneg: MajorizesOn f 0 I) (hg_nonneg: MajorizesOn g 0 I) :
  IntegrableOn (f * g) I := by
  -- This proof is written to follow the structure of the original text.
  by_cases hI : (I:Set ℝ).Nonempty
  swap
  . apply (integ_on_subsingleton _).1
    rw [←BoundedInterval.length_of_subsingleton]
    simp_all [Set.not_nonempty_iff_eq_empty]
  unfold IntegrableOn at hf hg
  obtain ⟨ M₁, hM₁ ⟩ := hf.1
  obtain ⟨ M₂, hM₂ ⟩ := hg.1
  have hM₁pos : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ hI.some hI.some_mem)
  have hM₂pos : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ hI.some hI.some_mem)
  have hmul_bound : BddOn (f * g) I := by
    use M₁ * M₂; peel hM₁ with x hx hM₁; specialize hM₂ _ hx
    simp [abs_mul]; apply mul_le_mul hM₁ hM₂ <;> positivity
  have lower_le_upper : 0 ≤ upper_integral (f * g) I - lower_integral (f * g) I := by
    linarith [lower_integral_le_upper hmul_bound]
  have (ε:ℝ) (hε: 0 < ε) : upper_integral (f * g) I - lower_integral (f * g) I ≤ 2*(M₁+M₂)*ε := by
    have : ∃ f', MinorizesOn f' f I ∧ PiecewiseConstantOn f' I ∧ integ f I - ε < PiecewiseConstantOn.integ f' I ∧ MajorizesOn f' 0 I := by
      obtain ⟨ f', hf'min, hf'const, hf'int ⟩ := gt_of_lt_lower_integral hf.1 (show integ f I - ε < lower_integral f I by linarith)
      use max f' 0
      have hzero := PiecewiseConstantOn.of_const (ConstantOn.of_const' 0 I)
      and_intros
      . peel hf_nonneg with x hx _; specialize hf'min _ hx; aesop
      . exact hf'const.max hzero
      . exact lt_of_lt_of_le hf'int (hf'const.integ_mono (by intros; simp) (hf'const.max hzero))
      intro _ _; simp
    obtain ⟨ f', hf'min, hf'const, hf'int, hf'_nonneg ⟩ := this
    have : ∃ g', MinorizesOn g' g I ∧ PiecewiseConstantOn g' I ∧ integ g I - ε < PiecewiseConstantOn.integ g' I ∧ MajorizesOn g' 0 I := by
      obtain ⟨ g', hg'min, hg'const, hg'int ⟩ := gt_of_lt_lower_integral hg.1 (show integ g I - ε < lower_integral g I by linarith)
      use max g' 0
      have hzero := PiecewiseConstantOn.of_const (ConstantOn.of_const' 0 I)
      and_intros
      . peel hg_nonneg with x hx _; specialize hg'min _ hx; aesop
      . exact hg'const.max hzero
      . apply lt_of_lt_of_le hg'int (hg'const.integ_mono (by intros; simp) (hg'const.max hzero))
      intro _ _; simp
    obtain ⟨ g', hg'min, hg'const, hg'int, hg'_nonneg ⟩ := this
    have : ∃ f'', MajorizesOn f'' f I ∧ PiecewiseConstantOn f'' I ∧ PiecewiseConstantOn.integ f'' I < integ f I + ε ∧ MinorizesOn f'' (fun _ ↦ M₁) I := by
      obtain ⟨ f'', hf''maj, hf''const, hf''int ⟩ := lt_of_gt_upper_integral hf.1 (show upper_integral f I < integ f I + ε  by linarith)
      use min f'' (fun _ ↦ M₁)
      have hM₁_piece := PiecewiseConstantOn.of_const (ConstantOn.of_const' M₁ I)
      and_intros
      . peel hM₁ with x hx hM₁; rw [abs_le'] at hM₁
        specialize hf''maj _ hx; simp [hf''maj, hM₁.1]
      . exact hf''const.min hM₁_piece
      . apply lt_of_le_of_lt ((hf''const.min hM₁_piece).integ_mono _ hf''const) hf''int
        intros; simp [hf''maj, hM₁_piece]
      intro _ _; simp
    obtain ⟨ f'', hf''maj, hf''const, hf''int, hf''bound ⟩ := this
    have : ∃ g'', MajorizesOn g'' g I ∧ PiecewiseConstantOn g'' I ∧ PiecewiseConstantOn.integ g'' I < integ g I + ε ∧ MinorizesOn g'' (fun _ ↦ M₂) I := by
      obtain ⟨ g'', hg''maj, hg''const, hg''int ⟩ := lt_of_gt_upper_integral hg.1 (show upper_integral g I < integ g I + ε  by linarith)
      use min g'' (fun _ ↦ M₂)
      have hM₂_piece := PiecewiseConstantOn.of_const (ConstantOn.of_const' M₂ I)
      and_intros
      . peel hM₂ with x hx hM₂; rw [abs_le'] at hM₂
        specialize hg''maj _ hx; simp [hg''maj, hM₂.1]
      . exact hg''const.min hM₂_piece
      . apply lt_of_le_of_lt ((hg''const.min hM₂_piece).integ_mono _ hg''const) hg''int
        intros; simp [hg''maj, hM₂_piece]
      intro _ _; simp
    obtain ⟨ g'', hg''maj, hg''const, hg''int, hg''bound ⟩ := this
    have hf'g'_const := PiecewiseConstantOn.mul hf'const hg'const
    have hf'g'_maj : MinorizesOn (f' * g') (f * g) I := by
      peel hf'min with x hx hf'min; specialize hg'min _ hx; specialize hf'_nonneg _ hx; specialize hg'_nonneg _ hx
      simp at *; exact mul_le_mul hf'min hg'min (by positivity) (by linarith)
    have hf''g''_const := PiecewiseConstantOn.mul hf''const hg''const
    have hf''g''_maj : MajorizesOn (f'' * g'') (f * g) I := by
      peel hf''maj with x hx hf''maj; specialize hg''maj _ hx; specialize hf''bound _ hx
      specialize hg_nonneg _ hx; specialize hf_nonneg _ hx
      simp at *; exact mul_le_mul hf''maj hg''maj (by positivity) (by linarith)
    have hupper_le := upper_integral_le_integ hmul_bound hf''g''_maj hf''g''_const
    have hlower_ge := integ_le_lower_integral hmul_bound hf'g'_maj hf'g'_const
    have hh_const := hf''g''_const.sub hf'g'_const
    have hh_integ := hf''g''_const.integ_sub hf'g'_const
    have hhmin : MinorizesOn (f'' * g'' - f' * g') (M₁ • (g''-g') + M₂ • (f''-f')) I := by
      intro x hx
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc
        _ = (f'' x) * (g'' x - g' x) + (g' x) * (f'' x - f' x) := by ring
        _ ≤ _ := by
          specialize hg'min x hx; specialize hg''maj x hx; specialize hf''bound x hx
          specialize hf'min x hx; specialize hf''maj x hx; specialize hg''bound x hx
          simp at hg''bound; gcongr <;> linarith
    have hg''g'_const := hg''const.sub hg'const
    have hg''g'_integ := hg''const.integ_sub hg'const
    have hM₁g''g'_const := hg''g'_const.smul M₁
    have hM₁g''g_integ := hg''g'_const.integ_smul M₁
    have hf''f'_const := hf''const.sub hf'const
    have hf''f_integ := hf''const.integ_sub hf'const
    have hM₂f''f'_const := hf''f'_const.smul M₂
    have hM₂f''f_integ := hf''f'_const.integ_smul M₂
    have hsum_const := hM₁g''g'_const.add hM₂f''f'_const
    have hsum_integ := hM₁g''g'_const.integ_add hM₂f''f'_const
    have hsum_bound := hh_const.integ_mono hhmin hsum_const
    calc
      _ ≤ M₁ * PiecewiseConstantOn.integ (g'' - g') I + M₂ * PiecewiseConstantOn.integ (f'' - f') I := by linarith
      _ ≤ M₁ * (2*ε) + M₂ * (2*ε) := by gcongr <;> linarith
      _ = _ := by ring
  exact ⟨ hmul_bound, by linarith [nonneg_of_le_const_mul_eps this] ⟩


theorem integ_of_mul {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f * g) I := by
  -- This proof is written to follow the structure of the original text.
  set fplus := max f (fun _ ↦ 0)
  set fminus := -min f (fun _ ↦ 0)
  set gplus := max g (fun _ ↦ 0)
  set gminus := -min g (fun _ ↦ 0)
  have := (integ_of_const 0 I).1
  have hfplus_integ : IntegrableOn fplus I := integ_of_max hf this
  have hfminus_integ : IntegrableOn fminus I := (integ_of_neg (integ_of_min hf this)).1
  have hgplus_integ : IntegrableOn gplus I := integ_of_max hg this
  have hgminus_integ : IntegrableOn gminus I := (integ_of_neg (integ_of_min hg this)).1
  have hfplus_nonneg : MajorizesOn fplus 0 I := by intro _ _; simp [fplus]
  have hfminus_nonneg : MajorizesOn fminus 0 I := by intro _ _; simp [fminus]
  have hgplus_nonneg : MajorizesOn gplus 0 I := by intro _ _; simp [gplus]
  have hgminus_nonneg : MajorizesOn gminus 0 I := by intro _ _; simp [gminus]
  have hfplusgplus := integ_of_mul_nonneg hfplus_integ hgplus_integ hfplus_nonneg hgplus_nonneg
  have hfplusgminus := integ_of_mul_nonneg hfplus_integ hgminus_integ hfplus_nonneg hgminus_nonneg
  have hfminusgplus := integ_of_mul_nonneg hfminus_integ hgplus_integ hfminus_nonneg hgplus_nonneg
  have hfminusgminus := integ_of_mul_nonneg hfminus_integ hgminus_integ hfminus_nonneg hgminus_nonneg
  have hf : f = fplus - fminus := by ext x; simp [fplus, fminus]
  have hg : g = gplus - gminus := by ext x; simp [gplus, gminus]
  rw [hf, hg]
  ring_nf
  apply (integ_of_add _ hfminusgminus).1
  apply (integ_of_add hfplusgplus _).1
  apply (integ_of_sub _ hfminusgplus).1
  exact (integ_of_neg hfplusgminus).1

open BoundedInterval

/-- Exercise 11.4.2 -/
theorem integ_split {I: BoundedInterval} {f: ℝ → ℝ} (hf: IntegrableOn f I) (P: Partition I) :
  integ f I = ∑ J ∈ P.intervals, integ f J := by
    sorry



end Chapter11
