import Mathlib.Tactic
import Analysis.Section_9_8
import Analysis.Section_11_5

/-!
# Analysis I, Section 11.5

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Riemann integrability of monotone functions

-/

namespace Chapter11
open Chapter9 BoundedInterval

/-- Proposition 11.6.1 -/
theorem integ_of_monotone {a b:ℝ} {f:ℝ → ℝ} (hf: MonotoneOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := by
  -- This proof is adapted from the structure of the original text.
  by_cases hab : 0 < b-a
  swap
  . apply (integ_on_subsingleton _).1
    rw [←BoundedInterval.length_of_subsingleton]
    aesop
  have hbound :=  BddOn.of_monotone hf
  set I := Icc a b

  have (ε:ℝ) (hε: 0 < ε) : upper_integral f I - lower_integral f I ≤ ((f b - f a) * (b-a)) *ε := by
    obtain ⟨ N, hN ⟩ := exists_nat_gt (1/ε)
    have hNpos : 0 < N := by
      rify
      have : 0 < 1/ε := by positivity
      linarith
    set δ := (b-a)/N
    have hδpos : 0 < δ := by positivity
    set e : ℕ ↪ BoundedInterval := {
      toFun j := Ico (a + δ*j) (a + δ*(j+1))
      inj' := by sorry
    }
    set P : Partition I := {
      intervals := insert (Icc b b) (Finset.map e (Finset.range N))
      exists_unique := by sorry
      contains := by sorry
    }
    have hup := calc
      upper_integral f I ≤ ∑ J ∈ P.intervals, (sSup (f '' (J:Set ℝ))) * |J|ₗ := upper_integ_le_upper_sum hbound P
      _ = ∑ j ∈ Finset.range N, (sSup (f '' (Ico (a + δ*j) (a + δ*(j+1))))) * |Ico (a + δ*j) (a + δ*(j+1))|ₗ := by
        simp [P]
        congr
      _ ≤ ∑ j ∈ Finset.range N, f (a + δ*(j+1)) * δ := by
        apply Finset.sum_le_sum
        intro j hj
        convert (mul_le_mul_right hδpos).mpr ?_
        . simp [length]; ring_nf
          simp [le_of_lt hδpos]
        apply csSup_le
        . simp; ring_nf; linarith
        intro y hy
        simp at hy
        obtain ⟨ x, ⟨ hx1, hx2 ⟩, rfl ⟩ := hy
        have : a + δ*(j+1) ≤ b := by
          sorry
        have hδj : 0 ≤ δ*j := by positivity
        have hδj1 : 0 ≤ δ*(j+1) := by positivity
        apply hf _ _ _
        . simp [I]
          exact ⟨ by linarith, by linarith ⟩
        . simp [I, hδj1, this]
        exact le_of_lt hx2
    have hdown := calc
      lower_integral f I ≥ ∑ J ∈ P.intervals, (sInf (f '' (J:Set ℝ))) * |J|ₗ := by
        sorry
      _ = ∑ j ∈ Finset.range N, (sInf (f '' (Ico (a + δ*j) (a + δ*(j+1))))) * |Ico (a + δ*j) (a + δ*(j+1))|ₗ := by
        sorry
      _ ≥ ∑ j ∈ Finset.range N, f (a + δ*j) * δ := by
        sorry
    calc
      _ ≤ ∑ j ∈ Finset.range N, f (a + δ*(j+1)) * δ - ∑ j ∈ Finset.Ico 0 N, f (a + δ*j) * δ := by linarith
      _ = (f b - f a) * δ := by
        sorry
      _ ≤ _ := by
        sorry
  refine ⟨ hbound, ?_ ⟩
  replace := nonneg_of_le_const_mul_eps this
  have low_le_up : lower_integral f I ≤ upper_integral f I := lower_integral_le_upper hbound
  linarith


/-- Proposition 11.6.1 -/
theorem integ_of_antitone {a b:ℝ} {f:ℝ → ℝ} (hf: AntitoneOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  sorry -- TODO

/-- Corollary 11.6.3 / Exercise 11.6.1 -/
theorem integ_of_bdd_monotone {I:BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: MonotoneOn f I) : IntegrableOn f I := by
  sorry

theorem integ_of_bdd_antitone {I:BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: AntitoneOn f I) : IntegrableOn f I := by
  sorry

/-- Proposition 11.6.4 (Integral test) -/
theorem summable_iff_integ_of_antitone {f:ℝ → ℝ} (hnon: ∀ x ≥ 0, f x ≥ 0)
  (hf: AntitoneOn f (Set.Ici 0)) :
  Summable f ↔ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  sorry

-- Exercise 11.6.2: Formulate a reasonable notion of a piecewise monotone function, and then
-- show that all bounded piecewise monotone functions are Riemann integrable.

/-- Exercise 11.6.4 -/
example : ∃ (f:ℝ → ℝ) (hnon: ∀ x ≥ 0, f x ≥ 0), Summable f ∧ ¬ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  sorry

example : ∃ (f:ℝ → ℝ) (hnon: ∀ x ≥ 0, f x ≥ 0), ¬ Summable f ∧ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  sorry

-- TODO:move Exercise 11.6.5 to Section 11.9

end Chapter11
