import Mathlib.Tactic
import Analysis.Section_5_2

/-!
# Analysis I, Section 5.2

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence
- Construction of a real number type `Chapter5.Real`
- Basic arithmetic operations and properties
-/

namespace Chapter5

/-- A class of Cauchy sequences that start at zero -/
@[ext]
class CauchySequence extends Sequence where
  zero : n₀ = 0
  cauchy : toSequence.isCauchy

theorem CauchySequence.ext' {a b: CauchySequence} (h: a.seq = b.seq) : a = b := by
  apply CauchySequence.ext
  . rw [a.zero, b.zero]
  exact h

/-- A sequence starting at zero that is Cauchy, can be viewed as a Cauchy sequence.-/
abbrev CauchySequence.mk' {a:ℕ → ℚ} (ha: (a:Sequence).isCauchy) : CauchySequence where
  n₀ := 0
  seq := (a:Sequence).seq
  vanish := by
    intro n hn
    exact (a:Sequence).vanish n hn
  zero := rfl
  cauchy := ha

theorem CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).isCauchy) : (mk' ha).toSequence = (a:Sequence) := by rfl

instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe := fun a n ↦ a.toSequence (n:ℤ)

theorem CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).isCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.equiv a b
  iseqv := {
     refl := sorry
     symm := sorry
     trans := sorry
  }

theorem CauchySequence.equiv_iff (a b: CauchySequence) : a ≈ b ↔ Sequence.equiv a b := by rfl
/-- Every constant sequence is Cauchy -/
theorem Sequence.isCauchy_of_const (a:ℚ) : ((fun n:ℕ ↦ a):Sequence).isCauchy := by sorry

instance CauchySequence.instZero : Zero CauchySequence where
  zero := CauchySequence.mk' (a := fun _: ℕ ↦ 0) (Sequence.isCauchy_of_const (0:ℚ))

abbrev Real := Quotient CauchySequence.instSetoid

open Classical in
/-- It is convenient in Lean to assign the "dummy" value of 0 to `LIM a` when `a` is not Cauchy.  This requires Classical logic, because the property of being Cauchy is not computable or decidable.  -/
noncomputable abbrev LIM (a:ℕ → ℚ) : Real := Quotient.mk _ (if h : (a:Sequence).isCauchy then CauchySequence.mk' h else (0:CauchySequence))

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (a:Sequence).isCauchy ∧ x = LIM a := by
  -- I had a lot of trouble with this proof; perhaps there is a more idiomatic way to proceed
  apply Quot.ind _ x; intro a
  use a
  set s : Sequence := (a:Sequence)
  have : s = a.toSequence := by
    apply Sequence.ext
    . rw [a.zero]
    ext n
    by_cases h:n ≥ 0
    . simp [s, Sequence.seq, h]
    simp [s, Sequence.seq, h]
    apply (a.vanish _ _).symm
    rw [a.zero]
    exact Int.lt_of_not_ge h
  rw [this]
  refine ⟨ a.cauchy, ?_ ⟩
  congr
  convert (dif_pos a.cauchy).symm using 4 with n
  apply CauchySequence.ext'
  change a.seq = s.seq
  . rw [this]
  classical
  exact Classical.propDecidable CauchySequence.toSequence.isCauchy

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.lim_eq_lim (a b:ℕ → ℚ) (ha: (a:Sequence).isCauchy) (hb: (b:Sequence).isCauchy) :
  LIM a = LIM b ↔ Sequence.equiv a b := by
  constructor
  . intro h
    replace h := Quotient.exact h
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff ] at h
  intro h
  apply Quotient.sound
  rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]










end Chapter5
