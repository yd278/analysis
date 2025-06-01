import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.2

This file is a translation of Section 4.2 of Analysis I to Lean 4.  All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.
-/

namespace Section_4_2

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r := fun a b ↦ a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl := by sorry
    symm := by sorry
    trans := by sorry
    }

@[simp]
theorem PreRat.eq (a b c d:ℤ) (hb: b ≠ 0) (hd: d ≠ 0): (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

abbrev Rat := Quotient PreRat.instSetoid

/-- We give division a "junk" value of 0//1 if the denominator is zero -/
abbrev Rat.formalDiv (a b:ℤ)  : Int := Quotient.mk PreInt.instSetoid if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩

infix:70 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0): a // b = c // d ↔ a * d = c * b := by
  simp [hb, hd]
  constructor
  . exact Quotient.exact
  intro h; exact Quotient.sound h

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq_diff (n:Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quot.ind _ n; intro ⟨ a, b, h ⟩
  use a, b; refine ⟨ h, ?_ ⟩
  simp [Rat.formalDiv, h]

/-- Lemma 4.2.3 (Addition well-defined) -/
theorem Rat.add_congr_left (a b a' b' c d : ℤ) (hb: b ≠ 0) (hb': b' ≠ 0) (hd: d ≠ 0) (h: a // b = a' // b') : (a*d+b*c) // (b*d) = (a'*d+b'*c) // (b'*d) := by
  have hbd: b*d ≠ 0 := by sorry
  have hb'd: b'*d ≠ 0 := by sorry
  simp only [Rat.eq _ _ hb hb', Rat.eq _ _ hbd hb'd] at h ⊢
  calc
    _ = (a*b')*d*d + b*b'*c*d := by ring
    _ = (a'*b)*d*d + b*b'*c*d := by rw [h]
    _ = _ := by ring

theorem Rat.add_congr_right (a b c d c' d' : ℤ) (hb: b ≠ 0) (hd: d ≠ 0) (hd': d' ≠ 0) (h: c // d = c' // d') : (a*d+b*c) // (b*d) = (a*d'+b*c') // (b*d') := by sorry

theorem Rat.add_congr (a b c d a' b' c' d' : ℤ) (hb: b ≠ 0) (hb': b' ≠ 0) (hd: d ≠ 0) (hd': d' ≠ 0) (h: a // b = a' // b') : (a*d+b*c) // (b*d) = (a*d'+b*c') // (b*d') := by sorry


/-- Lemma 4.2.3 (Addition well-defined) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intros ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h1 h2
    simp [Setoid.r] at *
    exact Rat.add_congr_left a b a' b' c d c' d' h1 h1' h2 h2')

end Section_4_2
