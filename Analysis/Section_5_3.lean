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
class CauchySequence extends Sequence where
  zero : n₀ = 0
  cauchy : toSequence.isCauchy

/-- A sequence starting at zero that is Cauchy, can be viewed as a Cauchy sequence.-/
abbrev CauchySequence.mk' {a:ℕ → ℚ} (ha: (a:Sequence).isCauchy) : CauchySequence where
  n₀ := 0
  seq := (a:Sequence).seq
  vanish := by
    intro n hn
    exact (a:Sequence).vanish n hn
  zero := rfl
  cauchy := ha

lemma CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).isCauchy) : (mk' ha).toSequence = (a:Sequence) := by rfl

instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe := fun a n ↦ a.toSequence (n:ℤ)

lemma CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).isCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.equiv a b
  iseqv := {
     refl := sorry
     symm := sorry
     trans := sorry
  }





end Chapter5
