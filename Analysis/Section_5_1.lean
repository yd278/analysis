import Mathlib.Tactic
import Analysis.Section_4_3

/-!
# Analysis I, Section 5.1

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of a sequence of rationals
- Notions of `ε`-steadiness, eventual `ε`-steadiness, and Cauchy sequences

-/

namespace Section_5_1

/-- Definition 5.1.1 (Sequence) -/
structure Sequence where
  n₀ : ℤ
  a : { n // n ≥ n₀ } → ℚ

lemma Sequence.mk_eq (n₀:ℤ) (a: { n // n ≥ n₀ } → ℚ) : Sequence.mk n₀ a = ⟨ n₀, a ⟩ := by rfl

abbrev Sequence.mk_nat (a:ℕ → ℚ) : Sequence :=
  Sequence.mk 0 (fun n ↦ a (n:ℤ).toNat)

/-- It is convenient to extend sequences by zero, to become functions on all of ℤ.  Unfortunately this extension isn't quite injective, so we cannot use the machinery of `Funlike`. -/
abbrev Sequence.extend (s: Sequence) (n:ℤ) : ℚ := if h : n ≥ s.n₀ then s.a ⟨n, h⟩ else 0

lemma Sequence.extend_mk {n n₀:ℤ} (a: { n // n ≥ n₀ } → ℚ) (h: n ≥ n₀) : (Sequence.mk n₀ a).extend n = a ⟨ n, h ⟩ := by simp [Sequence.extend, h]

lemma Sequence.extend_mk_nat (n:ℕ) (a: ℕ → ℚ) : (Sequence.mk_nat a).extend n = a n := by simp [Sequence.extend]

/-- Example 5.1.2 -/
abbrev Sequence.squares : Sequence := Sequence.mk_nat (fun n ↦ n^2)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.squares.extend n = n^2 := Sequence.extend_mk_nat _ _

/-- Example 5.1.2 -/
abbrev Sequence.three : Sequence := Sequence.mk_nat (fun _ ↦ 3)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.three.extend n = 3 := Sequence.extend_mk_nat _ _

/-- Example 5.1.2 -/
abbrev Sequence.squares_from_three : Sequence := Sequence.mk 3 (fun n ↦ n^2)

/-- Example 5.1.2 -/
example (n:ℤ) (hn: n ≥ 3) : Sequence.squares_from_three.extend n = n^2 := Sequence.extend_mk _ hn

-- need to temporarily leave the `Section_5_1` namespace to introduce the following notation

end Section_5_1

abbrev Rat.steady (ε: ℚ) (s: Section_5_1.Sequence) : Prop :=
  ∀ n m, ε.close (s.a n) (s.a m)

namespace Section_5_1

lemma Rat.steady_def (ε: ℚ) (s: Sequence) :
  ε.steady s ↔ ∀ n m, ε.close (s.a n) (s.a m) := by rfl

lemma Rat.steady_def' (ε: ℚ) (s: Sequence) :
  ε.steady s ↔ ∀ n m, n ≥ s.n₀ ∧ m ≥ s.n₀ → ε.close (s.extend n) (s.extend m) := by
  rw [Rat.steady_def]
  constructor
  . intro h n m ⟨ hn, hm ⟩
    sorry
  intro h n m
  sorry

end Section_5_1
