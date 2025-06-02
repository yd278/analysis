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

/-- Functions from ℕ to ℚ can be thought of as sequences. -/
instance Sequence.instCoe : Coe (ℕ → ℚ) Sequence :=
  ⟨ fun a ↦ Sequence.mk 0 (fun n ↦ a (n:ℤ).toNat) ⟩

/-- It is convenient to extend sequences by zero, to become functions on all of ℤ.  Unfortunately this extension isn't quite injective, so we cannot use the machinery of `FunLike`.  (One could use the machinery of `Function.extend`, however.) -/
abbrev Sequence.extend (s: Sequence) (n:ℤ) : ℚ := if h : n ≥ s.n₀ then s.a ⟨n, h⟩ else 0

lemma Sequence.extend_mk {n n₀:ℤ} (a: { n // n ≥ n₀ } → ℚ) (h: n ≥ n₀) : (Sequence.mk n₀ a).extend n = a ⟨ n, h ⟩ := by simp [Sequence.extend, h]

@[simp]
lemma Sequence.extend_coe (n:ℕ) (a: ℕ → ℚ) : (a:Sequence).extend n = a n := by simp [Sequence.extend]

/-- Example 5.1.2 -/
abbrev Sequence.squares : Sequence := ((fun n:ℕ ↦ (n^2:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.squares.extend n = n^2 := Sequence.extend_coe _ _

/-- Example 5.1.2 -/
abbrev Sequence.three : Sequence := ((fun (_:ℕ) ↦ (3:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.three.extend n = 3 := Sequence.extend_coe _ (fun (_:ℕ) ↦ (3:ℚ))

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

/-- Example 5.1.5 -/
example : (1:ℚ).steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by sorry

/-- Example 5.1.5 -/
example : ¬ (0.5:ℚ).steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by sorry

/-- Example 5.1.5 -/
example : (0.1:ℚ).steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by sorry

/-- Example 5.1.5 -/
example : ¬(0.01:ℚ).steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by sorry

/-- Example 5.1.5 -/
example (ε:ℚ) : ¬ ε.steady ((fun n:ℕ ↦ (2 ^ (n+1):ℚ) ):Sequence) := by sorry

/-- Example 5.1.5 -/
example (ε:ℚ) (hε: ε>0) : ε.steady ((fun _:ℕ ↦ (2:ℚ) ):Sequence) := by sorry

example : (10:ℚ).steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by sorry

example (ε:ℚ) (hε:ε<10):  ¬ ε.steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by sorry

/-- a.from n₁ starts `a:Sequence` from `n₁`.  It is intended for use when `n₁ \geq n₀`, but returns the "junk" value of the original sequence `a` otherwise. -/
abbrev Sequence.from (a:Sequence) (n₁:ℤ) : Sequence :=
  Sequence.mk (max a.n₀ n₁) (fun ⟨ n, hn ⟩ ↦ a.a ⟨ n, (le_max_left _ _).trans hn ⟩)

lemma Sequence.from_extend (a:Sequence) {n₁ n:ℤ} (hn: n ≥ n₁) :
  (a.from n₁).extend n = a.extend n := by
  simp [Sequence.from, Sequence.extend, hn]

end Section_5_1

/-- Definition 5.1.6 (Eventually ε-steady) -/
abbrev Rat.eventuallySteady (ε: ℚ) (s: Section_5_1.Sequence) : Prop := ∃ N, (N ≥ s.n₀) ∧ ε.steady (s.from N)

namespace Section_5_1

lemma Rat.eventuallySteady_def (ε: ℚ) (s: Sequence) :
  ε.eventuallySteady s ↔ ∃ N, (N ≥ s.n₀) ∧ ε.steady (s.from N) := by rfl

/-- Example 5.1.7 -/
lemma Sequence.ex_5_1_7_a : ¬ (0.1:ℚ).steady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) := by sorry

lemma Sequence.ex_5_1_7_b : (0.1:ℚ).steady (((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence).from 10) := by sorry

lemma Sequence.ex_5_1_7_c : (0.1:ℚ).eventuallySteady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) := by sorry

lemma Sequence.ex_5_1_7_d {ε:ℚ} (hε:ε>0) : ε.eventuallySteady ((fun n:ℕ ↦ if n=0 then (10:ℚ) else (0:ℚ) ):Sequence) := by sorry

abbrev Sequence.isCauchy (s:Sequence) : Prop := ∀ (ε:ℚ), (ε > 0 → (ε.eventuallySteady s))

lemma Sequence.isCauchy_def (s:Sequence) :
  s.isCauchy ↔ ∀ (ε:ℚ), (ε > 0 → ε.eventuallySteady s) := by rfl

lemma Sequence.isCauchy_of_coe (a:ℕ → ℚ) : (a:Sequence).isCauchy ↔ ∀ (ε:ℚ), ε > 0 → ∃ N, ∀ j k, j ≥ N ∧ k ≥ N → Section_4_3.dist (a j) (a k) ≤ ε := by sorry

lemma Sequence.isCauchy_of_mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℚ) : (Sequence.mk n₀ a).isCauchy ↔ ∀ (ε:ℚ), ε > 0 → ∃ N, N ≥ n₀ ∧ ∀ j k, j ≥ N ∧ k ≥ N → Section_4_3.dist ((Sequence.mk n₀ a).extend j) ((Sequence.mk n₀ a).extend k) ≤ ε := by sorry

noncomputable def Sequence.sqrt_two : Sequence := (fun n:ℕ ↦ ((⌊ (Real.sqrt 2)*10^n ⌋ / 10^n):ℚ))

/-- Example 5.1.10.  (This requires extensive familiarity with Mathlib's API for the real numbers. )-/
theorem Sequence.ex_5_1_10_a : (1:ℚ).steady Sequence.sqrt_two := by sorry

/-- Example 5.1.10.  (This requires extensive familiarity with Mathlib's API for the real numbers. )-/
theorem Sequence.ex_5_1_10_b : (0.1:ℚ).steady (Sequence.sqrt_two.from 1) := by sorry

theorem Sequence.ex_5_1_10_c : (0.1:ℚ).eventuallySteady Sequence.sqrt_two := by sorry

/-- Proposition 5.1.11 -/
theorem Sequence.harmonic_steady : (Sequence.mk 1 (fun n ↦ (1:ℚ)/n)).isCauchy := by
  -- This is proof is probably longer than it needs to be; there should be a shorter proof that is still in the spirit of  the proof in the book.
  rw [isCauchy_of_mk (fun n ↦ (1:ℚ)/n)]
  intro ε hε
  have : ∃ N:ℕ, N > 1/ε := exists_nat_gt (1 / ε)
  obtain ⟨ N, hN ⟩ := this
  use N
  have hN' : (N:ℤ) > 0 := by
    have : (1/ε) > 0 := by positivity
    replace hN := this.trans hN
    simp at hN ⊢; assumption
  constructor
  . simp at hN' ⊢; linarith
  intro j k ⟨ hj, hk ⟩
  have hj' : (j:ℚ) ≥ 0 := by simp; linarith
  have hj'' : (1:ℚ)/j ≤ (1:ℚ)/N := by
    gcongr
    . simp at hN' ⊢; assumption
    . simp at hj ⊢; qify at hj; assumption
  have hj''' : (1:ℚ)/j ≥ 0 := by positivity
  have hj'''' : j ≥ 1 := by simp at hj'; linarith
  have hk' : (k:ℚ) ≥ 0 := by simp; linarith
  have hk'' : (1:ℚ)/k ≤ (1:ℚ)/N := by
    gcongr
    . simp at hN' ⊢; assumption
    . simp at hk ⊢; qify at hk; assumption
  have hk''' : (1:ℚ)/k ≥ 0 := by positivity
  have hk'''' : k ≥ 1 := by simp at hk'; linarith
  have hdist : Section_4_3.dist ((1:ℚ)/j) ((1:ℚ)/k) ≤ (1:ℚ)/N := by
    rw [Section_4_3.dist_eq, abs_le']
    constructor <;> linarith
  simp [Sequence.extend, hj'''', hk'''']
  convert hdist.trans _ using 2
  . simp
  . simp
  rw [div_le_iff₀, mul_comm, ←div_le_iff₀ hε]
  . exact le_of_lt hN
  simp at hN' ⊢; assumption



end Section_5_1
