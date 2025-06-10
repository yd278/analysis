import Mathlib.Tactic

/-!
# Analysis I, Section 6.1

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

-

-/


/- Definition 6.1.1 (Distance).  Here we use the Mathlib distance. -/
#check Real.dist_eq

abbrev Real.close (ε x y : ℝ) : Prop := dist x y ≤ ε

/-- Definition 6.1.2 (ε-close). This is similar to the previous notion of ε-closeness, but where all quantities are real instead of rational. -/
theorem Real.close_def (ε x y : ℝ) : ε.close x y ↔ dist x y ≤ ε := by rfl

namespace Chapter6

/-- Definition 6.1.3 (Sequence). This is similar to the Chapter 5 sequence, except that now the sequence is real-valued. As with Chapter 5, we start sequences from 0 by default. -/
@[ext]
structure Sequence where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n, n < m → seq n = 0

/-- Sequences can be thought of as functions from ℤ to ℝ. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℝ) where
  coe := fun a ↦ a.seq

/-- Functions from ℕ to ℝ can be thought of as sequences. -/
instance Sequence.instCoe : Coe (ℕ → ℝ) Sequence where
  coe := fun a ↦ {
    m := 0
    seq := fun n ↦ if n ≥ 0 then a n.toNat else 0
    vanish := by
      intro n hn
      simp [hn]
  }

abbrev Sequence.mk' (m:ℤ) (a: { n // n ≥ m } → ℝ) : Sequence where
  m := m
  seq := fun n ↦ if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by
    intro n hn
    simp [hn]


lemma Sequence.eval_mk {n m:ℤ} (a: { n // n ≥ m } → ℝ) (h: n ≥ m) : (Sequence.mk' m a) n = a ⟨ n, h ⟩ := by simp [seq, h]

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℝ) : (a:Sequence) n = a n := by simp [seq]

/-- a.from n₁ starts `a:Sequence` from `n₁`.  It is intended for use when `n₁ ≥ n₀`, but returns the "junk" value of the original sequence `a` otherwise. -/
abbrev Sequence.from (a:Sequence) (m₁:ℤ) : Sequence :=
  mk' (max a.m m₁) (fun n ↦ a (n:ℤ))

lemma Sequence.from_eval (a:Sequence) {m₁ n:ℤ} (hn: n ≥ m₁) :
  (a.from m₁) n = a n := by
  simp [Sequence.from, seq, hn]
  intro h
  exact (a.vanish n h).symm

end Chapter6

/-- Definition 6.1.3 (ε-steady) -/
abbrev Real.steady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∀ n ≥ a.m, ∀ m ≥ a.m, ε.close (a n) (a m)

/-- Definition 6.1.3 (ε-steady) -/
lemma Real.steady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.steady a ↔ ∀ n ≥ a.m, ∀ m ≥ a.m, ε.close (a n) (a m) := by rfl

/-- Definition 6.1.3 (Eventually ε-steady) -/
abbrev Real.eventuallySteady (ε: ℝ) (a: Chapter6.Sequence) : Prop := ∃ N ≥ a.m, ε.steady (a.from N)

/-- Definition 6.1.3 (Eventually ε-steady) -/
lemma Real.eventuallySteady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.eventuallySteady a ↔ ∃ N, (N ≥ a.m) ∧ ε.steady (a.from N) := by rfl


namespace Chapter6

/-- Definition 6.1.3 (Cauchy sequence) -/
abbrev Sequence.isCauchy (a:Sequence) : Prop := ∀ ε > (0:ℝ), ε.eventuallySteady a

/-- Definition 6.1.3 (Cauchy sequence) -/
lemma Sequence.isCauchy_def (a:Sequence) :
  a.isCauchy ↔ ∀ ε > (0:ℝ), ε.eventuallySteady a := by rfl

lemma Sequence.isCauchy_of_coe (a:ℕ → ℝ) : (a:Sequence).isCauchy ↔ ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, dist (a j) (a k) ≤ ε := by sorry

lemma Sequence.isCauchy_of_mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℝ) : (mk' n₀ a).isCauchy ↔ ∀ ε > 0, ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N, dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by sorry




end Chapter6
