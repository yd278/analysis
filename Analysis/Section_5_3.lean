import Mathlib.Tactic
import Analysis.Section_5_2
import Mathlib.Algebra.Group.MinimalAxioms


/-!
# Analysis I, Section 5.3

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

@[simp]
theorem CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).isCauchy) : (mk' ha).toSequence = (a:Sequence) := by rfl

instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe := fun a n ↦ a.toSequence (n:ℤ)

@[simp]
theorem CauchySequence.coe_to_sequence (a: CauchySequence) : ((a:ℕ → ℚ):Sequence) = a.toSequence := by
  apply Sequence.ext
  . rw [a.zero]
  ext n
  by_cases h:n ≥ 0
  all_goals simp [h]
  rw [a.vanish]
  rw [a.zero]
  exact lt_of_not_ge h

@[simp]
theorem CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).isCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
theorem Sequence.equiv_trans {a b c:ℕ → ℚ} (hab: Sequence.equiv a b) (hbc: Sequence.equiv b c) :
  Sequence.equiv a c := by sorry

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

theorem LIM_def {a:ℕ → ℚ} (ha: (a:Sequence).isCauchy) : LIM a = Quotient.mk _ (CauchySequence.mk' ha) := by
  rw [LIM, dif_pos ha]

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (a:Sequence).isCauchy ∧ x = LIM a := by
  -- I had a lot of trouble with this proof; perhaps there is a more idiomatic way to proceed
  apply Quot.ind _ x; intro a
  set a' : ℕ → ℚ := (a:ℕ → ℚ); use a'
  set s : Sequence := (a':Sequence)
  have : s = a.toSequence := CauchySequence.coe_to_sequence a
  rw [this]
  refine ⟨ a.cauchy, ?_ ⟩
  congr
  convert (dif_pos a.cauchy).symm with n
  . apply CauchySequence.ext'
    change a.seq = s.seq
    rw [this]
  classical
  exact Classical.propDecidable _

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.lim_eq_lim (a b:ℕ → ℚ) (ha: (a:Sequence).isCauchy) (hb: (b:Sequence).isCauchy) :
  LIM a = LIM b ↔ Sequence.equiv a b := by
  constructor
  . intro h
    replace h := Quotient.exact h
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff] at h
  intro h
  apply Quotient.sound
  rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]

/--Lemma 5.3.6 (Sum of Cauchy sequences is Cauchy)-/
theorem Sequence.add_cauchy {a b:ℕ → ℚ}  (ha: (a:Sequence).isCauchy) (hb: (b:Sequence).isCauchy) : (a + b:Sequence).isCauchy := by
  -- This proof is written to follow the structure of the original text.
  rw [isCauchy_def] at ha hb ⊢
  intro ε hε
  have : ε/2 > 0 := by exact half_pos hε
  replace ha := ha (ε/2) this
  replace hb := hb (ε/2) this
  rw [Rat.eventuallySteady_def] at ha hb ⊢
  obtain ⟨ N, hN, hha ⟩ := ha
  obtain ⟨ M, hM, hhb ⟩ := hb
  use max N M
  simp at hN hM ⊢
  simp [hN, Rat.steady_def'] at hha hhb ⊢
  intro n m hnN hnM hmN hmM
  have hn := hN.trans hnN
  have hm := hM.trans hmM
  replace hha := hha n m hnN hmN
  replace hhb := hhb n m hn hnM hm hmM
  simp [hn, hm, hnN, hnM, hmN, hmM] at hha hhb ⊢
  convert Section_4_3.add_close hha hhb
  ring

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Sequence.equiv a a') :
  Sequence.equiv (a + b) (a' + b) := by
  -- This proof is written to follow the structure of the original text.
  rw [equiv_def] at haa' ⊢
  obtain ⟨ ε, hε, haa' ⟩ := haa'
  use ε, hε
  rw [Rat.eventually_close_def] at haa' ⊢
  obtain ⟨ N, haa' ⟩ := haa'
  use N
  rw [Rat.close_seq_def] at haa' ⊢
  simp at haa' ⊢
  intro n hn hN _ _
  replace haa' := haa' n hn hN hn hN
  simp [hn, hN] at haa' ⊢
  convert Section_4_3.add_close haa' (Section_4_3.close_refl (b n.toNat))
  simp

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Sequence.equiv b b') :
  Sequence.equiv (a + b) (a + b') := by
  simp_rw [add_comm, add_equiv_left a hbb']

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv {a b a' b':ℕ → ℚ} (haa': Sequence.equiv a a') (hbb': Sequence.equiv b b') :
  Sequence.equiv (a + b) (a' + b') := equiv_trans (add_equiv_left b haa') (add_equiv_right a' hbb')

/-- Definition 5.3.4 (Addition of reals) -/
noncomputable instance Real.add_inst : Add Real where
  add := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a + b)) (by
      intro a b a' b' haa' hbb'
      change LIM ((a:ℕ → ℚ) + (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) + (b':ℕ → ℚ))
      rw [lim_eq_lim]
      . exact Sequence.add_equiv haa' hbb'
      all_goals apply Sequence.add_cauchy
      all_goals rw [CauchySequence.coe_to_sequence]
      . exact a.cauchy
      . exact b.cauchy
      . exact a'.cauchy
      exact b'.cauchy
      )

/--Proposition 5.3.10 (Product of Cauchy sequences is Cauchy)-/
theorem Sequence.mul_cauchy {a b:ℕ → ℚ}  (ha: (a:Sequence).isCauchy) (hb: (b:Sequence).isCauchy) : (a * b:Sequence).isCauchy := by
  sorry

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Sequence.equiv a a') :
  Sequence.equiv (a * b) (a' * b) := by
  sorry

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Sequence.equiv b b') :
  Sequence.equiv (a * b) (a * b') := by
  simp_rw [mul_comm, mul_equiv_left a hbb']

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv {a b a' b':ℕ → ℚ} (haa': Sequence.equiv a a') (hbb': Sequence.equiv b b') :
  Sequence.equiv (a * b) (a' * b') := equiv_trans (mul_equiv_left b haa') (mul_equiv_right a' hbb')

/-- Definition 5.3.9 (Product of reals) -/
noncomputable instance Real.mul_inst : Mul Real where
  mul := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a * b)) (by
      intro a b a' b' haa' hbb'
      change LIM ((a:ℕ → ℚ) * (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) * (b':ℕ → ℚ))
      rw [lim_eq_lim]
      . exact Sequence.mul_equiv haa' hbb'
      all_goals apply Sequence.mul_cauchy
      all_goals rw [CauchySequence.coe_to_sequence]
      . exact a.cauchy
      . exact b.cauchy
      . exact a'.cauchy
      exact b'.cauchy
      )

instance Real.instRatCast : RatCast Real where
  ratCast := fun q ↦
    Quotient.mk _ (CauchySequence.mk' (a := fun _ ↦ q) (Sequence.isCauchy_of_const q))

theorem Real.ratCast_def (q:ℚ) : (q:Real) = LIM (fun _ ↦ q) := by
  rw [LIM_def]
  rfl

/-- Exercise 5.3.3 -/
@[simp]
theorem Real.ratCast_inj (q r:ℚ) : (q:Real) = (r:Real) ↔ q = r := by
  sorry

instance Real.instOfNat {n:ℕ} : OfNat Real n where
  ofNat := ((n:ℚ):Real)

instance Real.instNatCast : NatCast Real where
  natCast n := ((n:ℚ):Real)

instance Real.instIntCast : IntCast Real where
  intCast n := ((n:ℚ):Real)

theorem Real.add_of_ratCast (a b:ℚ) : (a:Real) + (b:Real) = (a+b:ℚ) := by sorry

theorem Real.mul_of_ratCast (a b:ℚ) : (a:Real) * (b:Real) = (a*b:ℚ) := by sorry

noncomputable instance Real.instNeg : Neg Real where
  neg := fun x ↦ ((-1:ℚ):Real) * x

theorem Real.neg_of_ratCast (a:ℚ) : -(a:Real) = (-a:ℚ) := by sorry

/-- It may be possible to omit the Cauchy sequence hypothesis here. -/
theorem Real.neg_of_LIM (a:ℕ → ℚ) (ha: (a:Sequence).isCauchy) : -LIM a = LIM (-a) := by sorry

/-- Proposition 5.3.11 -/
noncomputable instance Real.addGroup_inst : AddGroup Real :=
AddGroup.ofLeftAxioms (by sorry) (by sorry) (by sorry)

theorem Real.sub_eq_add_neg (x y:Real) : x - y = x + (-y) :=  rfl

/-- It may be possible to omit the Cauchy sequence hypothesis here. -/
theorem Real.sub_of_LIM (a b:ℕ → ℚ) (ha: (a:Sequence).isCauchy) (hb: (b:Sequence).isCauchy) :
  LIM a - LIM b = LIM (a - b) := by sorry

/-- Proposition 5.3.12 (laws of algebra) -/
noncomputable instance Real.instAddCommGroup : AddCommGroup Real where
  add_comm := by sorry

/-- Proposition 5.3.12 (laws of algebra) -/
noncomputable instance Real.instCommMonoid : CommMonoid Real where
  mul_comm := by sorry
  mul_assoc := by sorry
  one_mul := by sorry
  mul_one := by sorry

/-- Proposition 5.3.12 (laws of algebra) -/
noncomputable instance Real.instCommRing : CommRing Real where
  left_distrib := by sorry
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry
  natCast_succ := by sorry
  intCast_negSucc := by sorry

abbrev Real.ratCast_hom : ℚ →+* Real where
  toFun := RatCast.ratCast
  map_zero' := by sorry
  map_one' := by sorry
  map_add' := by sorry
  map_mul' := by sorry

/-- Definition 5.3.12 (sequences bounded away from zero).  Sequences are indexed to start from zero as this is more convenient for Mathlib purposes. -/
abbrev bounded_away_zero (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c

theorem bounded_away_zero_def (a:ℕ → ℚ) : bounded_away_zero a ↔
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c := by rfl

/-- Examples 5.3.13 -/
example : bounded_away_zero (fun n ↦ (-1)^n) := by sorry

/-- Examples 5.3.13 -/
example : ¬ bounded_away_zero (fun n ↦ 10^(-(n:ℤ)-1)) := by sorry

/-- Examples 5.3.13 -/
example : ¬ bounded_away_zero (fun n ↦ 1 - 10^(-(n:ℤ))) := by sorry

/-- Examples 5.3.13 -/
example : bounded_away_zero (fun n ↦ 10^(n+1)) := by sorry

/-- Examples 5.3.13 -/
example : ((fun (n:ℕ) ↦ (10:ℚ)^(n+1)):Sequence).isBounded := by sorry

/-- Lemma 5.3.14 -/
theorem bounded_away_zero_of_nonzero {x:Real} (hx: x ≠ 0) : ∃ a:ℕ → ℚ, (a:Sequence).isCauchy ∧ x = LIM a := by
  -- This proof is written to follow the structure of the original text.
  sorry -- TODO

/-- Lemma 5.3.15 -/
theorem inv_of_bounded_away_zero_cauchy {a:ℕ → ℚ} (ha: bounded_away_zero a) (ha_cauchy: (a:Sequence).isCauchy) :
  ((a⁻¹:ℕ → ℚ):Sequence).isCauchy := by
  -- This proof is written to follow the structure of the original text.
  sorry -- TODO

/-- Lemma 5.3.17 (Reciprocation is well-defined) -/
theorem inv_of_equiv {a b:ℕ → ℚ} (ha: bounded_away_zero a) (ha_cauchy: (a:Sequence).isCauchy) (hb: bounded_away_zero b) (hb_cauchy: (b:Sequence).isCauchy) (hlim: LIM a = LIM b) :
  LIM a⁻¹ = LIM b⁻¹ := by
  -- This proof is written to follow the structure of the original text.
  sorry -- TODO

end Chapter5
