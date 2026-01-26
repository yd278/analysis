import Mathlib.Tactic
import Analysis.Section_5_1


/-!
# Analysis I, Section 5.2: Equivalent Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of an ε-close and eventually ε-close sequences of rationals.
- Notion of an equivalent Cauchy sequence of rationals.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


abbrev Rat.CloseSeq (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Rat.EventuallyClose (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∃ N, ε.CloseSeq (a.from N) (b.from N)

namespace Chapter5

/-- Definition 5.2.1 ($ε$-close sequences) -/
lemma Rat.closeSeq_def (ε: ℚ) (a b: Sequence) :
    ε.CloseSeq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n) := by rfl

/-- Example 5.2.2 -/
example : (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  intro n hn1 hn2
  simp at hn1 hn2
  simp[Rat.Close,hn2]
  lift n to ℕ using hn1
  simp;ring_nf
  rw[abs_mul];simp
  rw[abs_of_neg];norm_num;grind


/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence) := by
  simp
  use 0; simp
  use 1;simp
  simp[Rat.Close]
  norm_num

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  simp
  use 0; simp
  use 1;simp
  simp[Rat.Close,abs]
  norm_num

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_def (ε: ℚ) (a b: Sequence) :
    ε.EventuallyClose a b ↔ ∃ N, ε.CloseSeq (a.from N) (b.from N) := by rfl

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_iff (ε: ℚ) (a b: ℕ → ℚ) :
    ε.EventuallyClose (a:Sequence) (b:Sequence) ↔ ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
      constructor
      . rintro ⟨N,h⟩ 
        use N.toNat;intro n hn
        specialize h n
        simp at h;
        simp[Int.toNat_le] at hn
        specialize h hn
        simp[hn] at h
        assumption
      rintro ⟨N,h⟩ 
      use N
      intro n; simp; intro hn
      lift n to ℕ using by grind
      norm_cast at hn
      simp[hn]
      specialize h n hn
      assumption

/-- Example 5.2.5 -/
example : ¬ (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
    simp; use 0; simp
    simp[Rat.Close]
    simp[abs];norm_num

example : (0.1:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
    use 1; intro n hn1 hn2
    simp at hn1 hn2
    lift n to ℕ using by grind
    simp[hn1,Rat.Close]
    ring_nf; rw[abs_of_pos (by positivity)]
    suffices h: (10:ℚ) ^ (-1 - n:ℤ ) ≤ 1 / 10 / 2 from by
      rw[le_div_iff₀',mul_comm] at h; 
      assumption; simp
    rw[neg_sub_left,zpow_neg]
    norm_num;simp
    rw[inv_le_inv₀ (by positivity ) (by simp)]
    norm_cast
    calc
      _ <= 10 ^ 2 := by simp
      _ <= _ := by apply pow_le_pow <;> grind

example : (0.01:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
    use 2; intro n hn1 hn2
    simp at hn1 hn2
    lift n to ℕ using by grind
    simp[hn1,Rat.Close]
    ring_nf; rw[abs_of_pos (by positivity)]
    suffices h: (10:ℚ) ^ (-1 - n:ℤ ) ≤ 1 / 100 / 2 from by
      rw[le_div_iff₀',mul_comm] at h; 
      assumption; simp
    rw[neg_sub_left,zpow_neg]
    norm_num;simp
    rw[inv_le_inv₀ (by positivity ) (by simp)]
    norm_cast
    calc
      _ <= 10 ^ 3 := by simp
      _ <= _ := by apply pow_le_pow <;> grind

/-- Definition 5.2.6 (Equivalent sequences) -/
abbrev Sequence.Equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.EventuallyClose (a:Sequence) (b:Sequence)

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_def (a b: ℕ → ℚ) :
    Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose (a:Sequence) (b:Sequence) := by rfl

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_iff (a b: ℕ → ℚ) : Equiv a b ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  constructor
  . 
    intro heq ε hε 
    specialize heq ε hε
    choose N hClose using heq
    use N.toNat 
    intro n hn
    simp[Int.toNat_le] at hn
    specialize hClose n; simp[hn] at hClose
    assumption
  intro heq ε hε 
  specialize heq ε hε 
  choose N hC using heq
  use N
  intro n hn1 hn2
  simp at hn1 hn2
  lift n to ℕ using by grind
  simp at hn1 hn2
  specialize hC n hn1
  simp[hn1]
  assumption

/-- Proposition 5.2.8 -/
lemma Sequence.equiv_example :
  -- This proof is perhaps more complicated than it needs to be; a shorter version may be
  -- possible that is still faithful to the original text.
  Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)
  rw [equiv_iff]
  intro ε hε
  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := calc
    _ = |((1:ℚ) + (10:ℚ)^(-(n:ℤ)-1)) - ((1:ℚ) - (10:ℚ)^(-(n:ℤ)-1))| := rfl
    _ = |2 * (10:ℚ)^(-(n:ℤ)-1)| := by ring_nf
    _ = _ := abs_of_nonneg (by positivity)
  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn; rw [hab n]; gcongr; norm_num
  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := calc
      _ = 2 / (10:ℚ)^(N+1) := by
        field_simp
        simp [mul_assoc, ←Section_4_3.pow_eq_zpow, ←zpow_add₀ (show 10 ≠ (0:ℚ) by norm_num)]
      _ ≤ _ := by
        gcongr
        apply le_trans _ (pow_le_pow_left₀ (show 0 ≤ (2:ℚ) by norm_num)
          (show (2:ℚ) ≤ 10 by norm_num) _)
        convert Nat.cast_le.mpr (Section_4_3.two_pow_geq (N+1)) using 1 <;> try infer_instance
        all_goals simp
    choose N hN using exists_nat_gt (2 / ε)
    refine ⟨ N, (hN' N).trans ?_ ⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    grind [mul_comm]
  choose N hN using hN; use N; intro n hn
  linarith [hab' N n hn]

/-- Exercise 5.2.1 -/
lemma Sequence.Equiv.symm  {a b : ℕ → ℚ}  (hab : Equiv a b) : Equiv b a := by
  intro ε hε 
  specialize hab ε hε 
  choose N hEC using hab
  use N
  intro n hnb hna
  specialize hEC n hnb hna
  simp at hnb
  simp [hnb,Rat.Close] at hEC ⊢ 
  rwa[abs_sub_comm]

lemma Sequence.isCauchy_of_equiv_mp {a b: ℕ → ℚ} (hab : Equiv a b) (ha : (a:Sequence).IsCauchy) :
    (b:Sequence).IsCauchy:= by

      intro ε hε 
      specialize ha (ε/3) (by simp[hε]) 
      choose N hN hC using ha
      specialize hab (ε/3) (by simp[hε]) 
      choose N' heq using hab
      simp at hN
      use max N N'
      simp[hN]
      intro n hn m hm
      simp at hn hm
      specialize hC n
      simp[hn] at hC
      specialize hC m
      simp[hm] at hC
      simp[hn,hm]
      have neq := heq n
      simp[hn] at neq
      have meq := heq m
      simp[hm] at meq
      rw[Section_4_3.close_symm] at neq
      have := Section_4_3.close_trans neq hC
      have := Section_4_3.close_trans this meq
      ring_nf at this
      assumption

theorem Sequence.isCauchy_of_equiv {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy ↔ (b:Sequence).IsCauchy := by
      constructor
      . intro ha; exact isCauchy_of_equiv_mp hab ha
      intro hb; have hba := Equiv.symm hab
      exact isCauchy_of_equiv_mp hba hb

/-- Exercise 5.2.2 -/

lemma eventuallyClose_symm {ε :ℚ} {a b : ℕ → ℚ} (hab: ε.EventuallyClose a b): ε.EventuallyClose b a:= by
  choose N hN using hab
  use N
  intro n hnb hna
  specialize hN n hna hnb
  simp at hnb
  simp[hnb,Rat.Close] at hN ⊢
  rwa[abs_sub_comm]
  
lemma Sequence.isBounded_of_eventuallyClose.mp {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) (ha: (a:Sequence).IsBounded ) :
    (b:Sequence).IsBounded := by
      choose U hU hBona  using ha
      choose N hCab using hab
      -- later
      have hlater : ((b:Sequence).from N).BoundedBy (U + |ε|):= by
        intro n; simp
        specialize hCab n; simp at hCab
        by_cases hn : 0 ≤ n
        . lift n to ℕ using hn
          by_cases hn' : N ≤ n
          simp at hn'
          . simp[hn'] at hCab ⊢ 
            simp[Rat.Close] at hCab
            have hbon := hBona n; simp at hbon
            rw[abs_sub_comm] at hCab
            have : b n = a n + (b n - a n) := by simp
            rw[this]
            calc
             _ <= |a n| + |b n - a n| := by apply abs_add
             _ <= U + ε := by grind
             _ <= _ := by simp; exact le_abs_self ε 
          simp[hn'] at hCab ⊢ 
          have : 0 ≤ |ε| := by simp
          grind
        simp[hn]
        have : 0 ≤ |ε| := by simp
        grind
      -- finite part
      set b' : Fin N.toNat → ℚ := fun i ↦ b i
      choose U' hU' hBonb using IsBounded.finite b'
      use max U' (U + |ε|)
      simp[hU']
      intro n 
      by_cases hn : 0 ≤ n
      .
        simp[hn] at ⊢ 
        by_cases hn' : n < N
        . left
          specialize hBonb ⟨n.toNat ,by simp;grind⟩ 
          simpa[b'] using hBonb
        right
        specialize hlater n
        push_neg at hn'
        simpa[hn,hn'] using hlater
      simp[hn,hU']
theorem Sequence.isBounded_of_eventuallyClose {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded ↔ (b:Sequence).IsBounded := by
      constructor
      . intro ha; exact isBounded_of_eventuallyClose.mp hab ha
      intro hb; have hba := eventuallyClose_symm hab
      exact isBounded_of_eventuallyClose.mp hba hb


end Chapter5
