import Mathlib.Tactic
import Analysis.Section_5_1
import Analysis.Section_5_3
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.1: Convergence and limit laws

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of $ε$-closeness, $ε$-steadiness, and their eventual counterparts.
- Notion of a Cauchy sequence, convergent sequence, and bounded sequence of reals.

-/


/- Definition 6.1.1 (Distance).  Here we use the Mathlib distance. -/
#check Real.dist_eq

abbrev Real.Close (ε x y : ℝ) : Prop := dist x y ≤ ε

/--
  Definition 6.1.2 (ε-close). This is similar to the previous notion of ε-closeness, but where
  all quantities are real instead of rational.
-/
theorem Real.close_def (ε x y : ℝ) : ε.Close x y ↔ dist x y ≤ ε := by rfl

namespace Chapter6

/--
  Definition 6.1.3 (Sequence). This is similar to the Chapter 5 sequence, except that now the
  sequence is real-valued. As with Chapter 5, we start sequences from 0 by default.
-/
@[ext]
structure Sequence where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Sequences can be thought of as functions from ℤ to ℝ. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℝ) where
  coe a := a.seq

@[coe]
abbrev Sequence.ofNatFun (a:ℕ → ℝ) : Sequence :=
 {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by simp_all
 }

/-- Functions from ℕ to ℝ can be thought of as sequences. -/
instance Sequence.instCoe : Coe (ℕ → ℝ) Sequence where
  coe := ofNatFun

abbrev Sequence.mk' (m:ℤ) (a: { n // n ≥ m } → ℝ) : Sequence where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by simp_all

lemma Sequence.eval_mk {n m:ℤ} (a: { n // n ≥ m } → ℝ) (h: n ≥ m) :
    (Sequence.mk' m a) n = a ⟨ n, h ⟩ := by simp [h]

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℝ) : (a:Sequence) n = a n := by simp

/--
  a.from n₁ starts `a:Sequence` from `n₁`.  It is intended for use when `n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence `a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (m₁:ℤ) : Sequence := mk' (max a.m m₁) (a ↑·)

lemma Sequence.from_eval (a:Sequence) {m₁ n:ℤ} (hn: n ≥ m₁) :
  (a.from m₁) n = a n := by
  simp [hn]; intros; symm; solve_by_elim [a.vanish]

end Chapter6

/-- Definition 6.1.3 (ε-steady) -/
abbrev Real.Steady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m)

/-- Definition 6.1.3 (ε-steady) -/
lemma Real.steady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m) := by rfl

/-- Definition 6.1.3 (Eventually ε-steady) -/
abbrev Real.EventuallySteady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.Steady (a.from N)

/-- Definition 6.1.3 (Eventually ε-steady) -/
lemma Real.eventuallySteady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.EventuallySteady a ↔ ∃ N, (N ≥ a.m) ∧ ε.Steady (a.from N) := by rfl

/-- For fixed s, the function ε ↦ ε.Steady s is monotone -/
theorem Real.Steady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂) (hsteady: ε₁.Steady a) :
    ε₂.Steady a := by grind

/-- For fixed s, the function ε ↦ ε.EventuallySteady s is monotone -/
theorem Real.EventuallySteady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂)
  (hsteady: ε₁.EventuallySteady a) :
    ε₂.EventuallySteady a := by peel 2 hsteady; grind [Steady.mono]

namespace Chapter6

/-- Definition 6.1.3 (Cauchy sequence) -/
abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℝ), ε.EventuallySteady a

/-- Definition 6.1.3 (Cauchy sequence) -/
lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℝ), ε.EventuallySteady a := by rfl

/-- This is almost the same as Chapter5.Sequence.IsCauchy.coe -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, dist (a j) (a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩
    lift N to ℕ using hN; use N
    intro j hj k hk
    simp [Real.steady_def] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all
  rintro ⟨ N, h' ⟩; refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := by omega
  have mpos : 0 ≤ m := by omega
  simp [hn, hm, npos, mpos]
  lift n to ℕ using npos
  lift m to ℕ using mpos
  specialize h' n ?_ m ?_ <;> try grind

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℝ) :
    (mk' n₀ a).IsCauchy
    ↔ ∀ ε > 0, ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N, dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩; refine ⟨ N, hN, ?_ ⟩
    dsimp at hN
    intro j hj k hk
    simp only [Real.Steady, show max n₀ N = N by omega] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
  rintro ⟨ N, _, _ ⟩; use max n₀ N; grind

@[coe]
abbrev Sequence.ofChapter5Sequence (a: Chapter5.Sequence) : Sequence :=
{
  m := a.n₀
  seq n := a n
  vanish n hn := by simp [a.vanish n hn]
}

instance Chapter5.Sequence.inst_coe_sequence : Coe Chapter5.Sequence Sequence where
  coe := Sequence.ofChapter5Sequence

@[simp]
theorem Chapter5.coe_sequence_eval (a: Chapter5.Sequence) (n:ℤ) : (a:Sequence) n = (a n:ℝ) := rfl

theorem Sequence.is_steady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.Steady a ↔ (ε:ℝ).Steady (a:Sequence) := by
      simp[Rat.Steady,Real.steady_def,Rat.Close,dist]
      congr! with n hn m hm
      norm_cast

theorem Sequence.is_eventuallySteady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.EventuallySteady a ↔ (ε:ℝ).EventuallySteady (a:Sequence) := by
      simp[Rat.EventuallySteady ,Real.EventuallySteady]
      congr! 3 with N
      have : (a:Sequence).from N = (a.from N) := by grind
      rw[this]
      exact is_steady_of_rat ε (a.from N)

/-- Proposition 6.1.4 -/
theorem Sequence.isCauchy_of_rat (a: Chapter5.Sequence) : a.IsCauchy ↔ (a:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  constructor
  swap
  . intro h; rw [isCauchy_def] at h
    rw [Chapter5.Sequence.isCauchy_def]
    intro ε hε
    specialize h ε (by positivity)
    rwa [is_eventuallySteady_of_rat]
  intro h
  rw [Chapter5.Sequence.isCauchy_def] at h
  rw [isCauchy_def]
  intro ε hε
  choose ε' hε' hlt using exists_pos_rat_lt hε
  specialize h ε' hε'
  rw [is_eventuallySteady_of_rat] at h
  exact h.mono (le_of_lt hlt)

end Chapter6

/-- Definition 6.1.5 -/
abbrev Real.CloseSeq (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop := ∀ n ≥ a.m, ε.Close (a n) L

/-- Definition 6.1.5 -/
theorem Real.closeSeq_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.CloseSeq a L ↔ ∀ n ≥ a.m, dist (a n) L ≤ ε := by rfl

/-- Definition 6.1.5 -/
abbrev Real.EventuallyClose (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop :=
  ∃ N ≥ a.m, ε.CloseSeq (a.from N) L

/-- Definition 6.1.5 -/
theorem Real.eventuallyClose_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.EventuallyClose a L ↔ ∃ N, (N ≥ a.m) ∧ ε.CloseSeq (a.from N) L := by rfl

theorem Real.CloseSeq.coe (ε : ℝ) (a : ℕ → ℝ) (L : ℝ):
  (ε.CloseSeq a L) ↔ ∀ n, dist (a n) L ≤ ε := by
  constructor
  . intro h n; specialize h n; grind
  . intro h n hn; lift n to ℕ using (by omega); specialize h n; grind

theorem Real.CloseSeq.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.CloseSeq a L) :
    ε₂.CloseSeq a L := by peel 2 hclose; rw [Real.Close, Real.dist_eq] at *; linarith

theorem Real.EventuallyClose.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.EventuallyClose a L) :
    ε₂.EventuallyClose a L := by peel 2 hclose; grind [CloseSeq.mono]
namespace Chapter6

abbrev Sequence.TendsTo (a:Sequence) (L:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.EventuallyClose a L

theorem Sequence.tendsTo_def (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > (0:ℝ), ε.EventuallyClose a L := by rfl

/-- Exercise 6.1.2 -/
theorem Sequence.tendsTo_iff (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| ≤ ε := by
    congr! 2 with ε hε 
    rw[Real.eventuallyClose_def]
    constructor<;> intro h
    . choose N hN hclose using h
      use N; intro n hn
      have hnm : n ≥ a.m := by linarith
      simp[Real.closeSeq_def] at hclose
      specialize hclose n hnm hn
      simpa [hnm,hn,dist] using hclose
    choose N hdist using h
    use max N a.m
    simp[Real.closeSeq_def]
    peel 2 hdist with n hn hdist
    intro hnm
    simpa[hnm,hn,dist]

noncomputable def seq_6_1_6 : Sequence := (fun (n:ℕ) ↦ 1-(10:ℝ)^(-(n:ℤ)-1):Sequence)

/-- Examples 6.1.6 -/
example : (0.1:ℝ).CloseSeq seq_6_1_6 1 := by
  rw [seq_6_1_6, Real.CloseSeq.coe]
  intro n
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by
    rw [sub_nonneg]
    rw (occs := .pos [2]) [show (1:ℝ) = 1 - 0 by norm_num]
    gcongr
    positivity
  ), sub_sub_cancel, show (0.1:ℝ) = (10:ℝ)^(-1:ℤ) by norm_num]
  gcongr <;> grind


/-- Examples 6.1.6 -/
example : ¬ (0.01:ℝ).CloseSeq seq_6_1_6 1 := by
  intro h; specialize h 0 (by positivity); simp [seq_6_1_6] at h; norm_num at h

/-- Examples 6.1.6 -/
example : (0.01:ℝ).EventuallyClose seq_6_1_6 1 := by
  use 1
  simp[seq_6_1_6, Real.closeSeq_def]
  intro n hn 
  have hn0 : 0 ≤ n := by linarith
  simp[hn,hn0]
  calc
   _ ≤ (10:ℝ) ^ ((-1:ℤ) - 1) := by gcongr;simp
   _ = _ := by simp;norm_num

/-- Examples 6.1.6 -/
example : seq_6_1_6.TendsTo 1 := by
  rw[seq_6_1_6,Sequence.tendsTo_def]
  intro ε hε 
  have hpow : ∃ (N:ℤ), (10:ℝ) ^(-N - 1) < ε := by
    simp only [neg_sub_left,zpow_neg,← inv_zpow]
    have hltone : (10:ℝ)⁻¹ < 1 := by norm_num
    choose N' hN' using exists_pow_lt_of_lt_one hε hltone
    use N'-1; simp_all
  choose N hN using hpow
  use max N 0
  simp[Real.closeSeq_def]
  intro n hnN hn0 
  simp[hnN,hn0]
  apply le_trans ?_ (le_of_lt hN)
  gcongr;simp

/-- Proposition 6.1.7 (Uniqueness of limits) -/
theorem Sequence.tendsTo_unique (a:Sequence) {L L':ℝ} (h:L ≠ L') :
    ¬ (a.TendsTo L ∧ a.TendsTo L') := by
  -- This proof is written to follow the structure of the original text.
  by_contra this
  choose hL hL' using this
  replace h : L - L' ≠ 0 := by grind
  replace h : |L-L'| > 0 := by positivity
  set ε := |L-L'| / 3
  have hε : ε > 0 := by positivity
  rw [tendsTo_iff] at hL hL'
  specialize hL ε hε; choose N hN using hL
  specialize hL' ε hε; choose M hM using hL'
  set n := max N M
  specialize hN n (by omega)
  specialize hM n (by omega)
  have : |L-L'| ≤ 2 * |L-L'|/3 := calc
    _ = dist L L' := by rw [Real.dist_eq]
    _ ≤ dist L (a.seq n) + dist (a.seq n) L' := dist_triangle _ _ _
    _ ≤ ε + ε := by rw [←Real.dist_eq] at hN hM; rw [dist_comm] at hN; gcongr
    _ = 2 * |L-L'|/3 := by grind
  linarith

/-- Definition 6.1.8 -/
abbrev Sequence.Convergent (a:Sequence) : Prop := ∃ L, a.TendsTo L

/-- Definition 6.1.8 -/
theorem Sequence.convergent_def (a:Sequence) : a.Convergent ↔ ∃ L, a.TendsTo L := by rfl

/-- Definition 6.1.8 -/
abbrev Sequence.Divergent (a:Sequence) : Prop := ¬ a.Convergent

/-- Definition 6.1.8 -/
theorem Sequence.divergent_def (a:Sequence) : a.Divergent ↔ ¬ a.Convergent := by rfl

open Classical in
/--
  Definition 6.1.8.  We give the limit of a sequence the junk value of 0 if it is not convergent.
-/
noncomputable abbrev lim (a:Sequence) : ℝ := if h: a.Convergent then h.choose else 0

/-- Definition 6.1.8 -/
theorem Sequence.lim_def {a:Sequence} (h: a.Convergent) : a.TendsTo (lim a) := by
  simp [lim, h]; exact h.choose_spec

/-- Definition 6.1.8-/
theorem Sequence.lim_eq {a:Sequence} {L:ℝ} :
a.TendsTo L ↔ a.Convergent ∧ lim a = L := by
  constructor
  . intro h; by_contra! eq
    have : a.Convergent := by rw [convergent_def]; use L
    replace eq := a.tendsTo_unique (eq this)
    apply lim_def at this; tauto
  intro ⟨ h, rfl ⟩; convert lim_def h


/-- Proposition 6.1.11 -/
theorem Sequence.lim_harmonic :
    ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  rw [←lim_eq, tendsTo_iff]
  intro ε hε
  choose N hN using exists_int_gt (1 / ε); use N; intro n hn
  have hNpos : (N:ℝ) > 0 := by apply LT.lt.trans _ hN; positivity
  simp at hNpos
  have hnpos : n ≥ 0 := by linarith
  simp [hnpos, abs_inv]
  calc
    _ ≤ (N:ℝ)⁻¹ := by
      rw [inv_le_inv₀] <;> try positivity
      calc
        _ ≤ (n:ℝ) := by simp [hn]
        _ = (n.toNat:ℤ) := by simp [hnpos]
        _ = n.toNat := rfl
        _ ≤ (n.toNat:ℝ) + 1 := by linarith
        _ ≤ _ := le_abs_self _
    _ ≤ ε := by
      rw [inv_le_comm₀] <;> try positivity
      rw [←inv_eq_one_div _] at hN; order

/-- Proposition 6.1.12 / Exercise 6.1.5 -/
theorem Real.dist_le (x y z:ℝ) : dist x z ≤ dist x y + dist y z := by
  simp[dist]
  set a := x - y;
  set b := y - z;
  rw[show x - z = a + b by simp[a,b]] 
  exact abs_add a b
theorem Real.close_trans {ε δ x y z:ℝ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by
      simp[dist] at hxy hyz
      have := dist_le x y z
      simp[dist] at this
      calc  
        _ ≤ |x - y| + |y - z| := by exact this
        _ ≤ _ := by simp[add_le_add hxy hyz]
theorem Real.close_comm {ε x y :ℝ}: ε.Close x y ↔  ε.Close y x := by
  simp[dist]
  rw[abs_sub_comm]

theorem Sequence.IsCauchy.convergent {a:Sequence} (h:a.Convergent) : a.IsCauchy := by
  intro ε hε 
  choose L hL using h
  specialize hL (ε/2) (by linarith) 
  choose N hNam hclose using hL
  use N
  refine ⟨hNam, ?_⟩ 
  intro i hi j hj
  have haiL := hclose i  hi
  have hajL := hclose j  hj
  simp at hi hj
  rw[Real.close_comm] at hajL
  convert Real.close_trans haiL hajL
  simp

/-- Example 6.1.13 -/
example : ¬ (0.1:ℝ).EventuallySteady ((fun n ↦ (-1:ℝ)^n):Sequence) := by
  by_contra! h
  choose N hN hS using h
  simp at hN
  have hN1 : N + 1 ≥ 0 := by linarith
  specialize hS N (by simpa) (N+1) (by simpa)
  lift N to ℕ using hN
  simp[hN1,dist,pow_succ] at hS
  have : |(-1:ℝ) ^ N + (-1:ℝ) ^ N| = 2 := by
    ring_nf
    simp[abs_mul]
  rw[this] at hS
  linarith

/-- Example 6.1.13 -/
example : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).IsCauchy := by
  by_contra h
  specialize h 0.1 (by norm_num)
  choose N hN hst using h
  simp at hN
  have hN1 : N+1 ≥ 0 := by linarith
  specialize hst N (by simpa) (N+1) (by simpa)
  lift N to ℕ using hN
  simp[hN1,dist,pow_succ] at hst
  have : |(-1:ℝ) ^ N + (-1:ℝ) ^ N| = 2 := by
    ring_nf
    simp[abs_mul]
  rw[this] at hst
  linarith

/-- Example 6.1.13 -/
example : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).Convergent := by
  by_contra h
  choose L hL using h
  specialize hL 0.1 (by linarith)
  choose N hN hst using hL
  simp at hN
  have hN1 : N+1 ≥ 0 := by linarith
  have hL1 := hst N (by simpa)
  simp[hN] at hL1
  have hL0 := hst (N+1) (by simpa)
  simp[hN1] at hL0
  lift N to ℕ using hN
  simp[pow_succ] at hL0 hL1
  rw[← Real.close_def] at hL1 hL0
  rw[Real.close_comm] at hL0
  have := Real.close_trans hL1 hL0
  simp[dist] at this
  have hcon: |(-1:ℝ) ^ N + (-1:ℝ) ^ N| = 2 := by
    ring_nf
    simp[abs_mul]
  rw[hcon] at this
  linarith

/-- Proposition 6.1.15 / Exercise 6.1.6 (Formal limits are genuine limits)-/
lemma Chapter5.Real.map_ratCast {q:ℚ} : (q:ℝ) = Chapter5.Real.equivR (q:Chapter5.Real) := by
  have := _root_.map_ratCast Chapter5.Real.equivR_ordered_ring q
  rw[← this]
  rfl


lemma Chapter5.Real.map_sub {x y:Chapter5.Real} :  Chapter5.Real.equivR (x - y) = Chapter5.Real.equivR x - Chapter5.Real.equivR y  := by
  convert Chapter5.Real.equivR_ordered_ring.map_sub x y




theorem Sequence.lim_eq_LIM {a:ℕ → ℚ} (h: (a:Chapter5.Sequence).IsCauchy) :
    ((a:Chapter5.Sequence):Sequence).TendsTo (Chapter5.Real.equivR (Chapter5.LIM a)) := by
      -- denotations
      set LR := Chapter5.LIM a
      set L := Chapter5.Real.equivR LR
      intro ε hε 
      set εR := Chapter5.Real.equivR.symm ε 
      observe hεR : ε = Chapter5.Real.equivR εR
      -- we want to prove that for all ε:
      -- There exists an N, where for all n > N, dist (a n) L  ≤ ε 
      -- we can convert it into dist (a n) LR ≤ ε' (which is a Rat < ε) 
      -- we know that for an ε'
      choose εQ hεQ0 hεQ using exists_pos_rat_lt hε 
      have hεQR : εQ < εR := by
        rwa[hεR,Chapter5.Real.map_ratCast,Chapter5.Real.map_lt_map_iff] at hεQ 

      obtain ⟨N,hac⟩  := Chapter5.Sequence.LIM_all_close h hεQ0
      use N;simp
      intro n hn ;simp at hn
      lift n to ℕ using (by linarith);simp at hn
      specialize hac n hn
      choose hacu hacb using hac
      simp[dist,hn,abs_le]
      split_ands
      . 
        suffices h: L ≤ (a n) + εQ from by linarith
        simp only [L,
        Chapter5.Real.map_ratCast,
        ←Chapter5.Real.map_add,
        Chapter5.Real.map_le_map_iff
        ]
        assumption
      suffices h: (a n) - εQ ≤  L from by linarith
      simp only[
        L,
        Chapter5.Real.map_ratCast,
        ← Chapter5.Real.map_sub,
        Chapter5.Real.map_le_map_iff
      ]
      assumption


/-- Definition 6.1.16 -/
abbrev Sequence.BoundedBy (a:Sequence) (M:ℝ) : Prop :=
  ∀ n, |a n| ≤ M

/-- Definition 6.1.16 -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℝ) :
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

/-- Definition 6.1.16 -/
abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 6.1.16 -/
lemma Sequence.isBounded_def (a:Sequence) :
  a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl
lemma Sequence.IsBounded.steady {a: Sequence} {ε :ℝ }(ha: ε.Steady a) (hε : ε ≥ 0) : ∃M ≥ 0 , a.BoundedBy M := by
  specialize ha a.m (by simp)
  set a₀ := |a a.m|
  observe ha₀: a₀ ≥ 0
  use a₀ + ε
  refine⟨ add_nonneg ha₀ hε ,?_⟩ 
  intro m
  specialize ha m
  by_cases hm : m >= a.m
  . specialize ha hm
    set aₘ := |a.seq m|
    simp[dist] at ha
    apply le_add_of_sub_left_le
    rw[abs_sub_comm] at ha
    have : aₘ - a₀ <= |a m - a a.m| := by
      have := abs_add (a m - a a.m) (a a.m)
      have : aₘ <= |a m - a a.m| + a₀ := by
        simp[aₘ,a₀]
        simpa[sub_add_cancel] using this
      exact abs_sub_abs_le_abs_sub (a.seq m) (a.seq a.m)
    grind
  push_neg at hm
  have := a.vanish m hm
  simp[this]
  calc
    _ <= a₀ := by simp[a₀]
    _ <= _ := by grind




lemma Sequence.IsBounded.finite {N:ℕ} (a: ℕ → ℝ) (ha : ∀ n ≥ N, a n = 0): ∃ M ≥ 0,  BoundedBy a M := by
  induction' N with k hind generalizing a
  . use 0
    simp[boundedBy_def]
    intro n hn; lift n to ℕ using hn
    specialize ha n (by simp)
    simpa
  set a' : ℕ → ℝ := fun n ↦ if n = k then 0 else a n
  have ha' : ∀ n ≥ k, a' n = 0 := by
    intro n hn
    by_cases htail : n ≥ k+1 
    . have : n ≠ k := by linarith
      simp[a',this]
      apply ha n htail
    have : n = k := by linarith
    simp[a',this]
  choose  M0 hM0 hMb using hind a' ha'
  simp[boundedBy_def,a'] at hMb
  use max M0 |a k|
  simp[boundedBy_def]
  peel hMb with n hMb
  by_cases hn : n ≥ 0
  . 
    lift n to ℕ using hn 
    simp at hMb ⊢ 
    by_cases hnk : n = k
    . right; simp[hnk]
    left; simpa[hnk] using hMb
  simp[hn] at hMb ⊢ 

theorem Sequence.bounded_of_cauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  specialize h 1 (by simp)
  choose N hN hste using h
  rw[ge_iff_le,le_iff_exists_nonneg_add] at hN
  choose c hc hdiff using hN
  lift c to ℕ using hc
  have hbon1 := Sequence.IsBounded.steady (hste) (by simp)
  obtain ⟨u1, hu1, hbon1⟩ := hbon1
  set a' : ℕ  → ℝ := fun i ↦ if i < c then a (a.m +i) else 0
  have ha' : ∀ n > c, a' n = 0 := by simp[a'];intro n hn hn';linarith
  choose u2 hu2 hbon2 using Sequence.IsBounded.finite a' ha'
  use max u1 u2
  split_ands
  . simp;tauto
  intro i
  by_cases hi : i >= N
  . specialize hbon1 i
    rw[from_eval _ hi] at hbon1
    simp;left;assumption
  push_neg at hi
  by_cases hi' : i >= a.m
  . 
    rw[ge_iff_le,le_iff_exists_nonneg_add] at hi'
    choose c' hc hca using hi'
    lift c' to ℕ using hc
    have hcc': c' < c := by
      simpa[← hca,← hdiff] using hi
    have : a i = a' c' := by
      simp[a',hca]
      intro hcon;linarith
    simp[this];right
    specialize hbon2 c' 
    assumption
  push_neg at hi'
  have := a.vanish i hi'
  simp[this];tauto


/-- Corollary 6.1.17 -/
theorem Sequence.bounded_of_convergent {a:Sequence} (h: a.Convergent) : a.IsBounded := by
  have hac : a.IsCauchy  := by
    exact IsCauchy.convergent h
  exact bounded_of_cauchy hac

/-- Example 6.1.18 -/
lemma Sequence.example_6_1_18 : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).IsBounded := by
  by_contra! hcon
  rw[Sequence.isBounded_def] at hcon
  choose M hM hBon using hcon
  rw[Sequence.boundedBy_def] at hBon
  choose n hn using  exists_int_gt M
  specialize hBon (max 0 n)
  simp at hBon
  have : |((max 0 n).toNat :ℝ )+ 1| ≥ n := by 
    norm_cast
    simp
    calc
      _ ≤ max 0 n := by simp
      _ ≤ _ := by simp
  linarith

/-- Example 6.1.18 -/
example : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).Convergent := by
  have := Sequence.example_6_1_18
  contrapose! this
  exact Sequence.bounded_of_convergent this

instance Sequence.inst_add : Add Sequence where
  add a b := {
    m := min a.m b.m
    seq n := a n + b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.add_eval {a b: Sequence} (n:ℤ) : (a + b) n = a n + b n := rfl

theorem Sequence.add_coe (a b: ℕ → ℝ) : (a:Sequence) + (b:Sequence) = (fun n ↦ a n + b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(a) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_add {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
  (a+b).TendsTo (L+M) := by
    intro ε hε
    specialize ha (ε/2) (by positivity)
    specialize hb (ε/2) (by positivity)
    choose Na hNa hNac using ha
    choose Nb hNb hNbc using hb
    use max Na Nb
    split_ands
    . rw[show (a+b).m = min a.m b.m by rfl]; grind
    intro n hn
    simp at hn
    simp[hn,dist]
    specialize hNac n (by grind)
    simp[hn,show a.m ≤ n by linarith,dist] at hNac
    specialize hNbc n (by grind)
    simp[hn,show b.m ≤ n by linarith,dist] at hNbc
    calc
      _ = |(a n - L) + (b n - M)| := by ring_nf
      _ ≤ |a n - L| + |b n - M| := by apply abs_add_le
      _ ≤ ε/2 + ε /2 := add_le_add hNac hNbc
      _ = _ := by simp

theorem Sequence.lim_add {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
  (a + b).Convergent ∧ lim (a + b) = lim a + lim b := by
    choose L ha using ha
    choose M hb using hb
    have hten := tendsTo_add ha hb
    rw[lim_eq] at hten ha hb
    refine ⟨hten.1,?_⟩ 
    rw[ha.2,hb.2,hten.2]

instance Sequence.inst_mul : Mul Sequence where
  mul a b := {
    m := min a.m b.m
    seq n := a n * b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.mul_eval {a b: Sequence} (n:ℤ) : (a * b) n = a n * b n := rfl

theorem Sequence.mul_coe (a b: ℕ → ℝ) : (a:Sequence) * (b:Sequence) = (fun n ↦ a n * b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(b) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
lemma Real.Close.mul_mul {ε δ x y z w:ℝ}  (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|y|).Close (x * z) (y * w) := by
      set a := x-y
      have ha : x = y + a := by grind
      have haε : |a| <= ε := by simpa[dist] using hxy
      set b := w-z
      have hb : w = z + b := by grind
      have hbδ: |b| ≤ δ := by simpa[dist,abs_sub_comm,b] using hzw
      have : x * z - y * w = a * z - b * y := by grind
      simp[dist]
      rw[this]
      calc
        _ <= |a*z| + |b*y| := by apply abs_sub
        _ <= |a| * |z| + |b| * |y| := by simp[abs_mul]
        _ <= ε * |z| + δ * |y| := by gcongr
lemma Real.Close.mono {ε δ x y :ℝ} (hxy : ε.Close x y) (hεδ : δ ≥ ε ) : δ.Close x y:= by
  simp[dist] at hxy ⊢ 
  linarith
theorem Sequence.tendsTo_mul {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a * b).TendsTo (L * M) := by
      observe hac : a.Convergent 
      observe hbc : b.Convergent 
      choose ub hbu0 hbub using bounded_of_convergent hbc
      intro ε hε
      specialize ha (ε/2/(max ub 1)) (by 
        apply div_pos (half_pos hε) (by simp)
      ) 
      specialize hb (ε/2/(max |L| 1)) (by 
        apply div_pos (half_pos hε) (by simp)
      )
      choose Na hNa ha using ha
      choose Nb hNb hb using hb
      use (max Na Nb)
      split_ands 
      . rw[show (a*b).m = min a.m b.m by rfl]; grind
      intro n hn
      simp at hn
      simp[hn]
      specialize ha n (by grind)
      specialize hb n (by grind)
      simp[hn,show a.m ≤ n by linarith] at ha
      simp[hn,show b.m ≤ n by linarith] at hb
      have := Real.Close.mul_mul ha hb
      apply Real.Close.mono this
      have  hex : max ub 1 ≥ |b n| := by
        simp;left
        exact hbub n
      have hf1 : ε /2 / (max ub 1) * |b n| ≤ ε /2 := by
        calc 
          _ ≤ ε /2 / (max ub 1) * (max ub 1) := by gcongr
          _ = _ := by rw[div_mul_cancel₀]; have : max ub 1 ≥ 1 := (by simp); linarith
      have hf2 : ε/2 / (max |L| 1) * |L| ≤ ε /2 := by 
        calc
          _ ≤ ε/2/(max |L| 1) * (max |L| 1) := by gcongr;simp
          _ = _ := by rw[div_mul_cancel₀]; have : max |L| 1 ≥ 1 :=(by simp); linarith
      linarith




theorem Sequence.lim_mul {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a * b).Convergent ∧ lim (a * b) = lim a * lim b := by
    choose L ha using ha
    choose M hb using hb
    have hten := tendsTo_mul ha hb
    rw[lim_eq] at hten ha hb
    refine ⟨hten.1,?_⟩ 
    rw[ha.2,hb.2,hten.2]


instance Sequence.inst_smul : SMul ℝ Sequence where
  smul c a := {
    m := a.m
    seq n := c * a n
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.smul_eval {a: Sequence} (c: ℝ) (n:ℤ) : (c • a) n = c * a n := rfl

theorem Sequence.smul_coe (c:ℝ) (a:ℕ → ℝ) : (c • (a:Sequence)) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Theorem 6.1.19(c) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_smul (c:ℝ) {a:Sequence} {L:ℝ} (ha: a.TendsTo L) :
    (c • a).TendsTo (c * L) := by
      observe hac : a.Convergent 
      intro ε hε
      specialize ha (ε/max |c| 1) (by 
        apply div_pos hε (by simp)
      ) 
      choose Na hNa ha using ha
      use Na
      split_ands 
      . rwa[show (c • a).m = a.m by rfl]
      intro n hn
      simp at hn
      simp[hn,dist]
      specialize ha n (by grind)
      simp[hn,show a.m ≤ n by linarith,dist] at ha
      rw[show c * a n - c * L = c * (a n - L) by ring]
      rw[abs_mul]
      calc
        _ ≤ |c| * (ε / max |c| 1) := by gcongr
        _ = ε / max |c| 1 * |c| := by ring
        _ ≤ ε / max |c| 1 * max |c| 1 := by gcongr; simp
        _ = _ := by rw[div_mul_cancel₀]; have : max |c| 1 ≥ 1 := (by simp); linarith

theorem Sequence.lim_smul (c:ℝ) {a:Sequence} (ha: a.Convergent) :
    (c • a).Convergent ∧ lim (c • a) = c * lim a := by
    choose L ha using ha
    have hten := tendsTo_smul c ha
    rw[lim_eq] at hten ha 
    refine ⟨hten.1,?_⟩ 
    rw[ha.2,hten.2]

instance Sequence.inst_sub : Sub Sequence where
  sub a b := {
    m := min a.m b.m
    seq n := a n - b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.sub_eval {a b: Sequence} (n:ℤ) : (a - b) n = a n - b n := rfl

theorem Sequence.sub_coe (a b: ℕ → ℝ) : (a:Sequence) - (b:Sequence) = (fun n ↦ a n - b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(d) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_sub {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a - b).TendsTo (L - M) := by
      suffices h : (a + (-1:ℝ) • b).TendsTo (L + -1 * M) from by
        have : a + (-1:ℝ) • b = a - b := by
          ext x
          . rfl
          simp;ring
        simp[this] at h
        simpa
      apply tendsTo_add ha
      apply tendsTo_smul _ hb

theorem Sequence.LIM_sub {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a - b).Convergent ∧ lim (a - b) = lim a - lim b := by
    choose L ha using ha
    choose M hb using hb
    have hten := tendsTo_sub ha hb
    rw[lim_eq] at hten ha hb
    refine ⟨hten.1,?_⟩ 
    rw[ha.2,hb.2,hten.2]

instance Sequence.inst_neg : Neg Sequence where
  neg a := {
    m := a.m
    seq n := - a n 
    vanish n hn := by simp;apply a.vanish _ hn
  }

@[simp]
theorem Sequence.neg_eval {a: Sequence} (n:ℤ) : (-a) n = - a n := rfl

theorem Sequence.neg_coe (a : ℕ → ℝ) : (-a:Sequence)   = (fun n ↦ - a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

abbrev Sequence.const (r:ℝ) (m:ℤ) : Sequence where 
  m := m
  seq n := if n ≥ m then r else 0
  vanish n hn := by simp; intro; linarith 

lemma Sequence.tendsTo_const (r:ℝ) (m:ℤ) : (const r m).TendsTo r := by
  intro ε hε
  use m;simp
  intro n hn
  simp at hn
  simp[dist,hn]
  linarith

theorem Sequence.tendsTo_neg {a:Sequence} {L:ℝ} (ha: a.TendsTo L) :
  (-a).TendsTo (-L) := by
    have hz := tendsTo_const 0 a.m
    have : -a = (const 0 a.m) - a := by
      ext n
      . change a.m = min a.m a.m
        simp
      simp
    rw[this]
    rw[show -L = 0 - L by simp]
    apply tendsTo_sub hz ha
noncomputable instance Sequence.inst_inv : Inv Sequence where
  inv a := {
    m := a.m
    seq n := (a n)⁻¹
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.inv_eval {a: Sequence} (n:ℤ) : (a⁻¹) n = (a n)⁻¹ := rfl
theorem Sequence.inv_coe (a: ℕ → ℝ) : (a:Sequence)⁻¹ = (fun n ↦ (a n)⁻¹) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(e) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_inv {a:Sequence} {L:ℝ} (ha: a.TendsTo L) (hnon: L ≠ 0) :
    (a⁻¹).TendsTo (L⁻¹) := by
      have hmeq : a⁻¹.m = a.m := by rfl
      wlog hpos: L > 0
      . have hneg : L < 0 := by push_neg at hpos;grind
        set a':= (-1:ℝ) • a
        have ha' : a'.TendsTo (-L) := by 
          simp[a']
          have :=  tendsTo_smul (-1) ha 
          simpa
        specialize this ha' (by simpa) (by rfl) (by linarith)
        have : ((-1:ℝ)• (a'⁻¹)).TendsTo L⁻¹ := by
          have hrev := tendsTo_smul (-1) this
          simpa using hrev
        simp[a'] at this
        have hrev : (-1:ℝ) • ((-1:ℝ)• a)⁻¹ = a⁻¹ := by
          ext n
          . rfl
          simp
        rwa[hrev] at this
      -- now only consider positive L
      intro ε hε 
      by_cases hεL : ε ≥ L⁻¹
      . specialize ha (L/2) (by positivity)
        choose N hN ha using ha
        use N
        split_ands
        . rwa[hmeq]
        suffices h: L⁻¹.CloseSeq (a⁻¹.from N) L⁻¹ from by
          peel h with n hn h
          apply Real.Close.mono h (by linarith)
        intro n hn
        simp at hn
        simp[hn,dist,abs_le]
        specialize ha n (by simpa[← hmeq])
        simp[← hmeq,dist,hn,abs_le] at ha
        choose hal hau using ha
        have hapos : a n > 0 := by
          rw[← sub_le_iff_le_add]  at hal
          linarith
        refine ⟨le_of_lt hapos,?_⟩ 
        have hahalf : L/2 ≤ a n:= by
          rw[← sub_le_iff_le_add]  at hal
          linarith
        calc
          _ ≤ (L / 2) ⁻¹ := by rwa[inv_le_inv₀ hapos (by positivity)]
          _ = _ := by ring
      --- for those always pos values
      push_neg at hεL 
      set ε'u := L^2*ε /(1 - L * ε)
      have hudenpos : (1 - L * ε) > 0 := by
        simp
        calc 
          _ < L * L⁻¹ := by gcongr
          _ = _ := by field_simp
      have hldenpos : (1 + L * ε) > 0 := by
        have : L * ε > 0 := mul_pos hpos hε 
        linarith
      set ε'l := L^2*ε / (1 + L*ε)
      have hεul : ε'u > ε'l := by
        simp[ε'u ,ε'l]
        gcongr
        rw[sub_eq_add_neg]
        gcongr;simp
        apply mul_pos hpos hε 
      have hεpos : ε'l > 0 := by
        simp[ε'l]
        apply div_pos (mul_pos ?_ hε) ?_
        apply sq_pos_of_pos hpos
        linarith
      specialize ha ε'l hεpos
      choose N hN ha using ha
      use N; rw[hmeq];simp[hN]
      peel ha with n hn ha
      simp at hn
      simp[dist,← hmeq,hn,abs_le] at ha
      choose hal hau using ha
      replace hal : a n ≥ L - ε'l := by simpa
      replace hau : a n ≤ L + ε'u := by
        apply le_trans hau (by rw[add_comm]; gcongr)
      have hapos : a n > 0 := by
        suffices h: L - ε'l > 0 from by linarith
        simp[ε'l] 
        rw[div_lt_comm₀ hldenpos hpos]
        calc 
          _ = L^2/L * ε := by ring
          _ = L * ε := by simp;left;field_simp;exact pow_two L
          _ < _ := by  linarith
      simp[dist,hn,abs_le]
      -- now there are just algebras
      split_ands
      . 
        rw[← sub_le_iff_le_add]
        apply le_inv_of_le_inv₀  hapos
        calc 
          _ ≤ L + ε'u := hau
          _ = _ := by simp[ε'u];field_simp;ring
      apply inv_le_of_inv_le₀ 
      linarith
      calc
        _ = L - ε'l := by simp[ε'l];field_simp;ring
        _ ≤ _ := hal

theorem Sequence.lim_inv {a:Sequence} (ha: a.Convergent) (hnon: lim a ≠ 0) :
  (a⁻¹).Convergent ∧ lim (a⁻¹) = (lim a)⁻¹ := by
    choose L ha using ha
    have hten := tendsTo_inv  ha (by rw[lim_eq] at ha;rwa[← ha.2])
    rw[lim_eq] at hten ha 
    refine ⟨hten.1,?_⟩ 
    rw[ha.2,hten.2]

noncomputable instance Sequence.inst_div : Div Sequence where
  div a b := {
    m := min a.m b.m
    seq n := a n / b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.div_eval {a b: Sequence} (n:ℤ) : (a / b) n = a n / b n := rfl

theorem Sequence.div_coe (a b: ℕ → ℝ) : (a:Sequence) / (b:Sequence) = (fun n ↦ a n / b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(f) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_div {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) (hnon: M ≠ 0) :
    (a / b).TendsTo (L / M) := by
      have hbinv := tendsTo_inv hb hnon
      have hseq : a / b = a * (b⁻¹) := by
        ext x <;> rfl
      rw[hseq,div_eq_mul_inv]
      exact tendsTo_mul ha hbinv

theorem Sequence.lim_div {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) (hnon: lim b ≠ 0) :
  (a / b).Convergent ∧ lim (a / b) = lim a / lim b := by
    choose L ha using ha
    choose M hb using hb
    have hMnon : M ≠ 0 := by
      rw[lim_eq] at hb
      rwa[← hb.2]
    have hten := tendsTo_div ha hb hMnon
    rw[lim_eq] at hten ha hb
    refine ⟨hten.1,?_⟩ 
    rw[ha.2,hb.2,hten.2]

instance Sequence.inst_max : Max Sequence where
  max a b := {
    m := min a.m b.m
    seq n := max (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.max_eval {a b: Sequence} (n:ℤ) : (a ⊔ b) n = (a n) ⊔ (b n) := rfl

theorem Sequence.max_coe (a b: ℕ → ℝ) : (a:Sequence) ⊔ (b:Sequence) = (fun n ↦ max (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(g) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
lemma Sequence.max_comm {a b : Sequence} : max a b = max b a := by
  ext n
  . change min a.m b.m = min b.m a.m
    exact Int.min_comm a.m b.m
  simp; rw[_root_.max_comm]

lemma Sequence.lt_of_lim_lt {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) (hle : L < M):
    ∃ N, N ≥ a.m ∧ N ≥ b.m ∧ ∀ n ≥ N , a n < b n := by
      observe hdiff : M - L > 0
      set diff := M - L
      specialize ha (diff/3) (by linarith)
      specialize hb (diff/3) (by linarith)
      choose Na hNa haC using ha
      choose Nb hNb hbC using hb
      use max Na Nb
      split_ands
      . simp[hNa]
      . simp[hNb]
      intro n hn
      simp at hn
      have hna: n ≥ a.m:= by linarith
      have hnb: n ≥ b.m:= by linarith
      specialize haC n (by aesop)
      specialize hbC n (by aesop)
      simp[dist,hn,hna,hnb,abs_le] at haC hbC
      linarith

theorem Sequence.tendsTo_max_eq {a b:Sequence} {L:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo L) :
    (max a b).TendsTo L := by
      intro ε hε 
      specialize ha ε hε
      specialize hb ε hε 
      choose Na hNa haC using ha
      choose Nb hNb hbC using hb
      use max Na Nb
      split_ands
      . change max Na Nb ≥ min a.m b.m
        grind
      intro n hn
      simp at hn
      have hna: n ≥ a.m:= by linarith
      have hnb: n ≥ b.m:= by linarith
      specialize haC n (by aesop)
      specialize hbC n (by aesop)
      simp[dist,hn,hna,hnb,abs_le] at haC hbC ⊢ 
      split_ands
      . rw[← sub_le_iff_le_add]
        simp;grind
      grind
      grind
theorem Sequence.tendsTo_max {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (max a b).TendsTo (max L M) := by
      wlog hle : M ≤ L
      . specialize this hb ha (by linarith)
        rwa[max_comm,_root_.max_comm]
      simp[hle]
      obtain (heq|hlt) := hle.eq_or_lt
      . rw[heq] at hb
        exact tendsTo_max_eq ha hb
      intro ε hε 
      choose Nth hNtha hNthb hNlt using lt_of_lim_lt hb ha hlt
      specialize ha ε hε 
      choose N hNa hCa using ha
      use max Nth N
      split_ands
      . change max Nth N ≥ min a.m b.m
        grind
      intro n hn
      simp at hn
      simp[hn]
      specialize hNlt n hn.2.1
      rw[max_eq_left_of_lt hNlt]
      specialize hCa n (by grind)
      have hamn : a.m ≤ n := by linarith
      simpa[hn,hamn] using hCa

theorem Sequence.lim_max {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (max a b).Convergent ∧ lim (max a b) = max (lim a) (lim b) := by
    choose L ha using ha
    choose M hb using hb
    have hten := tendsTo_max ha hb
    rw[lim_eq] at hten ha hb
    refine ⟨hten.1,?_⟩ 
    rw[ha.2,hb.2,hten.2]

instance Sequence.inst_min : Min Sequence where
  min a b := {
    m := min a.m b.m
    seq n := min (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.min_eval {a b: Sequence} (n:ℤ) : (a ⊓ b) n = (a n) ⊓ (b n) := rfl

theorem Sequence.min_coe (a b: ℕ → ℝ) : (a:Sequence) ⊓ (b:Sequence) = (fun n ↦ min (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(h) (limit laws) -/
lemma Sequence.min_comm {a b : Sequence} : min a b = min b a := by
  ext n
  . change min a.m b.m = min b.m a.m
    exact Int.min_comm a.m b.m
  simp; rw[_root_.min_comm]
theorem Sequence.tendsTo_min_eq {a b:Sequence} {L:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo L) :
    (min a b).TendsTo L := by
      intro ε hε 
      specialize ha ε hε
      specialize hb ε hε 
      choose Na hNa haC using ha
      choose Nb hNb hbC using hb
      use max Na Nb
      split_ands
      . change max Na Nb ≥ min a.m b.m
        grind
      intro n hn
      simp at hn
      have hna: n ≥ a.m:= by linarith
      have hnb: n ≥ b.m:= by linarith
      specialize haC n (by aesop)
      specialize hbC n (by aesop)
      simp[dist,hn,hna,hnb,abs_le] at haC hbC ⊢ 
      split_ands
      . rw[← sub_le_iff_le_add]
        simp;grind
      grind
theorem Sequence.tendsTo_min {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (min a b).TendsTo (min L M) := by
      wlog hle : M ≤ L
      . specialize this hb ha (by linarith)
        rwa[min_comm,_root_.min_comm]
      simp[hle]
      obtain (heq|hlt) := hle.eq_or_lt
      . rw[← heq] at ha
        exact tendsTo_min_eq ha hb
      intro ε hε 
      choose Nth hNtha hNthb hNlt using lt_of_lim_lt hb ha hlt
      specialize hb ε hε 
      choose N hNb hCb using hb
      use max Nth N
      split_ands
      . change max Nth N ≥ min a.m b.m
        grind
      intro n hn
      simp at hn
      simp[hn]
      specialize hNlt n hn.2.1
      rw[min_eq_right_of_lt hNlt]
      specialize hCb n (by grind)
      have hbmn : b.m ≤ n := by linarith
      simpa[hn,hbmn] using hCb

theorem Sequence.lim_min {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (min a b).Convergent ∧ lim (min a b) = min (lim a) (lim b) := by
    choose L ha using ha
    choose M hb using hb
    have hten := tendsTo_min ha hb
    rw[lim_eq] at hten ha hb
    refine ⟨hten.1,?_⟩ 
    rw[ha.2,hb.2,hten.2]

/-- Exercise 6.1.1 -/
theorem Sequence.mono_if {a: ℕ → ℝ} (ha: ∀ n, a (n+1) > a n) {n m:ℕ} (hnm: m > n) : a m > a n := by
  induction' m,hnm using Nat.le_induction with k hnk hind 
  . simp; exact ha n
  have := ha k
  linarith

/-- Exercise 6.1.3 -/
theorem Sequence.tendsTo_of_from {a: Sequence} {c:ℝ} (m:ℤ) :
    a.TendsTo c ↔ (a.from m).TendsTo c := by
      simp_rw[tendsTo_def,Real.eventuallyClose_def]
      congr! 2 with ε hε
      constructor <;> intro h
      . choose N hN hclose using h
        use max N m 
        refine ⟨by grind, ?_⟩ 
        intro n hn
        simp at hn
        obtain ⟨hnam ,hnN, hnm⟩ := hn 
        simp[hnam,hnN,hnm]
        specialize hclose n;simpa[hnam,hnN] using hclose
      choose N hN hclose using h
      use N
      simp at hN
      obtain ⟨hNam, hNm⟩ := hN 
      refine ⟨hNam,?_⟩ 
      intro n hn; simp at hn
      obtain ⟨hnam,hnN⟩ := hn 
      have hmn : m ≤ n := by linarith
      specialize hclose n
      simp[hnam,hmn,hnN] at hclose
      simpa[hnam,hnN]

/-- Exercise 6.1.4 -/
theorem Sequence.tendsTo_of_shift {a: Sequence} {c:ℝ} (k:ℕ) :
    a.TendsTo c ↔ (Sequence.mk' a.m (fun n : {n // n ≥ a.m} ↦ a (n+k))).TendsTo c := by
      simp_rw[tendsTo_def,Real.eventuallyClose_def]
      congr! 2 with ε hε
      constructor <;> intro h
      . choose N hN hclose using h
        use N
        refine ⟨hN,?_⟩ 
        intro n hn
        simp at hn
        choose hnam hnN using hn
        have hnkam : (n+k)≥ a.m := by linarith
        have hnkN : (n+k)≥ N := by linarith
        specialize hclose (n+k)
        simp[hnkam,hnkN] at hclose
        simpa[hnam,hnN]
      choose N hN hclose using h
      use N + k
      refine ⟨by linarith, ?_⟩ 
      intro n hn
      simp at hn
      choose hnam hnNk using hn
      simp[hnam,hnNk]
      specialize hclose (n - k)
      have hnNk: N ≤ n-k := by linarith
      have hnamk : a.m ≤ n - k := by linarith
      simpa[hnamk,hnNk] using hclose

/-- Exercise 6.1.7 -/
theorem Sequence.isBounded_of_rat (a: Chapter5.Sequence) :
    a.IsBounded ↔ (a:Sequence).IsBounded := by
      constructor
      . intro ha
        choose M hM hMb using ha
        use M; simp
        refine ⟨hM,?_⟩ 
        peel hMb with n hMb
        simp;norm_cast
      intro ha
      choose M hM hMb using ha
      choose Mq hMq using exists_rat_gt M
      use Mq;split_ands
      . rify; linarith
      peel hMb with n hMb
      simp at hMb
      rify;linarith

/-- Exercise 6.1.9 -/
noncomputable abbrev Sequence.harmonic_k (k:ℝ) : Sequence  := fun (n:ℕ) ↦ k / (n+1)

lemma Sequence.harmonic_k_tendsTo_zero (k:ℝ): (harmonic_k k).TendsTo 0 := by
  wlog hk : k > 0
  . simp at hk
    obtain (rfl | hk ) := eq_or_lt_of_le hk
    . simp[harmonic_k]
      have : (fun (n:ℕ) ↦ (0:ℝ)) = const 0 0 := by simp
      rw[this]
      apply tendsTo_const
    specialize this (-k) (Left.neg_pos_iff.mpr hk)
    rw[← neg_zero]
    have hneg : harmonic_k (k) = - harmonic_k (-k) := by
      simp[harmonic_k];ext n
      simp;rfl
      by_cases hn : 0 ≤ n
      . lift n to ℕ using hn
        simp;ring
      simp[hn]
    rw[hneg] 
    apply tendsTo_neg this
  have h1 : (harmonic_k 1).TendsTo 0 := by
    simp[harmonic_k]
    obtain ⟨hhcon, hlim⟩  := lim_harmonic
    have := lim_def hhcon
    rwa[hlim] at this
  have hsmul : harmonic_k k = k • (harmonic_k 1) := by
    simp[harmonic_k];symm
    apply smul_coe
  rw[hsmul, show (0:ℝ) = (k * 0) by simp]
  apply tendsTo_smul _ h1

lemma Sequence.harmonic_k_convergent {k:ℝ}  : (harmonic_k k).Convergent := by
  use 0
  exact harmonic_k_tendsTo_zero k

lemma Sequence.harmonic_k_lim{k:ℝ}  : lim (harmonic_k k) = 0 := by
  have := harmonic_k_tendsTo_zero k 
  rw[lim_eq] at this
  exact this.2
theorem Sequence.lim_div_fail :
    ∃ a b, a.Convergent
    ∧ b.Convergent
    ∧ lim b = 0
    ∧ ¬ ((a / b).Convergent ∧ lim (a / b) = lim a / lim b) := by
      set a := harmonic_k 1
      set b := harmonic_k 2
      use a,b
      refine ⟨ harmonic_k_convergent  , harmonic_k_convergent , harmonic_k_lim , ?_⟩ 
      set c := a / b
      have hcm : c.m = 0 :=by
        simp[c]
        change min a.m b.m = 0
        simp[a,b]
      have : c.TendsTo (1/2) := by
        intro ε hε 
        use c.m;simp
        intro n hn
        simp[hcm] at hn
        lift n to ℕ using hn
        have : c n = 1/2 := by
          simp[c,a,b];field_simp
        simp[hcm,this]
        linarith
      have hcc : c.Convergent := by
        use 1/2
      have hcl : lim c = 1/2 := by
        rw[lim_eq] at this
        exact this.2
      simp[hcc,hcl]
      simp[a,b,harmonic_k_lim]

theorem Chapter5.Sequence.IsCauchy_iff (a:Chapter5.Sequence) :
    a.IsCauchy ↔ ∀ ε > (0:ℝ), ∃ N ≥ a.n₀, ∀ n ≥ N, ∀ m ≥ N, |a n - a m| ≤ ε := by
      constructor
      . intro ha ε hε 
        choose εq hεq0 hεq  using exists_pos_rat_lt hε 
        specialize ha εq  hεq0 
        peel ha with N hNa n ha
        intro hnN m hmN
        specialize ha (by grind)
        specialize ha m (by grind)
        simp[Rat.Close] at ha

        simp[hnN,hmN, show a.n₀ ≤ n by linarith, show a.n₀ ≤ m by linarith] at ha
        calc
          _ ≤ (εq :ℝ) := by norm_cast
          _ ≤ _ := by linarith
      intro ha ε hε
      specialize ha ε (by simpa)
      peel ha with N hNa n hs
      intro hn
      simp at hn
      specialize hs hn.2
      intro m hm
      simp at hm
      specialize hs m hm.2
      norm_cast at hs
      simpa[Rat.Close,hn,hm]

end Chapter6

-- additional definitions for exercise 6.1.10
abbrev Real.SeqCloseSeq (ε: ℝ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Real.SeqEventuallyClose (ε: ℝ) (a b: Chapter5.Sequence): Prop :=
  ∃ N, ε.SeqCloseSeq (a.from N) (b.from N)

-- extended definition of rational sequences equivalence but with positive real ε
abbrev Chapter5.Sequence.RatEquiv (a b: ℕ → ℚ) : Prop :=
  ∀ (ε:ℝ), ε > 0 → ε.SeqEventuallyClose (a:Chapter5.Sequence) (b:Chapter5.Sequence)

namespace Chapter6
/-- Exercise 6.1.10 -/
theorem Chapter5.Sequence.equiv_rat (a b: ℕ → ℚ) :
  Chapter5.Sequence.Equiv a b ↔ Chapter5.Sequence.RatEquiv a b := by
    constructor
    . intro ha ε hε 
      choose εq hεq0 hεq  using exists_pos_rat_lt hε 
      specialize ha εq  hεq0 
      peel ha with N n hna hnb ha
      simp at hna hnb
      simp[Rat.Close,hna] at ha
      simp[hna,dist]
      calc
        _ ≤ (εq:ℝ) := by norm_cast
        _ ≤ _ := by linarith
    intro ha ε hε
    specialize ha ε (by simpa)
    peel ha with N n hna hnb ha
    simp at hna hnb
    simp[Rat.Close,hna]
    simp[hna,dist] at ha
    norm_cast at ha

end Chapter6
