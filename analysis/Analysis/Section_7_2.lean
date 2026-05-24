import Mathlib.Tactic
import Mathlib.Algebra.Field.Power
import Analysis.Section_7_1
/-!
# Analysis I, Section 7.2: Infinite series

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Formal series and their limits.
- Absolute convergence; basic series laws.

-/

namespace Chapter7

open BigOperators

/--
  Definition 7.2.1 (Formal infinite series). This is similar to Chapter 6 sequence, but is
  manipulated differently. As with Chapter 5, we will start series from 0 by default.
-/
@[ext]
structure Series where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Functions from ℕ to ℝ can be thought of as series. -/
instance Series.instCoe : Coe (ℕ → ℝ) Series where
  coe := fun a ↦ {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by grind
  }

@[simp]
theorem Series.eval_coe (a: ℕ → ℝ) (n: ℕ) : (a: Series).seq n = a n := by simp

abbrev Series.mk' {m:ℤ} (a: { n // n ≥ m } → ℝ) : Series where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by grind

theorem Series.eval_mk' {m:ℤ} (a : { n // n ≥ m } → ℝ) {n : ℤ} (h:n ≥ m) :
    (Series.mk' a).seq n = a ⟨ n, h ⟩ := by simp [h]

/-- Definition 7.2.2 (Convergence of series) -/
abbrev Series.partial (s : Series) (N:ℤ) : ℝ := ∑ n ∈ Finset.Icc s.m N, s.seq n

theorem Series.partial_succ (s : Series) {N:ℤ} (h: N ≥ s.m-1) : s.partial (N+1) = s.partial N + s.seq (N+1) := by
  unfold Series.partial
  rw [add_comm (s.partial N) _]
  convert Finset.sum_insert (show N+1 ∉ Finset.Icc s.m N by simp)
  symm; apply Finset.insert_Icc_right_eq_Icc_add_one; linarith

theorem Series.partial_of_lt {s : Series} {N:ℤ} (h: N < s.m) : s.partial N = 0 := by
  unfold Series.partial
  rw [Finset.sum_eq_zero]
  intro n hn; simp at hn; grind

abbrev Series.convergesTo (s : Series) (L:ℝ) : Prop := Filter.atTop.Tendsto (s.partial) (nhds L)

abbrev Series.converges (s : Series) : Prop := ∃ L, s.convergesTo L

abbrev Series.diverges (s : Series) : Prop := ¬s.converges

open Classical in
noncomputable abbrev Series.sum (s : Series) : ℝ := if h : s.converges then h.choose else 0

theorem Series.converges_of_convergesTo {s : Series} {L:ℝ} (h: s.convergesTo L) :
    s.converges := by use L

/-- Remark 7.2.3 -/
theorem Series.sum_of_converges {s : Series} {L:ℝ} (h: s.convergesTo L) : s.sum = L := by
  simp [sum, converges_of_convergesTo h]
  exact tendsto_nhds_unique ((converges_of_convergesTo h).choose_spec) h

theorem Series.convergesTo_uniq {s : Series} {L L':ℝ} (h: s.convergesTo L) (h': s.convergesTo L') :
    L = L' := tendsto_nhds_unique h h'

theorem Series.convergesTo_sum {s : Series} (h: s.converges) : s.convergesTo s.sum := by
  simp [sum, h]; exact h.choose_spec

/-- Example 7.2.4 -/
noncomputable abbrev Series.example_7_2_4 := mk' (m := 1) (fun n ↦ (2:ℝ)^(-n:ℤ))

theorem Series.example_7_2_4a {N:ℤ} (hN: N ≥ 1) : example_7_2_4.partial N = 1 - (2:ℝ)^(-N) := by
  unfold Series.partial
  induction' N,hN using Int.le_induction with k hk hind
  . norm_num
  simp at hind ⊢ 
  rw[Finset.sum_of_nonempty (by omega)]
  simp[show 0 ≤ k by omega]
  rw[hind,sub_add]
  congr
  field_simp
  ring_nf
  calc
    _ = (2:ℝ) ^ k := by 
      rw[add_comm,zpow_add_one₀ (by simp),mul_two];simp
    _ = _ := by
      rw[← zpow_add₀ (by simp), ← zpow_add₀  (by simp)]
      simp

theorem Series.example_7_2_4b : example_7_2_4.convergesTo 1 := by
  unfold convergesTo
  have h : example_7_2_4.partial = fun n ↦ if h : n ≥ 1 then  1 - (2:ℝ)^(-n) else 0 := by
    ext N
    split_ifs with hn
    . rw[example_7_2_4a hn]
    apply partial_of_lt
    simp; omega
  rw[h,Metric.tendsto_atTop]
  intro ε hε
  set m := - Real.logb 2 ε
  set mc := max ⌈m⌉ 1
  use (mc+1)
  intro n hnmc
  have hn1 : 1 ≤ n := by omega
  have hmc : 2 ^ (-mc) ≤ ε := by
    have hnegm : 2^(-m) = ε := by 
      simp[m]
      refine Real.rpow_logb (by simp) (by simp) hε
    have hnegmc : -mc ≤ -m := by
      simp[mc];left
      exact Int.le_ceil m
    have : (2:ℝ) ^ (-mc) = (2:ℝ) ^ (- (mc:ℝ)) := by norm_cast
    rw[this,← hnegm]
    simp[hnegmc]
      
  have hni : 2 ^ (-n) < ε := by
    rw[ge_iff_le,← neg_le_neg_iff] at hnmc
    calc
      _ ≤ (2:ℝ) ^ (-(mc + 1)) := by 
        apply zpow_le_zpow_right₀
        simp
        assumption
      _ < (2:ℝ) ^ (-mc) := by
        apply zpow_lt_zpow_right₀
        simp
        omega
      _ ≤ _ := by assumption
  simp only [ge_iff_le, hn1, ↓reduceDIte,  dist_self_sub_left , norm_zpow,
    Real.norm_ofNat, hni]


theorem Series.example_7_2_4c : example_7_2_4.sum = 1 := by
  apply sum_of_converges example_7_2_4b

noncomputable abbrev Series.example_7_2_4' := mk' (m := 1) (fun n ↦ (2:ℝ)^(n:ℤ))

theorem Series.example_7_2_4'a {N:ℤ} (hN: N ≥ 1) : example_7_2_4'.partial N = (2:ℝ)^(N+1) - 2 := by
  induction' N,hN using Int.le_induction with k hk hind
  . simp[Series.partial]
    norm_num
  rw[Series.partial_succ]
  . simp[example_7_2_4', show 0 ≤ k by omega,hind]
    nth_rw 3 [zpow_add_one₀]
    rw[sub_add_eq_add_sub,mul_two]
    simp
  simp
  omega
theorem Series.example_7_2_4'b : example_7_2_4'.diverges := by
  simp[convergesTo]
  intro x hx
  set g:= example_7_2_4'.partial
  set f:ℕ → ℝ := fun n ↦ (2:ℝ)^(n+1) - 2
  have hfg : ∀ (n:ℕ), n ≥ 1 → f n = g (n:ℤ) := by
    intro n hn
    zify at hn
    simp[f,g]
    rw[example_7_2_4'a hn]
    norm_cast
  have htop : Filter.Tendsto f Filter.atTop (nhds x) := by
    have : ∀ᶠ (n : ℕ) in Filter.atTop, f n = g n := by
      refine Filter.eventually_atTop.mpr ⟨1, fun n hn => hfg n hn⟩
    rw[Filter.tendsto_congr' this]
    apply hx.comp
    exact tendsto_natCast_atTop_atTop
  have hbdda := htop.bddAbove_range
  choose M hM using hbdda
  have hM' (n : ℕ) : f n ≤ M :=
    hM (Set.mem_range_self n)
  have h_pow_ge (n:ℕ): f n ≥ (n:ℝ) := by
    induction' n with k hind
    . simp[f]
    simp[f] at ⊢ hind
    ring_nf at hind ⊢ 
    calc
      _ ≤ (1:ℝ) + (-2 + 2 ^ k * 2) := by linarith
      _ ≤ _ := by
        simp
        rw[← add_assoc,← add_assoc]
        nlinarith
  specialize hM' (Nat.ceil M + 1)
  specialize h_pow_ge (Nat.ceil M + 1)
  have hcon : (Nat.ceil  M + 1) > M := by
    calc
      _ ≥ M + 1 := by gcongr; exact Nat.le_ceil M
      _ > _ := by simp
  simp at h_pow_ge
  linarith

/-- Proposition 7.2.5 / Exercise 7.2.2 -/
lemma Series.interval_eq_partial_sub (s:Series) (p q : ℤ) (hpq: p ≤ q) : ∑ n ∈ Finset.Icc p q, s.seq n = s.partial q - s.partial (p-1):= by
  induction' q,hpq using Int.le_induction with k hk hind
  . simp
    by_cases hq : p < s.m
    . rw[s.vanish,partial_of_lt,partial_of_lt]
      simp
      linarith
      assumption'
    symm
    rw[sub_eq_iff_eq_add]
    set p' := p-1
    rw[show p = p'+1 by linarith,add_comm _ (s.partial p')]
    apply partial_succ
    linarith
  rw[Finset.sum_of_nonempty (by linarith)] 
  rw[hind]
  rw[add_comm,add_sub_assoc']
  congr
  symm
  by_cases hkm : k ≥ s.m - 1
  . rw[add_comm _ (s.partial k)]
    apply partial_succ _ hkm
  simp at hkm
  rw[s.vanish _ hkm]
  rw[partial_of_lt hkm]
  have hkm' : k < s.m := by omega
  rw[partial_of_lt hkm']
  simp
  
lemma Series.tail_decay_iff_CauchySeq (s:Series) : 
  (∀ ε > 0, ∃ N ≥ s.m, ∀ p ≥ N, ∀ q ≥ N, |∑ n ∈ Finset.Icc p q, s.seq n| ≤ ε) ↔ CauchySeq s.partial := by
    rw[cauchySeq_iff_tendsto_dist_atTop_0,Metric.tendsto_atTop]
    constructor
    . 
      rintro hseg ε hε 
      specialize hseg (ε/2) (half_pos hε )
      choose N hN hpqs using hseg
      use (N,N)
      intro n hn
      wlog hpq : n.1 < n.2
      .
        by_cases heq : n.1 = n.2
        . simp[heq,hε]
        specialize this s ε hε N hN hpqs (n.2,n.1)
        simp at this
        rw[dist_comm] at this
        rw[Real.dist_0_eq_abs,abs_of_nonneg (by simp) ]
        specialize this hn.2 hn.1 
        apply this
        simp at hpq 
        apply lt_of_le_of_ne hpq
        symm;assumption
      set p := n.1 + 1
      have hpn1 : n.1 = p - 1 := by linarith
      rw[hpn1]
      set q := n.2
      simp[Real.dist_eq]
      have hpN : p ≥ N := by 
        have := hn.1
        linarith
      have hqN : q ≥ N :=hn.2
      specialize hpqs p hpN q hqN
      rw[interval_eq_partial_sub _ _ _ (by linarith)] at hpqs
      calc
         _ ≤ ε/2 := by rwa[abs_sub_comm]
         _ < _ := by apply div_two_lt_of_pos hε
    intro hcau ε hε 
    specialize hcau ε hε 
    choose N hN  using hcau
    use max s.m (max (N.1+1) (N.2+1))
    simp
    intro p hp hpn q hq hqn
    have hpqn : (p-1, q) ≥ N := by
      constructor
      . simp
        apply le_sub_left_of_add_le
        omega
      . simp
        omega
    specialize hN (p-1,q) hpqn
    simp at hN
    by_cases hpq : p ≤ q
    . rw[interval_eq_partial_sub _ _ _ hpq]
      rw[Real.dist_eq,abs_sub_comm] at hN
      apply le_of_lt hN
    rw[Finset.sum_of_empty]
    simp;apply le_of_lt hε 
    simp at hpq
    assumption



theorem Series.converges_iff_tail_decay (s:Series) :
    s.converges ↔ ∀ ε > 0, ∃ N ≥ s.m, ∀ p ≥ N, ∀ q ≥ N, |∑ n ∈ Finset.Icc p q, s.seq n| ≤ ε := by
      rw[tail_decay_iff_CauchySeq ]
      exact (cauchy_iff_exists_le_nhds).symm
       

/-- Corollary 7.2.6 (Zero test) / Exercise 7.2.3 -/
theorem Series.decay_of_converges {s:Series} (h: s.converges) :
    Filter.atTop.Tendsto s.seq (nhds 0) := by
  sorry

theorem Series.diverges_of_nodecay {s:Series} (h: ¬ Filter.atTop.Tendsto s.seq (nhds 0)) :
    s.diverges := by
  sorry

/-- Example 7.2.7 -/
theorem Series.example_7_2_7 : ((fun n:ℕ ↦ (1:ℝ)):Series).diverges := by
  apply diverges_of_nodecay
  sorry

theorem Series.example_7_2_7' : ((fun n:ℕ ↦ (-1:ℝ)^n):Series).diverges := by
  apply diverges_of_nodecay
  sorry

/-- Definition 7.2.8 (Absolute convergence) -/
abbrev Series.abs (s:Series) : Series := mk' (m:=s.m) (fun n ↦ |s.seq n|)

abbrev Series.absConverges (s:Series) : Prop := s.abs.converges

abbrev Series.condConverges (s:Series) : Prop := s.converges ∧ ¬ s.absConverges

/-- Proposition 7.2.9 (Absolute convergence test) / Example 7.2.4 -/
theorem Series.converges_of_absConverges {s:Series} (h : s.absConverges) : s.converges := by
  sorry

theorem Series.abs_le {s:Series} (h : s.absConverges) : |s.sum| ≤ s.abs.sum := by
  sorry

/-- Proposition 7.2.12 (Alternating series test) -/
theorem Series.converges_of_alternating {m:ℤ} {a: { n // n ≥ m} → ℝ} (ha: ∀ n, a n ≥ 0)
  (ha': Antitone a) :
    ((mk' (fun n ↦ (-1)^(n:ℤ) * a n)).converges ↔ Filter.atTop.Tendsto a (nhds 0)) := by
  -- This proof is written to follow the structure of the original text.
  constructor
  . intro h; apply decay_of_converges at h
    rw [tendsto_iff_dist_tendsto_zero] at h ⊢
    rw [←Filter.tendsto_comp_val_Ici_atTop (a := m)] at h
    convert h using 2 with _ n
    simp [n.property]
  intro h
  unfold converges convergesTo
  set b := mk' fun n ↦ (-1) ^ (n:ℤ) * a n
  set S := b.partial
  have claim0 {N:ℤ} (hN: N ≥ m) : S (N+1) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ := by
    convert b.partial_succ ?_; simp [b, show N+1 ≥ m by grind]; linarith
  have claim1 {N:ℤ} (hN: N ≥ m) : S (N+2) = S N + (-1)^(N+1) * (a ⟨ N+1, by grind ⟩ - a ⟨ N+2, by grind ⟩) := calc
      S (N+2) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1)^(N+2) * a ⟨ N+2, by grind ⟩ := by
        simp_rw [←claim0 hN, show N+2=N+1+1 by abel]; apply claim0; linarith
      _ = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1) * (-1)^(N+1) * a ⟨ N+2, by grind ⟩ := by
        congr; rw [←zpow_one_add₀] <;> grind
      _ = _ := by ring
  have claim2 {N:ℤ} (hN: N ≥ m) (h': Odd N) : S (N+2) ≥ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have claim3 {N:ℤ} (hN: N ≥ m) (h': Even N) : S (N+2) ≤ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have why1 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k) ≤ S N := by sorry
  have why2 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≥ S N - a ⟨ N+1, by grind ⟩ := by sorry
  have why3 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≤ S (N+2*k) := by sorry
  have claim4 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S N -
 a ⟨ N+1, by grind ⟩ ≤ S (N + 2*k + 1) ∧ S (N + 2*k + 1) ≤ S (N + 2*k) ∧ S (N + 2*k) ≤ S N := ⟨ ge_iff_le.mp (why2 hN h' k), why3 hN h' k, why1 hN h' k ⟩
  have why4 {N n:ℤ} (hN: N ≥ m) (h': Even N) (hn: n ≥ N) : S N - a ⟨ N+1, by grind ⟩ ≤ S n ∧ S n ≤ S N := by
    sorry
  have why5 {ε:ℝ} (hε: ε > 0) : ∃ N, ∀ n ≥ N, ∀ m ≥ N, |S n - S m| ≤ ε := by sorry
  have : CauchySeq S := by
    rw [Metric.cauchySeq_iff']
    intro ε hε; choose N hN using why5 (half_pos hε); use N
    intro n hn; rw [Real.dist_eq]; linarith [hN n hn N (by simp)]
  exact cauchySeq_tendsto_of_complete this

/-- Example 7.2.13 -/
noncomputable abbrev Series.example_7_2_13 : Series := (mk' (m:=1) (fun n ↦ (-1:ℝ)^(n:ℤ) / (n:ℤ)))

theorem Series.example_7_2_13a : example_7_2_13.converges := by
  sorry

theorem Series.example_7_2_13b : ¬ example_7_2_13.absConverges := by
  sorry

theorem Series.example_7_2_13c :  example_7_2_13.condConverges := by
  sorry

instance Series.inst_add : Add Series where
  add a b := {
    m := max a.m b.m
    seq n := if n ≥ max a.m b.m then a.seq n + b.seq n else 0
    vanish n hn := by rw [lt_iff_not_ge] at hn; simp [hn]
  }

theorem Series.add_coe (a b: ℕ → ℝ) : (a:Series) + (b:Series) = (fun n ↦ a n + b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HAdd.hAdd, Add.add]

/-- Proposition 7.2.14 (a) (Series laws) / Exercise 7.2.5.  The `convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.add {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s + t).convergesTo (L + M) := by
  sorry

theorem Series.add {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s + t).converges ∧ (s+t).sum = s.sum + t.sum := by sorry

instance Series.inst.smul : SMul ℝ Series where
  smul c s := {
    m := s.m
    seq n := if n ≥ s.m then c * s.seq n else 0
    vanish := by grind
  }

theorem Series.smul_coe (a: ℕ → ℝ) (c: ℝ) : (c • a:Series) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Proposition 7.2.14 (b) (Series laws) / Exercise 7.2.5.  The `convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.smul {s:Series} {L c: ℝ} (hs: s.convergesTo L) :
    (c • s).convergesTo (c * L) := by
  sorry

theorem Series.smul {c:ℝ} {s:Series} (hs: s.converges) :
    (c • s).converges ∧ (c • s).sum = c * s.sum := by sorry

/-- The corresponding API for subtraction was not in the textbook, but is useful in later sections, so is included here. -/
instance Series.inst_sub : Sub Series where
  sub a b := {
    m := max a.m b.m
    seq n := if n ≥ max a.m b.m then a.seq n - b.seq n else 0
    vanish := by grind
  }

theorem Series.sub_coe (a b: ℕ → ℝ) : (a:Series) - (b:Series) = (fun n ↦ a n - b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSub.hSub, Sub.sub]

theorem Series.convergesTo.sub {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s - t).convergesTo (L - M) := by
  sorry

theorem Series.sub {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s - t).converges ∧ (s-t).sum = s.sum - t.sum := by sorry

abbrev Series.from (s:Series) (m₁:ℤ) : Series := mk' (m := max s.m m₁) (fun n ↦ s.seq (n:ℤ))

/-- Proposition 7.2.14 (c) (Series laws) / Exercise 7.2.5 -/
theorem Series.converges_from (s:Series) (k:ℕ) : s.converges ↔ (s.from (s.m+k)).converges := by
  sorry

theorem Series.sum_from {s:Series} (k:ℕ) (h: s.converges) :
    s.sum = ∑ n ∈ Finset.Ico s.m (s.m+k), s.seq n + (s.from (s.m+k)).sum := by
  sorry

/-- Proposition 7.2.14 (d) (Series laws) / Exercise 7.2.5 -/
theorem Series.shift {s:Series} {x:ℝ} (h: s.convergesTo x) (L:ℤ) :
    (mk' (m := s.m + L) (fun n ↦ s.seq (n - L))).convergesTo x := by
  sorry

/-- Lemma 7.2.15 (telescoping series) / Exercise 7.2.6 -/
theorem Series.telescope {a:ℕ → ℝ} (ha: Filter.atTop.Tendsto a (nhds 0)) :
    ((fun n:ℕ ↦ a (n+1) - a n):Series).convergesTo (a 0) := by
  sorry

/- Exercise 7.2.1  -/

def Series.exercise_7_2_1_convergent :
  Decidable ( (mk' (m := 1) (fun n ↦ (-1:ℝ)^(n:ℤ))).converges ) := by
  -- The first line of this proof should be `apply isTrue` or `apply isFalse`.
  sorry


end Chapter7
