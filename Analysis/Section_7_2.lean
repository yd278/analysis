import Mathlib.Tactic
import Mathlib.Algebra.Field.Power
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
noncomputable abbrev Series.partial (s : Series) (N:ℤ) : ℝ := ∑ n ∈ Finset.Icc s.m N, s.seq n

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
      simp[mc]
      left
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
    intro p hpm hpn1 hpn2 q hqm hqn1 hqn2

    have hpqn : (p-1, q) ≥ N := by
      constructor
      . simp
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
      rw[converges_iff_tail_decay] at h
      rw[Metric.tendsto_atTop]
      intro ε hε
      specialize h (ε /2 ) (half_pos hε)
      choose N hN hdecay using h
      use N
      intro n hn
      simp
      specialize hdecay n hn n hn
      simp at hdecay
      linarith
      

theorem Series.diverges_of_nodecay {s:Series} (h: ¬ Filter.atTop.Tendsto s.seq (nhds 0)) :
    s.diverges := by
      contrapose h
      apply decay_of_converges h

/-- Example 7.2.7 -/
theorem Series.example_7_2_7 : ((fun _:ℕ ↦ (1:ℝ)):Series).diverges := by
  apply diverges_of_nodecay
  intro h
  rw[Metric.tendsto_atTop] at h
  specialize h 1 (by simp)
  choose N hN using h
  specialize hN (max N 0) (by simp)
  simp at hN

theorem Series.example_7_2_7' : ((fun n:ℕ ↦ (-1:ℝ)^n):Series).diverges := by
  apply diverges_of_nodecay
  intro h
  rw[Metric.tendsto_atTop] at h
  specialize h 1 (by simp)
  choose N hN using h
  specialize hN (max N 0) (by simp)
  simp at hN

/-- Definition 7.2.8 (Absolute convergence) -/
abbrev Series.abs (s:Series) : Series := mk' (m:=s.m) (fun n ↦ |s.seq n|)

abbrev Series.absConverges (s:Series) : Prop := s.abs.converges

abbrev Series.condConverges (s:Series) : Prop := s.converges ∧ ¬ s.absConverges

/-- Proposition 7.2.9 (Absolute convergence test) / Exercise 7.2.4 -/
theorem Series.converges_of_absConverges {s:Series} (h : s.absConverges) : s.converges := by
  simp[absConverges ] at h
  rw[ converges_iff_tail_decay] at h ⊢ 
  peel h with ε hε N hN 
  rw [show s.abs.m = s.m by rfl] at hN
  simp[hN.left]
  replace hN := hN.right
  peel hN with p hp q hq hsum
  have hrep (p q:ℤ): ∑ n ∈ Finset.Icc p q,s.abs.seq n = ∑ n ∈ Finset.Icc p q,|s.seq n| := by
    apply Finset.sum_congr
    simp
    intro x hx
    simp
    intro hxsm
    rw[s.vanish _ hxsm]
    simp
  apply le_trans _ hsum
  rw[hrep]
  refine le_trans ?_ (le_abs_self _)
  apply Finset.abs_finite_series_le

theorem Series.abs_le {s:Series} (h : s.absConverges) : |s.sum| ≤ s.abs.sum := by
  have hconv := converges_of_absConverges h
  choose L hL using hconv
  choose R hR using h
  rw[sum_of_converges hL, sum_of_converges hR]
  have hLabs := Filter.Tendsto.abs hL

  apply le_of_tendsto_of_tendsto' hLabs hR
  intro x
  by_cases hx : x ≥ s.m
  . 
    induction' x,hx using Int.le_induction with k hk hind
    . simp[Series.partial]
    rw[partial_succ _ (by linarith)]
    rw[partial_succ _ (by linarith)]
    rw[show s.abs.seq (k+1) = |s.seq (k+1)| by simp[show s.m ≤ k+1 by linarith] ]
    calc
      _ ≤ |s.partial k| + |s.seq (k+1)| := by apply abs_add_le
      _ ≤ _ := by gcongr
  rw[partial_of_lt, partial_of_lt]
  simp
  linarith
  linarith


/-- Proposition 7.2.12 (Alternating series test) -/
theorem Series.converges_of_alternating {m:ℤ} {a: { n // n ≥ m} → ℝ} (ha: ∀ n, a n ≥ 0)
  (ha': Antitone a) :
    ((mk' (fun n ↦ (-1)^(n:ℤ) * a n)).converges ↔ Filter.atTop.Tendsto a (nhds 0)) := by
  -- This proof is written to follow the structure of the original text.
  constructor
  . intro h; apply decay_of_converges at h
    rw [tendsto_iff_dist_tendsto_zero] at h ⊢
    rw [←Filter.tendsto_comp_val_Ici_atTop (a := m)] at h
    refine h.congr (fun n => ?_)
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
  have why1 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k) ≤ S N := by
    induction' k with k hind
    . simp
    rify;rw[mul_add,← add_assoc];norm_num
    have hev : Even (N + 2 * k) := by grind
    have hn' : (N + 2 * k) ≥ m := by grind
    have := claim3 hn' hev
    linarith
    
  have why2 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≥ S N - a ⟨ N+1, by grind ⟩ := by
    have claim0' : S (N + 1) = S N - a ⟨N + 1, by grind⟩ := by
      rw[claim0 hN];
      have : (-1:ℝ) ^ (N+1) = -1 := by
        apply Odd.neg_one_zpow
        apply h'.add_one
      rw[this];simp;ring
    rw[← claim0']
    induction' k with k hind
    . simp
    zify
    rw[show N + (2:ℤ) * (k + 1) + 1 = N + (2:ℤ) * k + 1 + 2 by ring]
    have hodd : Odd (N + 2 * k + 1) := by
      apply Even.add_one
      apply Even.add h'
      simp
    have hnm : (N + 2 * k + 1) ≥ m := by grind
    apply le_trans hind
    apply claim2 hnm hodd

  have why3 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≤ S (N+2*k) := by
    have hodd : Odd (N+2*k+1) := by grind
    have hnm : N+2*k ≥ m := by grind
    have claim0' := claim0 hnm
    rw[Odd.neg_one_zpow  hodd] at claim0'
    rw[claim0']
    simp;apply ha
  have claim4 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S N -
 a ⟨ N+1, by grind ⟩ ≤ S (N + 2*k + 1) ∧ S (N + 2*k + 1) ≤ S (N + 2*k) ∧ S (N + 2*k) ≤ S N := ⟨ ge_iff_le.mp (why2 hN h' k), why3 hN h' k, why1 hN h' k ⟩
  have why4 {N n:ℤ} (hN: N ≥ m) (h': Even N) (hn: n ≥ N) : S N - a ⟨ N+1, by grind ⟩ ≤ S n ∧ S n ≤ S N := by
    set d := (n - N).toNat
    have hd : n = N + d := by
      simp[d, show max (n - N) 0 = (n - N) by simp[hn]]
    rw[show S n = S (N + d) by rw[hd]]
    specialize claim4 hN h'
    obtain ⟨k,(hk|hk)⟩ :=  d.even_or_odd'
    <;> specialize claim4 k
    <;> simp only[hk, Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,← add_assoc]
    . refine ⟨le_trans claim4.1 claim4.2.1,claim4.2.2⟩ 
    refine ⟨claim4.1, le_trans claim4.2.1 claim4.2.2⟩ 
  have why5 {ε:ℝ} (hε: ε > 0) : ∃ N, ∀ n ≥ N, ∀ m ≥ N, |S n - S m| ≤ ε := by
    have hne : Nonempty { n // n ≥ m } := by use m
    rw[Metric.tendsto_atTop] at h
    specialize h ε hε 
    obtain ⟨⟨T,hT⟩ ,hTa⟩ := h 
    set N := if Even T then T else (T + 1)
    have hNT : N ≥ T := by 
      simp[N];split_ifs<;>simp
    have hN: N ≥ m := by linarith
    have h' : Even N := by
        simp[N]; split_ifs with hT
        . assumption
        simp at hT
        exact hT.add_one
    use N
    intro n1 hn1 n2 hn2
    have hr1 := why4 hN h' hn1
    have hr2 := why4 hN h' hn2
    specialize hTa ⟨N+1,by grind⟩ (by simp;linarith)
    rw[Real.dist_eq,sub_zero,abs_of_nonneg (by apply ha)] at hTa
    rw[abs_sub_le_iff]
    split_ands <;> linarith
  have : CauchySeq S := by
    rw [Metric.cauchySeq_iff']
    intro ε hε; choose N hN using why5 (half_pos hε); use N
    intro n hn; rw [Real.dist_eq]; linarith [hN n hn N (by simp)]
  exact cauchySeq_tendsto_of_complete this

/-- Example 7.2.13 -/
noncomputable abbrev Series.example_7_2_13 : Series := (mk' (m:=1) (fun n ↦ (-1:ℝ)^(n:ℤ) / (n:ℤ)))

theorem Series.example_7_2_13a : example_7_2_13.converges := by
  set a := fun n : {n// n≥ (1:ℤ)} ↦ (1:ℝ) / (n:ℤ)
  have heq : example_7_2_13 = (mk' fun n ↦ (-1)^(n:ℤ) * a n) := by
    ext x
    . simp
    simp;split_ifs
    . simp[a];field_simp
    simp
  rw[heq,converges_of_alternating]
  . 
    have hne : Nonempty {n // n ≥ (1:ℤ)} := by use 1
    rw[Metric.tendsto_atTop]
    intro ε hε
    set N := ⌈ε⁻¹⌉
    have hN : N ≥ 1 := by simp[N,hε]
    use ⟨N+1,by grind⟩ 
    rintro ⟨n,hn⟩ hnN
    simp at hnN
    simp[a]
    apply inv_lt_of_inv_lt₀ hε 
    have :ε⁻¹ ≤ N := by apply Int.le_ceil
    apply lt_of_le_of_lt this
    rw[abs_of_pos] <;> simp<;> linarith
  . rintro ⟨x,hx⟩ 
    simp[a]
    linarith
  rintro ⟨x1,hx1⟩ ⟨x2,hx2⟩ hle
  simp at hle
  simp[a]
  rw[inv_le_inv₀]
  <;> simp <;> linarith

/- theorem Series.example_7_2_13b : ¬ example_7_2_13.absConverges := by -/
/-   -- See Corollary 7.3.7 -/
/-   sorry -/

/- theorem Series.example_7_2_13c :  example_7_2_13.condConverges := by -/
/-   refine ⟨example_7_2_13a,example_7_2_13b⟩  -/

instance Series.inst_add : Add Series where
  add a b := {
    m := min a.m b.m
    seq n := a.seq n + b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }

theorem Series.add_coe (a b: ℕ → ℝ) : (a:Series) + (b:Series) = (fun n ↦ a n + b n) := by
  ext n; rfl
  change (a:Series).seq n + (b:Series).seq n = _
  by_cases h:n ≥ 0 <;> simp [h]


/-- Proposition 7.2.14 (a) (Series laws) / Exercise 7.2.5.  The {name}`convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.add {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s + t).convergesTo (L + M) := by
      unfold convergesTo at hs ht ⊢ 
      suffices hadd : (s+t).partial = s.partial + t.partial from by
        rw[hadd]
        apply hs.add ht
      wlog hst : s.m ≤ t.m
      . simp at hst
        specialize this ht hs (le_of_lt hst)
        have hcomm : s + t = t + s:= by
          ext m
          . apply min_comm
          apply add_comm _ _
        rwa[hcomm,add_comm]
      ext n
      simp
      by_cases hn : n < s.m
      . rw[partial_of_lt (by change n < min s.m t.m; omega)]
        rw[partial_of_lt (by omega)]
        rw[partial_of_lt (by omega)]
        simp
      simp at hn
      induction' n,hn using Int.le_induction with k hk hind
      . simp[Series.partial]
        simp[show (s+t).m = s.m by change min s.m t.m = s.m; omega]
        obtain (heq|hlt) := hst.eq_or_lt
        . simp[heq];rfl
        simp[hlt]
        change s.seq s.m + t.seq s.m = s.seq s.m
        simp;apply t.vanish _ hlt
      rw[partial_succ _ (by change k ≥ min s.m t.m -1;omega)]
      rw[partial_succ _ (by omega)]
      rw[hind]
      rw[show (s+t).seq (k+1) = s.seq (k+1) + t.seq (k+1) by rfl]
      suffices ht_succ : t.partial (k+1) = t.partial (k) + t.seq (k+1) from by linarith
      by_cases hkt : k ≥ t.m - 1
      . apply partial_succ _ hkt
      simp at hkt
      simp[Series.partial]
      rw[t.vanish _ hkt]
      have : k < t.m := by omega
      simp[hkt,this]


theorem Series.add {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s + t).converges ∧ (s+t).sum = s.sum + t.sum := by
      choose L hL using hs
      choose M hM using ht
      rw[ sum_of_converges hL, sum_of_converges hM]
      have hsum := hL.add hM
      split_ands
      . use L+M
      exact sum_of_converges hsum

instance Series.inst.smul : SMul ℝ Series where
  smul c s := {
    m := s.m
    seq n := if n ≥ s.m then c * s.seq n else 0
    vanish := by grind
  }

theorem Series.smul_coe (a: ℕ → ℝ) (c: ℝ) : (c • a:Series) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Proposition 7.2.14 (b) (Series laws) / Exercise 7.2.5.  The {name}`convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.smul {s:Series} {L c: ℝ} (hs: s.convergesTo L) :
    (c • s).convergesTo (c * L) := by
      unfold convergesTo at hs  ⊢ 
      suffices hsc : (c • s).partial = fun n ↦  s.partial n * c from by
        rw[hsc]
        rw[mul_comm,← smul_eq_mul]
        apply hs.smul_const c
      ext n
      obtain (hlt|hge) := lt_or_ge n s.m
      . rw[partial_of_lt (by omega)]
        rw[partial_of_lt hlt]
        simp
      replace hge : n ≥ s.m - 1 := by omega
      induction' n,hge using Int.le_induction with k hk hind 
      . rw[partial_of_lt (by change s.m - 1 < s.m; simp), partial_of_lt (by simp)];simp
      rw[partial_succ _ (by omega), partial_succ _ (by omega)]
      simp[hind,add_mul]
      rw[mul_comm]
      change( if (k+1) ≥ s.m then c * s.seq (k+1) else 0)  = c * s.seq (k+1)
      simp;intro
      linarith

theorem Series.smul {c:ℝ} {s:Series} (hs: s.converges) :
    (c • s).converges ∧ (c • s).sum = c * s.sum := by
      choose L hL using hs
      rw[sum_of_converges hL]
      split_ands
      . use c*L
        unfold convergesTo 
        exact convergesTo.smul hL
      apply sum_of_converges 
      exact convergesTo.smul hL

/-- The corresponding API for subtraction was not in the textbook, but is useful in later sections, so is included here. -/
instance Series.inst_sub : Sub Series where
  sub a b := {
    m := min a.m b.m
    seq n := a.seq n - b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }

theorem Series.sub_coe (a b: ℕ → ℝ) : (a:Series) - (b:Series) = (fun n ↦ a n - b n) := by
  ext n; rfl
  change (a:Series).seq n - (b:Series).seq n = _
  by_cases h:n ≥ 0 <;> simp [h]
lemma Series.partial_succ' {s:Series}  {N:ℤ} : s.partial (N+1) = s.partial N + s.seq (N+1) := by
  by_cases hN: N ≥ s.m - 1
  . apply partial_succ _ hN
  unfold Series.partial
  simp at hN
  rw[Finset.sum_of_empty hN]
  rw[Finset.sum_of_empty (by omega)]
  simp;symm
  apply s.vanish _ hN

theorem Series.convergesTo.sub {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s - t).convergesTo (L - M) := by
    unfold convergesTo at hs ht ⊢ 
    set m := min s.m t.m
    have hsubm : (s - t).m = m := by rfl
    suffices hsub : (s-t).partial = s.partial - t.partial from by
      rw[hsub]
      apply hs.sub ht
    ext n
    simp
    by_cases hnm : n < m
    . repeat rw[partial_of_lt (by omega)]
      simp
    simp at hnm
    induction' n,hnm using Int.le_induction with k hk hind
    . simp[Series.partial,hsubm]
      rw[show (s-t).seq m = s.seq m - t.seq m by rfl]
      obtain (hle|heq|hge) := lt_trichotomy s.m t.m
      . have hm : m = s.m := by omega
        rw[hm];simp;rw[Finset.sum_of_empty hle]
        apply t.vanish _ hle
      . have hm : m = t.m := by omega
        simp[hm,heq]
      . have hm : m=t.m :=by omega
        rw[hm];simp;rw[Finset.sum_of_empty hge]
        apply s.vanish _ hge
    repeat rw[partial_succ']
    simp[hind]
    have hst: (s-t).seq (k+1) = s.seq (k+1) - t.seq (k+1) := by rfl
    linarith

theorem Series.sub {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s - t).converges ∧ (s-t).sum = s.sum - t.sum := by
      choose L hL using hs
      choose M hM using ht
      split_ands
      . use L-M
        apply convergesTo.sub hL hM
      apply sum_of_converges 
      rw[sum_of_converges hL, sum_of_converges hM]
      apply convergesTo.sub hL hM

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
    ((fun n:ℕ ↦ a n - a (n+1)):Series).convergesTo (a 0) := by
  sorry

/- Exercise 7.2.1  -/

def Series.exercise_7_2_1_convergent :
  Decidable ( (mk' (m := 1) (fun n ↦ (-1:ℝ)^(n:ℤ))).converges ) := by
  -- The first line of this proof should be `apply isTrue` or `apply isFalse`.
  sorry


end Chapter7
