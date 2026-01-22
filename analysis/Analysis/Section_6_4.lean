import Mathlib.Tactic
import Analysis.Section_6_3

/-!
# Analysis I, Section 6.4: Limsup, liminf, and limit points

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Lim sup and lim inf of sequences
- Limit points of sequences
- Comparison and squeeze tests
- Completeness of the reals

-/

abbrev Real.Adherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) := ∃ n ≥ a.m, ε.Close (a n) x

abbrev Real.ContinuallyAdherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) :=
  ∀ N ≥ a.m, ε.Adherent (a.from N) x

namespace Chapter6

open EReal

abbrev Sequence.LimitPoint (a:Sequence) (x:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.ContinuallyAdherent a x

theorem Sequence.limit_point_def (a:Sequence) (x:ℝ) :
  a.LimitPoint x ↔ ∀ ε > 0, ∀ N ≥ a.m, ∃ n ≥ N, |a n - x| ≤ ε := by
    unfold LimitPoint Real.ContinuallyAdherent Real.Adherent
    congr! 6 with ε hε N hN n
    constructor
    . rintro ⟨hn ,hclose⟩ 
      simp at hn
      simp[hn.2]
      simpa[dist,hn] using hclose
    rintro ⟨hn,hclose⟩ 
    have : n ≥ a.m := by linarith
    simpa[dist,hn,this]

noncomputable abbrev Example_6_4_3 : Sequence := (fun (n:ℕ) ↦ 1 - (10:ℝ)^(-(n:ℤ)-1))

/-- Example 6.4.3 -/
example : (0.1:ℝ).Adherent Example_6_4_3 0.8 := by
  use 0
  simp[dist]
  norm_num
  rw[abs_of_pos (by positivity)]

/-- Example 6.4.3 -/
example : ¬ (0.1:ℝ).ContinuallyAdherent Example_6_4_3 0.8 := by

  unfold Real.ContinuallyAdherent 
  push_neg
  use 1;simp
  intro n hn
  simp[dist,hn, show 0 ≤ n by linarith]
  calc
    _ < (1:ℝ) - 10 ^ (-(1:ℤ) - 1) - 0.8 := by norm_num
    _ ≤ (1:ℝ) - 10 ^ (-n - 1) - 0.8 := by gcongr;simp
    _ ≤ _ := by apply le_abs_self

/-- Example 6.4.3 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_3 1 := by
  intro N hN
  simp at hN
  use N
  simp[hN]
  calc
    _ ≤ (10:ℝ) ^ (- (0:ℤ) - 1) := by gcongr;simp
    _ = _ := by norm_num

/-- Example 6.4.3 -/
example : Example_6_4_3.LimitPoint 1 := by
  intro ε hε 
  intro N hN 
  simp at hN
  have hpow : ∃ (N:ℤ), (10:ℝ) ^(-N - 1) < ε := by
    simp only [neg_sub_left,zpow_neg,← inv_zpow]
    have hltone : (10:ℝ)⁻¹ < 1 := by norm_num
    choose N' hN' using exists_pow_lt_of_lt_one hε hltone
    use N'-1; simp_all
  choose m hm using hpow
  use max N m
  split_ands
  . simp[hN]
  simp[dist,hN]
  rw[abs_of_pos (by positivity)]
  replace hm := le_of_lt hm
  apply le_trans ?_ hm
  simp

noncomputable abbrev Example_6_4_4 : Sequence :=
  (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

/-- Example 6.4.4 -/
example : (0.1:ℝ).Adherent Example_6_4_4 1 := by
  use 0
  simp
  norm_num


/-- Example 6.4.4 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_4 1 := by
  intro N hN
  simp at hN
  lift N to ℕ using hN
  by_cases hpar : Even N
  . use N
    simp[dist]
    have :(-1:ℝ)^N = 1 := by exact Even.neg_one_pow hpar
    simp[this]
    calc 
      _ ≤ |(10:ℝ) ^ ( - (0:ℤ) - 1)| := by gcongr; simp; simp
      _ ≤ _ := by norm_num; rw[abs_of_pos (by positivity)]
  simp at hpar
  use (N + 1)
  replace hpar : Even (N + 1) := by exact Odd.add_one hpar
  simp[dist, show 0 ≤ (N:ℤ) + 1 by linarith]
  have : (-1:ℝ) ^ (N+1) = 1 := by exact Even.neg_one_pow hpar
  simp[this]
  rw[abs_of_pos (by positivity)]
  calc
    _ ≤ (10:ℝ) ^ (-(1:ℤ) + -(0) - 1) := by gcongr; simp;simp
    _ ≤ _ := by norm_num
lemma Real.exists_decimal_seq {ε :ℝ} (hε: ε >0) : ∃ (N:ℕ), ∀ n ≥ N, (10:ℝ) ^(-(n:ℤ) - 1) < ε := by
    suffices h :∃(N:ℤ), ∀ n ≥ N, (10:ℝ) ^ (-n - 1) < ε from by
      choose N hN using h
      use N.toNat
      intro n hn
      apply hN n 
      zify at hn
      apply ge_trans hn
      simp
    simp only [neg_sub_left,zpow_neg,← inv_zpow]
    have hltone : (10:ℝ)⁻¹ < 1 := by norm_num
    choose N' hN' using exists_pow_lt_of_lt_one hε hltone
    use N'-1
    intro n hn
    calc
      _ ≤ (10:ℝ)⁻¹ ^ (1 + N' - 1:ℤ) := by
        apply zpow_le_zpow_right_of_le_one₀
        positivity
        linarith
        linarith
      _ < _ := by field_simp;ring_nf;assumption
/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint 1 := by
  intro ε hε 
  have hpow : ∃ (N:ℕ), ∀ n ≥ N, (10:ℝ) ^(-(n:ℤ) - 1) < ε := by
    suffices h :∃(N:ℤ), ∀ n ≥ N, (10:ℝ) ^ (-n - 1) < ε from by
      choose N hN using h
      use N.toNat
      intro n hn
      apply hN n 
      zify at hn
      apply ge_trans hn
      simp
    simp only [neg_sub_left,zpow_neg,← inv_zpow]
    have hltone : (10:ℝ)⁻¹ < 1 := by norm_num
    choose N' hN' using exists_pow_lt_of_lt_one hε hltone
    use N'-1
    intro n hn
    calc
      _ ≤ (10:ℝ)⁻¹ ^ (1 + N' - 1:ℤ) := by
        apply zpow_le_zpow_right_of_le_one₀
        positivity
        linarith
        linarith
      _ < _ := by field_simp;ring_nf;assumption
  intro N hN
  simp at hN
  lift N to ℕ using hN
  choose m hm using hpow

  set n := max N m
  by_cases hpar : Even n
  . use n
    simp[dist, show N ≤ n by simp[n]]
    have : (-1:ℝ)^n  = 1 := by exact Even.neg_one_pow hpar
    simp[this]
    rw[abs_of_pos (by positivity)]
    apply le_of_lt
    apply hm n
    simp[n]
  simp at hpar
  use (n+1)
  have hnN : N ≤ n+1 := by
    apply le_trans (show N ≤ n by simp[n])
    linarith
  zify at hnN
  replace hpar : Even (n+1) := by exact Odd.add_one hpar
  have :(-1:ℝ) ^ (n+1) = 1 := by exact Even.neg_one_pow hpar
  simp[hnN, show (n:ℤ)+1 ≥ 0 by linarith,dist,this]
  rw[abs_of_pos (by positivity)]
  apply le_of_lt
  have := hm (n+1) (by apply le_trans (show m ≤ n by simp[n]); linarith)
  simpa using this

/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint (-1) := by
  intro ε hε 
  have hpow : ∃ (N:ℕ), ∀ n ≥ N, (10:ℝ) ^(-(n:ℤ) - 1) < ε := by
    suffices h :∃(N:ℤ), ∀ n ≥ N, (10:ℝ) ^ (-n - 1) < ε from by
      choose N hN using h
      use N.toNat
      intro n hn
      apply hN n 
      zify at hn
      apply ge_trans hn
      simp
    simp only [neg_sub_left,zpow_neg,← inv_zpow]
    have hltone : (10:ℝ)⁻¹ < 1 := by norm_num
    choose N' hN' using exists_pow_lt_of_lt_one hε hltone
    use N'-1
    intro n hn
    calc
      _ ≤ (10:ℝ)⁻¹ ^ (1 + N' - 1:ℤ) := by
        apply zpow_le_zpow_right_of_le_one₀
        positivity
        linarith
        linarith
      _ < _ := by field_simp;ring_nf;assumption
  intro N hN
  simp at hN
  lift N to ℕ using hN
  choose m hm using hpow

  set n := max N m
  by_cases hpar : Odd n
  . use n
    simp[dist, show N ≤ n by simp[n]]
    have : (-1:ℝ)^n  = -1 := by exact Odd.neg_one_pow hpar
    simp[this]
    rw[abs_of_pos (by positivity)]
    apply le_of_lt
    apply hm n
    simp[n]
  simp at hpar
  use (n+1)
  have hnN : N ≤ n+1 := by
    apply le_trans (show N ≤ n by simp[n])
    linarith
  zify at hnN
  replace hpar : Odd (n+1) := by exact Even.add_one hpar
  have :(-1:ℝ) ^ (n+1) = -1 := by exact Odd.neg_one_pow hpar
  simp[hnN, show (n:ℤ)+1 ≥ 0 by linarith,dist,this]
  rw[abs_of_pos (by positivity)]
  apply le_of_lt
  have := hm (n+1) (by apply le_trans (show m ≤ n by simp[n]); linarith)
  simpa using this
/-- Example 6.4.4 -/
example : ¬ Example_6_4_4.LimitPoint 0 := by
  unfold Sequence.LimitPoint Real.ContinuallyAdherent
  push_neg
  use 0.1;
  refine ⟨by linarith, ?_⟩ 
  use 0; simp
  intro x hx 
  lift x to ℕ using hx
  simp
  by_cases hpar : Even x
  . observe :(-1:ℝ)^ x = 1
    simp[this]
    rw[abs_of_pos (by positivity)]
    calc
      _ < (1:ℝ) := by linarith
      _ < _ := by simp; positivity
  . simp at hpar
    observe: (-1:ℝ)^x = (-1)
    simp[this]
    rw[← neg_add,abs_neg,abs_of_pos (by positivity)]
    calc
      _ < (1:ℝ) := by linarith
      _ < _ := by simp; positivity

/-- Proposition 6.4.5 / Exercise 6.4.1 -/
theorem Sequence.limit_point_of_limit {a:Sequence} {x:ℝ} (h: a.TendsTo x) : a.LimitPoint x := by
  peel h with ε hε h
  intro N hN
  choose n hn hclose using h
  simp at hN hn
  use max n N
  simp[hN]
  specialize hclose (max n N) (by simp[hn])
  simpa[hn] using hclose
/--
  A technical issue uncovered by the formalization: the upper and lower sequences of a real
  sequence take values in the extended reals rather than the reals, so the definitions need to be
  adjusted accordingly.
-/
noncomputable abbrev Sequence.upperseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).sup

noncomputable abbrev Sequence.limsup (a:Sequence) : EReal :=
  sInf { x | ∃ N ≥ a.m, x = a.upperseq N }

noncomputable abbrev Sequence.lowerseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).inf

noncomputable abbrev Sequence.liminf (a:Sequence) : EReal :=
  sSup { x | ∃ N ≥ a.m, x = a.lowerseq N }

noncomputable abbrev Example_6_4_7 : Sequence := (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))
lemma Sequence.sup_of_max (a:Sequence) {n:ℤ} (hn : n ≥ a.m) (han : ∀ m ≥ a.m, a m ≤ a n) : a.sup = a n:= by
  observe hle: a n ≤ a.sup 
  have hge: a.sup ≤ a n:= by
    apply sup_le_upper
    peel han with m hm han
    rw[EReal.le_iff];left
    use a m, a n
  apply eq_of_le_of_ge hge hle

lemma Sequence.inf_of_min (a:Sequence) {n:ℤ} (hn : n ≥ a.m) (han : ∀ m ≥ a.m, a m ≥ a n) : a.inf = a n:= by
  observe hle: a n ≥ a.inf 
  have hge: a.inf ≥ a n:= by
    apply inf_ge_lower
    peel han with m hm han
    simp[han]
  apply eq_of_le_of_ge hle hge
lemma Example_6_4_7.odd_lt_even {n m:ℕ} (hn:Odd n) (hm: Even m): Example_6_4_7 n < Example_6_4_7 m := by
  simp
  observe : (-1:ℝ) ^ n = -1
  simp[this]
  observe : (-1:ℝ) ^ m = 1
  simp[this]
  calc
    _ < (0:ℝ)  := by simp;positivity
    _ < _ := by positivity

lemma Example_6_4_7.even_antitone (n:ℕ) (hn:Even n): Example_6_4_7 (n + 2) ≤  Example_6_4_7 n := by
  simp [show 0 ≤ (n:ℤ)+2  by linarith,
    show ((n:ℤ)+2).toNat = n + 2 by rfl
  ]
  have : Even (n+2) := by
    apply Even.add hn
    simp
  observe :(-1:ℝ) ^(n+2) = 1
  simp[this]
  observe :(-1:ℝ) ^(n) = 1
  simp[this]
lemma Example_6_4_7.odd_monotone (n:ℕ) (hn:Odd n): Example_6_4_7 (n + 2) ≥   Example_6_4_7 n := by
  simp [show 0 ≤ (n:ℤ)+2  by linarith,
    show ((n:ℤ)+2).toNat = n + 2 by rfl
  ]
  have : Odd (n+2) := by
    apply Odd.add_even hn
    simp
  observe :(-1:ℝ) ^(n+2) = -1
  simp[this]
  observe :(-1:ℝ) ^(n) = -1
  simp[this]

lemma Example_6_4_7.even_antitone_trans (n:ℕ) (hn:Even n) : ∀ m ≥ n, Even m → Example_6_4_7 n ≥ Example_6_4_7 m := by
  suffices h: ∀ (i:ℕ), Example_6_4_7 n ≥ Example_6_4_7 (n + (i + i)) from by
    intro m hmn hme
    choose d hd using exists_add_of_le hmn
    have hde: Even d := by
      observe hd : d = m - n
      simp[hd]
      exact Even.tsub hme hn
    simp[Even] at hde
    choose i hi using hde
    rw[hd,hi]
    exact h i
  -- now we can do induction
  intro i
  induction' i with k hind
  . simp
  apply ge_trans hind
  norm_cast
  rw[ show (n + (k + 1 + (k + 1))) = (n + (k + k)) + 2 by ring]
  set v := n + (k + k)
  have hve : Even v := by
    simp[v]
    apply Even.add hn
    exact Even.add_self k
  apply even_antitone v hve

lemma Example_6_4_7.odd_monotone_trans (n:ℕ) (hn:Odd n) : ∀ m ≥ n, Odd m → Example_6_4_7 n ≤ Example_6_4_7 m := by
  suffices h: ∀ (i:ℕ), Example_6_4_7 n ≤ Example_6_4_7 (n + (i + i)) from by
    intro m hmn hme
    choose d hd using exists_add_of_le hmn
    have hde: Even d := by
      observe hd : d = m - n
      simp[hd]
      exact Nat.Odd.sub_odd hme hn
    simp[Even] at hde
    choose i hi using hde
    rw[hd,hi]
    exact h i
  -- now we can do induction
  intro i
  induction' i with k hind
  . simp
  apply le_trans hind
  norm_cast
  rw[ show (n + (k + 1 + (k + 1))) = (n + (k + k)) + 2 by ring]
  set v := n + (k + k)
  have hve : Odd v := by
    simp[v]
    apply Odd.add_even hn
    exact Even.add_self k
  apply odd_monotone v hve
lemma Example_6_4_7.even_upper {n:ℕ} (hn: Even n) : ∀ m ≥ n, Example_6_4_7 m ≤ Example_6_4_7 n:= by
  intro m hm
  by_cases hme: Even m
  . exact even_antitone_trans n hn m hm hme
  simp at hme
  apply le_of_lt
  exact odd_lt_even hme hn


lemma Example_6_4_7.odd_lower {n:ℕ} (hn: Odd n) : ∀ m ≥ n, Example_6_4_7 m ≥ Example_6_4_7 n:= by
  intro m hm
  by_cases hme: Even m
  . apply le_of_lt
    exact odd_lt_even hn hme
  simp at hme
  exact odd_monotone_trans n hn m hm hme 

lemma Example_6_4_7.upperseq_fun (n:ℕ) :
    Example_6_4_7.upperseq n = if Even n then 1 + (10:ℝ)^(-(n:ℤ)-1) else 1 + (10:ℝ)^(-(n:ℤ)-2) := by
      unfold Sequence.upperseq
      set f := Example_6_4_7.from n
      split_ifs with hpn
      . 
        -- show that it's exactly f(n)
        have hfn : f n = 1 + (10:ℝ) ^ (-(n:ℤ) - 1) := by
          simp[f]
          observe :(-1:ℝ) ^ n = 1
          simp[this]
        rw[← hfn]
        apply Sequence.sup_of_max
        . simp[f]
        -- show that f(n) is the largest
        intro m hm
        simp[f] at hm
        rw[show f n = Example_6_4_7 n by simp[f]]
        rw[ show f m = Example_6_4_7 m by simp [f,hm]]
        lift m to ℕ using by linarith
        simp at hm
        exact Example_6_4_7.even_upper hpn m hm
      have hfn : f (n + 1) = 1 + (10:ℝ) ^ (-(n:ℤ)-2) := by
        simp[f]
        have : 0 ≤ (n:ℤ)+1:=by linarith
        simp[this]
        observe : Even (n+1)
        observe : (-1:ℝ)^(n+1) = 1
        simp[this]
        ring
      rw[← hfn]
      apply Sequence.sup_of_max
      . simp[f]
      simp at hpn
      intro m hm
      simp[f] at hm
      rw[show f (n+1) = Example_6_4_7 (n+1) by simp[f]]
      rw[ show f m = Example_6_4_7 m by simp [f,hm]]
      lift m to ℕ using by linarith
      observe hn : Even (n+1)
      rw[show (n:ℤ) + 1 = (n+1:ℕ) by rfl]
      by_cases hsp : m = n
      . rw[hsp]; apply le_of_lt; exact Example_6_4_7.odd_lt_even hpn hn
      simp at hm
      push_neg at hsp
      have hm : m ≥ n+1 := by omega
      set n := n+1
      exact Example_6_4_7.even_upper hn m hm


example : Example_6_4_7.limsup = 1 := by
  simp[Sequence.limsup]
  apply IsGLB.sInf_eq
  constructor
  . intro x hx 
    simp at hx
    choose N hN hNx using hx
    lift N to ℕ using hN
    rw[Example_6_4_7.upperseq_fun N] at hNx
    split_ifs at hNx with hpar
    all_goals
      simp[hNx]
      rw[EReal.le_iff]
      left
      use 1
    . use 1+(10 ^ (-(N:ℤ)-1))
      simp;positivity
    use 1+(10^(-(N:ℤ)-2))
    simp;positivity
  intro l hl
  rw[mem_lowerBounds] at hl
  contrapose hl
  rw[EReal.le_iff] at hl
  push_neg at hl
  obtain ⟨hr,hnt,hnb⟩ := hl 
  push_neg
  obtain ⟨l,rfl⟩ |rfl |rfl := l.def
  . 
    specialize hr l 1
    simp at hr
    observe hε : l - 1 > 0
    set ε := l - 1
    choose N hN using Real.exists_decimal_seq hε 
    set n := if Even N then N else (N+1) with hn
    split_ifs at hn with hnp
    . rw[← hn] at hnp
      specialize hN n (by simp[hn])
      use (1:ℝ)+ ((10:ℝ)^ (- (n:ℤ) -1):ℝ)
      simp only [ Set.mem_setOf_eq]
      split_ands
      . use n
        rw[Example_6_4_7.upperseq_fun n]
        split_ands
        simp
        simp only [hnp, ↓reduceIte,EReal.coe_add]
      norm_cast
      linarith
    have hnp: Even n := by
      simp[n,hnp]
      exact Nat.even_add_one.mpr hnp
    specialize hN n (by simp[hn])
    use (1:ℝ)+ ((10:ℝ)^ (- (n:ℤ) -1):ℝ)
    simp only [ Set.mem_setOf_eq]
    split_ands
    . use n
      rw[Example_6_4_7.upperseq_fun n]
      split_ands
      simp
      simp only [hnp, ↓reduceIte,EReal.coe_add]
    norm_cast
    linarith
  . use Example_6_4_7.upperseq 0
    simp
    split_ands
    . use 0
    change Example_6_4_7.upperseq (0:ℕ) < ⊤ 
    rw[Example_6_4_7.upperseq_fun 0]
    simp
    exact compareOfLessAndEq_eq_lt.mp rfl
  simp at hnb



lemma Example_6_4_7.lowerseq_fun (n:ℕ) :
    Example_6_4_7.lowerseq n
    = if Even n then -(1 + (10:ℝ)^(-(n:ℤ)-2)) else -(1 + (10:ℝ)^(-(n:ℤ)-1)) := by
      unfold Sequence.lowerseq 
      set f := Example_6_4_7.from n
      split_ifs with hpn
      . 
        -- show that it's exactly f(n)
        have hfn : f (n + 1) = - (1 + (10:ℝ) ^ (-(n:ℤ)-2)) := by
          simp[f]
          have : 0 ≤ (n:ℤ)+1:=by linarith
          simp[this]
          observe : Odd (n+1)
          observe : (-1:ℝ)^(n+1) = -1
          simp[this]
          ring
        rw[← hfn]
        apply Sequence.inf_of_min
        . simp[f]
        -- show that f(n+1) is the smallest
        intro m hm
        simp[f] at hm
        rw[show f (n+1) = Example_6_4_7 (n+1) by simp[f]]
        rw[ show f m = Example_6_4_7 m by simp [f,hm]]
        lift m to ℕ using by linarith
        observe hn : Odd (n+1)
        rw[show (n:ℤ) + 1 = (n+1:ℕ) by rfl]
        by_cases hsp : m = n
        . rw[hsp]; apply le_of_lt; exact Example_6_4_7.odd_lt_even hn hpn
        simp at hm
        push_neg at hsp
        have hm : m ≥ n+1 := by omega
        set n := n+1
        exact odd_lower hn m hm
      simp at hpn
      have hfn : f n = -(1 + (10:ℝ) ^ (-(n:ℤ) - 1)) := by
        simp[f]
        observe :(-1:ℝ) ^ n = -1
        simp[this]
      rw[← hfn]
      apply Sequence.inf_of_min
      . simp[f]
      intro m hm
      simp[f] at hm
      rw[show f n = Example_6_4_7 n by simp[f]]
      rw[ show f m = Example_6_4_7 m by simp [f,hm]]
      lift m to ℕ using by linarith
      simp at hm
      exact odd_lower hpn m hm

example : Example_6_4_7.liminf = -1 := by
  simp[Sequence.liminf]
  apply IsLUB.sSup_eq
  constructor
  . intro x hx 
    simp at hx
    choose N hN hNx using hx
    lift N to ℕ using hN
    rw[Example_6_4_7.lowerseq_fun N] at hNx
    split_ifs at hNx with hpar
    all_goals
      simp[hNx]
      simp_rw[show (-1:EReal) = ((-1:ℝ):EReal) by rfl]
      rw[← EReal.coe_neg,← EReal.coe_add]
      apply EReal.coe_le_coe
      simp
      positivity
  
  intro l hl
  rw[mem_upperBounds] at hl
  obtain ⟨l,rfl⟩ |rfl | rfl := l.def 
  . 
    rw[← EReal.coe_one, ← EReal.coe_neg]
    apply EReal.coe_le_coe
    contrapose! hl
    observe hε : -1 - l > 0
    set ε := -1 - l 
    choose N hN using Real.exists_decimal_seq hε 
    set n := if Odd N then N else N + 1 with hn
    have hnN : n ≥ N := by
      simp[n]
      split_ifs <;> simp
    have hnp : Odd n := by
      simp[n]
      split_ifs with hNp
      exact hNp
      exact Nat.odd_add_one.mpr hNp
    specialize hN n hnN
    use (- ((1:ℝ) + ((10:ℝ)^ (-(n:ℤ) - 1):ℝ )))
    simp
    split_ands
    . use n
      rw[Example_6_4_7.lowerseq_fun n]
      simp[show ¬ Even n by simpa]
      simp_rw[← EReal.coe_one,
        ← EReal.coe_add,
        ← EReal.coe_neg,
        ← EReal.coe_add
      ]
      simp
    rw[← EReal.coe_one,← EReal.coe_add]
    apply EReal.coe_lt_coe
    linarith
  . simp
  specialize hl (-(1 + ((10:ℝ)^(-(0:ℤ)-2)):ℝ))
  simp at hl
  specialize hl (0:ℕ)
  rw[Example_6_4_7.lowerseq_fun 0] at hl
  specialize hl (by simp) (by
    simp
    simp_rw[← EReal.coe_one, 
    ← EReal.coe_neg,
    ← EReal.coe_add,
    ← EReal.coe_neg,
    ]
    simp
  )
  contrapose! hl
  exact Ne.symm (not_eq_of_beq_eq_false rfl)


example : Example_6_4_7.sup = (1.1:ℝ) := by
  have : ((1.1:ℝ):EReal) = Example_6_4_7 0 := by
    simp;
    rw[← EReal.coe_one,
      ← EReal.coe_add
    ]
    norm_num
  rw[this]
  apply Sequence.sup_of_max
  . simp
  observe : Even 0
  have := Example_6_4_7.even_upper (this)
  intro m hm
  simp at hm
  lift m to ℕ using hm
  specialize this m (by simp)
  assumption'

example : Example_6_4_7.inf = (-1.01:ℝ) := by
  have : ((-1.01:ℝ):EReal) = Example_6_4_7 1 := by
    simp;
    simp_rw[← EReal.coe_one,
      ← EReal.coe_neg,
      ← EReal.coe_add
    ]
    norm_num
  rw[this]
  apply Sequence.inf_of_min
  . simp
  observe ho1 : Odd 1
  have := Example_6_4_7.odd_lower (ho1)
  intro m hm
  simp at hm
  lift m to ℕ using hm
  by_cases hspm : m = 0
  . simp[hspm]
    norm_num
  specialize this m (by omega)
  assumption'

noncomputable abbrev Example_6_4_8 : Sequence := (fun (n:ℕ) ↦ if Even n then (n+1:ℝ) else -(n:ℝ)-1)

example (n:ℕ) : Example_6_4_8.upperseq n = ⊤ := by sorry

example : Example_6_4_8.limsup = ⊤ := by sorry

example (n:ℕ) : Example_6_4_8.lowerseq n = ⊥ := by sorry

example : Example_6_4_8.liminf = ⊥ := by sorry

noncomputable abbrev Example_6_4_9 : Sequence :=
  (fun (n:ℕ) ↦ if Even n then (n+1:ℝ)⁻¹ else -(n+1:ℝ)⁻¹)

example (n:ℕ) : Example_6_4_9.upperseq n = if Even n then (n+1:ℝ)⁻¹ else -(n+2:ℝ)⁻¹ := by sorry

example : Example_6_4_9.limsup = 0 := by sorry

example (n:ℕ) : Example_6_4_9.lowerseq n = if Even n then -(n+2:ℝ)⁻¹ else -(n+1:ℝ)⁻¹ := by sorry

example : Example_6_4_9.liminf = 0 := by sorry

noncomputable abbrev Example_6_4_10 : Sequence := (fun (n:ℕ) ↦ (n+1:ℝ))

example (n:ℕ) : Example_6_4_10.upperseq n = ⊤ := by sorry

example : Example_6_4_9.limsup = ⊤ := by sorry

example (n:ℕ) : Example_6_4_9.lowerseq n = n+1 := by sorry

example : Example_6_4_9.liminf = ⊤ := by sorry

/-- Proposition 6.4.12(a) -/
theorem Sequence.gt_limsup_bounds {a:Sequence} {x:EReal} (h: x > a.limsup) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n < x := by
  -- This proof is written to follow the structure of the original text.
  simp [limsup, sInf_lt_iff] at h
  obtain ⟨_, ⟨ N, ⟨ hN, rfl ⟩ ⟩, ha ⟩ := h; use N
  simp [hN, upperseq] at ha ⊢; intro n _
  have hn' : n ≥ (a.from N).m := by grind
  convert lt_of_le_of_lt ((a.from N).le_sup hn') ha using 1
  grind

/-- Proposition 6.4.12(a) -/
theorem Sequence.lt_liminf_bounds {a:Sequence} {y:EReal} (h: y < a.liminf) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n > y := by
  sorry

/-- Proposition 6.4.12(b) -/
theorem Sequence.lt_limsup_bounds {a:Sequence} {x:EReal} (h: x < a.limsup) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n > x := by
  -- This proof is written to follow the structure of the original text.
  have hx : x < a.upperseq N := by apply lt_of_lt_of_le h (sInf_le _); simp; use N
  choose n hn hxn _ using exists_between_lt_sup hx
  grind

/-- Proposition 6.4.12(b) -/
theorem Sequence.gt_liminf_bounds {a:Sequence} {x:EReal} (h: x > a.liminf) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n < x := by
  sorry

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.inf_le_liminf (a:Sequence) : a.inf ≤ a.liminf := by sorry

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.liminf_le_limsup (a:Sequence) : a.liminf ≤ a.limsup := by sorry

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.limsup_le_sup (a:Sequence) : a.limsup ≤ a.sup := by sorry

/-- Proposition 6.4.12(d) / Exercise 6.4.3 -/
theorem Sequence.limit_point_between_liminf_limsup {a:Sequence} {c:ℝ} (h: a.LimitPoint c) :
  a.liminf ≤ c ∧ c ≤ a.limsup := by
  sorry

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_limsup {a:Sequence} {L_plus:ℝ} (h: a.limsup = L_plus) :
    a.LimitPoint L_plus := by
  sorry

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_liminf {a:Sequence} {L_minus:ℝ} (h: a.liminf = L_minus) :
    a.LimitPoint L_minus := by
  sorry

/-- Proposition 6.4.12(f) / Exercise 6.4.3 -/
theorem Sequence.tendsTo_iff_eq_limsup_liminf {a:Sequence} (c:ℝ) :
  a.TendsTo c ↔ a.liminf = c ∧ a.limsup = c := by
  sorry

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.sup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.sup ≤ b.sup := by sorry

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.inf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.inf ≤ b.inf := by sorry

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.limsup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.limsup ≤ b.limsup := by sorry

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.liminf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.liminf ≤ b.liminf := by sorry

/-- Corollary 6.4.14 (Squeeze test) / Exercise 6.4.5 -/
theorem Sequence.lim_of_between {a b c:Sequence} {L:ℝ} (hm: b.m = a.m ∧ c.m = a.m)
  (hab: ∀ n ≥ a.m, a n ≤ b n ∧ b n ≤ c n) (ha: a.TendsTo L) (hb: b.TendsTo L) :
    c.TendsTo L := by sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ 2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ -2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (-1)^n/(n+1:ℝ) + 1 / (n+1)^2):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (2:ℝ)^(-(n:ℤ))):Sequence).TendsTo 0 := by
  sorry

abbrev Sequence.abs (a:Sequence) : Sequence where
  m := a.m
  seq n := |a n|
  vanish n hn := by simp [a.vanish n hn]


/-- Corollary 6.4.17 (Zero test for sequences) / Exercise 6.4.7 -/
theorem Sequence.tendsTo_zero_iff (a:Sequence) :
  a.TendsTo (0:ℝ) ↔ a.abs.TendsTo (0:ℝ) := by
  sorry

/--
  This helper lemma, implicit in the textbook proofs of Theorem 6.4.18 and Theorem 6.6.8, is made
  explicit here.
-/
theorem Sequence.finite_limsup_liminf_of_bounded {a:Sequence} (hbound: a.IsBounded) :
    (∃ L_plus:ℝ, a.limsup = L_plus) ∧ (∃ L_minus:ℝ, a.liminf = L_minus) := by
  choose M hMpos hbound using hbound
  have hlimsup_bound : a.limsup ≤ M := by
    apply a.limsup_le_sup.trans (sup_le_upper _)
    intro n hN; simp
    exact (le_abs_self _).trans (hbound n)
  have hliminf_bound : -M ≤ a.liminf := by
    apply (inf_ge_lower _).trans a.inf_le_liminf
    intro n hN; simp [←coe_neg]; rw [neg_le]
    exact (neg_le_abs _).trans (hbound n)
  split_ands
  . use a.limsup.toReal
    symm; apply coe_toReal
    . contrapose! hlimsup_bound; simp [hlimsup_bound]
    replace hliminf_bound := hliminf_bound.trans a.liminf_le_limsup
    contrapose! hliminf_bound; simp [hliminf_bound, ←coe_neg]
  use a.liminf.toReal; symm; apply coe_toReal
  . apply a.liminf_le_limsup.trans at hlimsup_bound
    contrapose! hlimsup_bound; simp [hlimsup_bound]
  contrapose! hliminf_bound; simp [hliminf_bound, ←coe_neg]

/-- Theorem 6.4.18 (Completeness of the reals) -/
theorem Sequence.Cauchy_iff_convergent (a:Sequence) :
  a.IsCauchy ↔ a.Convergent := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, IsCauchy.convergent ⟩; intro h
  have ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ L_minus, hL_minus ⟩ ⟩ :=
    finite_limsup_liminf_of_bounded (bounded_of_cauchy h)
  use L_minus; simp [tendsTo_iff_eq_limsup_liminf, hL_minus, hL_plus]
  have hlow : 0 ≤ L_plus - L_minus := by
    have := a.liminf_le_limsup; simp [hL_minus, hL_plus] at this; grind
  have hup (ε:ℝ) (hε: ε>0) : L_plus - L_minus ≤ 2*ε := by
    specialize h ε hε; choose N hN hsteady using h
    have hN0 : N ≥ (a.from N).m := by grind
    have hN1 : (a.from N).seq N = a.seq N := by grind
    have h1 : (a N - ε:ℝ) ≤ (a.from N).inf := by
      apply inf_ge_lower; grind [Real.dist_eq, abs_le',EReal.coe_le_coe_iff]
    have h2 : (a.from N).inf ≤ L_minus := by
      simp_rw [←hL_minus, liminf, lowerseq]; apply le_sSup; simp; use N
    have h3 : (a.from N).sup ≤ (a N + ε:ℝ) := by
      apply sup_le_upper; grind [EReal.coe_le_coe_iff, Real.dist_eq, abs_le']
    have h4 : L_plus ≤ (a.from N).sup := by
      simp_rw [←hL_plus, limsup, upperseq]; apply sInf_le; simp; use N
    replace h1 := h1.trans h2
    replace h4 := h4.trans h3
    grind [EReal.coe_le_coe_iff]
  obtain hlow | hlow := le_iff_lt_or_eq.mp hlow
  . specialize hup ((L_plus - L_minus)/3) ?_ <;> linarith
  grind

/-- Exercise 6.4.6 -/
theorem Sequence.sup_not_strict_mono : ∃ (a b:ℕ → ℝ), (∀ n, a n < b n) ∧ (a:Sequence).sup ≠ (b:Sequence).sup := by
  sorry

/- Exercise 6.4.7 -/
def Sequence.tendsTo_real_iff :
  Decidable (∀ (a:Sequence) (x:ℝ), a.TendsTo x ↔ a.abs.TendsTo x) := by
  -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
  sorry

/-- This definition is needed for Exercises 6.4.8 and 6.4.9. -/
abbrev Sequence.ExtendedLimitPoint (a:Sequence) (x:EReal) : Prop := if x = ⊤ then ¬ a.BddAbove else if x = ⊥ then ¬ a.BddBelow else a.LimitPoint x.toReal

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_limsup (a:Sequence) : a.ExtendedLimitPoint a.limsup := by sorry

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_liminf (a:Sequence) : a.ExtendedLimitPoint a.liminf := by sorry

theorem Sequence.extended_limit_point_le_limsup {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≤ a.limsup := by sorry

theorem Sequence.extended_limit_point_ge_liminf {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≥ a.liminf := by sorry

/-- Exercise 6.4.9 -/
theorem Sequence.exists_three_limit_points : ∃ a:Sequence, ∀ L:EReal, a.ExtendedLimitPoint L ↔ L = ⊥ ∨ L = 0 ∨ L = ⊤ := by sorry

/-- Exercise 6.4.10 -/
theorem Sequence.limit_points_of_limit_points {a b:Sequence} {c:ℝ} (hab: ∀ n ≥ b.m, a.LimitPoint (b n)) (hbc: b.LimitPoint c) : a.LimitPoint c := by sorry


end Chapter6
