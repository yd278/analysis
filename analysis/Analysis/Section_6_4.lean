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
lemma Real.exists_decimal_lt {ε :ℝ} (hε: ε >0) : ∃ (N:ℕ), ∀ n ≥ N, (10:ℝ) ^(-(n:ℤ) - 1) < ε := by
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
  . have :(-1:ℝ)^ x = 1 := by exact Even.neg_one_pow hpar
    simp[this]
    rw[abs_of_pos (by positivity)]
    calc
      _ < (1:ℝ) := by linarith
      _ < _ := by simp; positivity
  . simp at hpar
    have: (-1:ℝ)^x = (-1) := by exact Odd.neg_one_pow hpar
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
-- tends to c <-> bdd above and below
-- bdd <-> sup 

noncomputable abbrev Sequence.liminf (a:Sequence) : EReal :=
  sSup { x | ∃ N ≥ a.m, x = a.lowerseq N }

-- add some useful lemma here
lemma Sequence.sup_of_max {a:Sequence} {n:ℤ} (hn : n ≥ a.m) (han : ∀ m ≥ a.m, a m ≤ a n) : a.sup = a n:= by
  have hle: a n ≤ a.sup  := by exact le_sup hn
  have hge: a.sup ≤ a n:= by
    apply sup_le_upper
    peel han with m hm han
    rw[EReal.le_iff];left
    use a m, a n
  apply eq_of_le_of_ge hge hle
lemma Sequence.inf_of_min {a:Sequence} {n:ℤ} (hn : n ≥ a.m) (han : ∀ m ≥ a.m, a m ≥ a n) : a.inf = a n:= by
  have hle: a n ≥ a.inf  := by exact ge_inf hn
  have hge: a.inf ≥ a n:= by
    apply inf_ge_lower
    peel han with m hm han
    simp[han]
  apply eq_of_le_of_ge hle hge
lemma Sequence.sup_of_unbounded_above {a:Sequence} (ha : ¬ a.BddAbove) : a.sup = ⊤ := by
  contrapose! ha
  obtain ⟨l,hr⟩|htop|hbot := a.sup.def 
  . use l
    intro n hn
    have := le_sup hn
    rw[← hr] at this
    simpa using this
  . contradiction
  have := le_sup (show a.m ≥ a.m by simp)
  rw[hbot] at this
  simp at this
lemma Sequence.upperseq_of_unbounded_above {a:Sequence} (ha : ¬ a.BddAbove) {n:ℤ} (hn : n ≥ a.m):
    a.upperseq n = ⊤ := by
      unfold Sequence.upperseq
      apply Sequence.sup_of_unbounded_above
      induction' n,hn using Int.le_induction with k hk hind
      . have :a.from a.m = a := by 
          ext m
          . simp
          simp
          intro h
          have := a.vanish m h
          simp[this]
        rwa[this]
      contrapose! hind
      choose bon hbon using hind
      use max bon (a k)
      intro n hn
      by_cases hnk : n = k
      . simp[hnk]
        split_ifs with hkam
        <;>right<;>simp
      replace hnk : n ≥ k+1 := by
        simp at hn
        omega
      specialize hbon n (by simp[hnk];linarith)
      have: a.from (k+1) n = a.from k n := by
        simp[hnk]
        have :a.m ≤  n := by linarith
        simp[this]
        intro hnk';linarith
      rw[this] at hbon
      apply le_trans hbon
      simp
lemma Sequence.limsup_of_unbounded_above { a:Sequence} (ha : ¬ a.BddAbove):
    a.limsup = ⊤ := by
      unfold limsup
      simp
      intro ub n hn
      have := upperseq_of_unbounded_above ha hn
      rw[this]
      simp
lemma Sequence.inf_of_unbounded_below {a:Sequence} (ha : ¬ a.BddBelow) : a.inf = ⊥ := by
  contrapose! ha
  obtain ⟨l,hr⟩|htop|hbot := a.inf.def 
  . use l
    intro n hn
    have := ge_inf hn
    rw[← hr] at this
    simpa using this
  . have := ge_inf (show a.m ≥ a.m by simp)
    rw[htop] at this
    simp at this
  contradiction
lemma Sequence.lowerseq_of_unbounded_below {a:Sequence} (ha : ¬ a.BddBelow) {n:ℤ} (hn : n ≥ a.m):
    a.lowerseq n = ⊥ := by
      unfold Sequence.lowerseq
      apply Sequence.inf_of_unbounded_below
      induction' n,hn using Int.le_induction with k hk hind
      . have :a.from a.m = a := by 
          ext m
          . simp
          simp
          intro h
          have := a.vanish m h
          simp[this]
        rwa[this]
      contrapose! hind
      choose bon hbon using hind
      use min bon (a k)
      intro n hn
      by_cases hnk : n = k
      . simp[hnk]
        split_ifs with hkam
        <;>right <;> simp
      replace hnk : n ≥ k+1 := by
        simp at hn
        omega
      specialize hbon n (by simp[hnk];linarith)
      have: a.from (k+1) n = a.from k n := by
        simp[hnk]
        have :a.m ≤  n := by linarith
        simp[this]
        intro hnk';linarith
      rw[this] at hbon
      apply ge_trans hbon
      simp
lemma Sequence.liminf_of_unbounded_below { a:Sequence} (ha : ¬ a.BddBelow ):
    a.liminf = ⊥ := by
      unfold liminf
      simp
      intro ub n hn
      have := lowerseq_of_unbounded_below ha hn
      rw[this]
      simp
/- -- for both Example_6_4_7 and Example_6_4_9, they are alternating sequences: -/
/-     -- positive even terms and negative odd terms -/
/-     -- antitone even sub-sequences -/
/-     -- monotone odd sub-sequences -/
abbrev Sequence.Alternating (a:Sequence) := ∀ n ≥ a.m, if Even n then a n > 0 else a n < 0
lemma Sequence.Alternating_trans {a:Sequence} (haa: a.Alternating) : (a.from n).Alternating := by
  unfold Alternating  at haa ⊢
  intro m hm
  simp at hm
  specialize haa m hm.1
  simpa[hm]
abbrev Sequence.Even_Antitone (a:Sequence):= ∀ n ≥ a.m, Even n → a (n + 2) ≤ a n
lemma Sequence.Even_Antitone_trans {a:Sequence} (haea : a.Even_Antitone) {n:ℤ} : (a.from n).Even_Antitone := by
  unfold Even_Antitone  at haea ⊢
  intro m hm hme
  simp at hm
  specialize haea m hm.1 hme
  simpa[hm, show a.m ≤ m+2 by linarith,show n ≤ m+2 by linarith]
abbrev Sequence.Odd_Monotone (a: Sequence) := ∀ n ≥ a.m, Odd n → a (n + 2) ≥ a n
lemma Sequence.Odd_Monotone_trans {a:Sequence} (haom : a.Odd_Monotone) : (a.from n).Odd_Monotone := by
  unfold Odd_Monotone  at haom ⊢
  intro m hm hme
  simp at hm
  specialize haom m hm.1 hme
  simpa[hm, show a.m ≤ m+2 by linarith,show n ≤ m+2 by linarith]

/- -- Exercises are: -/
/-     -- show that upperseq n is a (ceilEven n) ✅ -/
/-     -- show that lowerseq n is a (ceilOdd n) ✅ -/
/-     -- show that limsup is inf even_subseq ✅ -/
/-     -- calculate liminf is sup odd_subseq ✅ -/
/-     -- calculate sup✅ -/
/-     -- calculate inf✅ -/
end Chapter6
abbrev Nat.ceilEven (n:ℕ ) := if Even n then n else n + 1
lemma Nat.ceilEven_ge (n:ℕ ) :  n.ceilEven ≥ n := by
  simp[ceilEven]
  split_ifs <;> simp
lemma Nat.ceilEven_least (n:ℕ ) {m :ℕ } (hmn : m≥ n) (hme : Even m):
    m≥ n.ceilEven := by
      simp[ceilEven]
      split_ifs with hne
      . assumption
      by_contra!
      have : m = n := by omega
      rw[this] at hme;contradiction
lemma Nat.ceilEven_Even (n:ℕ ) : Even n.ceilEven := by
  simp[ceilEven]
  split_ifs with hn
  . assumption
  rwa[even_add_one]

abbrev Nat.ceilOdd (n:ℕ ) := if Odd n then n else n + 1
lemma Nat.ceilOdd_ge (n:ℕ ) :  n.ceilOdd ≥ n := by
  simp[ceilOdd]
  split_ifs <;> simp
lemma Nat.ceilOdd_Odd (n:ℕ ) : Odd n.ceilOdd := by
  simp[ceilOdd]
  split_ifs with hn
  . assumption
  simp at hn
  exact Even.add_one hn
lemma Nat.ceilOdd_least (n:ℕ ) {m :ℕ } (hmn : m≥ n) (hme : Odd m):
    m≥ n.ceilOdd := by
      simp[ceilOdd]
      split_ifs with hne
      . assumption
      by_contra!
      have : m = n := by omega
      rw[this] at hme;contradiction

abbrev Int.ceilEven (n:ℤ) := if Even n then n else n + 1
lemma Int.ceilEven_ge (n:ℤ) :  n.ceilEven ≥ n := by
  simp[ceilEven]
  split_ifs <;> simp
lemma Int.ceilEven_least (n:ℤ) {m :ℤ} (hmn : m≥ n) (hme : Even m):
    m≥ n.ceilEven := by
      simp[ceilEven]
      split_ifs with hne
      . assumption
      by_contra!
      have : m = n := by omega
      rw[this] at hme;contradiction
lemma Int.ceilEven_Even (n:ℤ) : Even n.ceilEven := by
  simp[ceilEven]
  split_ifs with hn
  . assumption
  rwa[even_add_one]

abbrev Int.ceilOdd (n:ℤ) := if Odd n then n else n + 1
lemma Int.ceilOdd_ge (n:ℤ) :  n.ceilOdd ≥ n := by
  simp[ceilOdd]
  split_ifs <;> simp
lemma Int.ceilOdd_Odd (n:ℤ) : Odd n.ceilOdd := by
  simp[ceilOdd]
  split_ifs with hn
  . assumption
  simp at hn
  exact Even.add_one hn
lemma Int.ceilOdd_least (n:ℤ) {m :ℤ} (hmn : m≥ n) (hme : Odd m):
    m≥ n.ceilOdd := by
      simp[ceilOdd]
      split_ifs with hne
      . assumption
      by_contra!
      have : m = n := by omega
      rw[this] at hme;contradiction
namespace Chapter6
lemma Sequence.even_antitone_trans {a:Sequence} (haea : a.Even_Antitone ) {n m :ℤ} 
  (hn : n≥ a.m) (hmn : m ≥ n ) (hme : Even m) (hne : Even n) :
    a m ≤ a n := by
      suffices h: ∀ (i:ℕ), a n ≥ a (n + (i + i)) from by
        choose d hd0 hd using exists_nonneg_add_of_le hmn
        have hde: Even d := by
          have hd : d = m - n := by linarith
          simp[hd]
          exact Even.sub hme hne
        lift d to ℕ using hd0
        simp at hde
        simp[Even] at hde
        choose i hi using hde
        rw[← hd,hi]
        exact h i
      -- now we can do induction
      intro i
      induction' i with k hind
      . simp
      apply ge_trans hind
      norm_cast
      have: (n + ((k + 1 + (k + 1):ℕ ):ℤ)) = (n + ((k + k:ℕ):ℤ)) + 2 := by
        ring_nf
        have : ((2 + k * 2:ℕ):ℤ ) = 2 + ((k * 2:ℕ ) :ℤ) := by rfl
        rw[this]
        ring
      rw[this]
      set v := n + (k + k:ℕ)
      have hve : Even v := by
        simp[v]
        apply Even.add hne
        simp
      have hvm : v ≥ a.m := by simp[v];linarith
      apply haea v hvm hve
lemma Sequence.sup_of_alternating_and_even_antitone {a:Sequence} (haa : a.Alternating ) (haea: a.Even_Antitone) :
    a.sup = a (a.m.ceilEven) := by
      apply sup_of_max a.m.ceilEven_ge
      intro m hm 
      have hm'e := a.m.ceilEven_Even
      by_cases hmp : Even m
      . have hmge : m ≥ a.m.ceilEven := a.m.ceilEven_least hm hmp
        have := a.m.ceilEven_ge
        apply even_antitone_trans haea this hmge hmp hm'e
      have hneg := haa m hm
      simp[hmp] at hneg
      have hpos := haa a.m.ceilEven a.m.ceilEven_ge
      simp[hm'e] at hpos
      linarith
lemma Sequence.upperseq_of_alternating_and_even_antitone {a:Sequence} (haa : a.Alternating) (haea : a.Even_Antitone)
    {n:ℤ} (hn : n ≥ a.m) :
      a.upperseq n = a (n.ceilEven) := by
      unfold upperseq
      set a' := a.from n
      have hn' : n = a'.m := by simp[a',hn]
      have hnn' := n.ceilEven_ge
      have hna' : a.m ≤ n.ceilEven := le_trans hn hnn'
      have hsubst : a n.ceilEven = a' n.ceilEven := by
        simp[a',hna',hnn']
      rw[hsubst,hn']
      apply sup_of_alternating_and_even_antitone
      exact Alternating_trans haa
      exact Even_Antitone_trans haea

lemma Sequence.odd_monotone_trans {a:Sequence} (haom : a.Odd_Monotone) {n m :ℤ}
  (hn : n≥ a.m) (hmn : m ≥ n ) (hme : Odd m) (hne : Odd n) :
    a m ≥  a n := by
      suffices h: ∀ (i:ℕ), a n ≤ a (n + (i + i)) from by
        choose d hd0 hd using exists_nonneg_add_of_le hmn
        have hde: Even d := by
          have hd : d = m - n := by linarith
          simp[hd]
          exact Odd.sub_odd hme hne
        lift d to ℕ using hd0
        simp at hde
        simp[Even] at hde
        choose i hi using hde
        rw[← hd,hi]
        exact h i
      -- now we can do induction
      intro i
      induction' i with k hind
      . simp
      apply le_trans hind
      norm_cast
      have: (n + ((k + 1 + (k + 1):ℕ ):ℤ)) = (n + ((k + k:ℕ):ℤ)) + 2 := by
        ring_nf
        have : ((2 + k * 2:ℕ):ℤ ) = 2 + ((k * 2:ℕ ) :ℤ) := by rfl
        rw[this]
        ring
      rw[this]
      set v := n + (k + k:ℕ)
      have hve : Odd v := by
        simp[v]
        apply Odd.add_even hne
        simp
      have hvm : v ≥ a.m := by simp[v];linarith
      apply haom v hvm hve
lemma Sequence.inf_of_alternating_and_odd_monotone {a:Sequence} (haa : a.Alternating ) (haom: a.Odd_Monotone) :
    a.inf = a (a.m.ceilOdd) := by
      apply inf_of_min a.m.ceilOdd_ge
      intro m hm 
      have hm'e : ¬ Even a.m.ceilOdd := by simp; exact a.m.ceilOdd_Odd
      by_cases hmp : Odd m
      . have hmge : m ≥ a.m.ceilOdd := a.m.ceilOdd_least hm hmp
        have := a.m.ceilOdd_ge
        apply odd_monotone_trans haom this hmge hmp
        simpa using hm'e
      have hpos := haa m hm
      simp at hmp
      simp[hmp] at hpos
      have hneg := haa a.m.ceilOdd a.m.ceilOdd_ge
      simp[hm'e] at hneg
      linarith
lemma Sequence.lowerseq_of_alternating_and_odd_monotone {a:Sequence} (haa : a.Alternating) (hamo : a.Odd_Monotone)
    {n:ℤ} (hn : n ≥ a.m) :
      a.lowerseq n = a (n.ceilOdd) := by
      unfold lowerseq
      set a' := a.from n
      have hn' : n = a'.m := by simp[a',hn]
      have hnn' := n.ceilOdd_ge
      have hna' : a.m ≤ n.ceilOdd := le_trans hn hnn'
      have hsubst : a n.ceilOdd = a' n.ceilOdd := by
        simp[a',hna',hnn']
      rw[hsubst,hn']
      apply inf_of_alternating_and_odd_monotone
      exact Alternating_trans haa
      exact Odd_Monotone_trans hamo

lemma Sequence.limsup_of_alternating_and_even_aititone {a:Sequence} (haa: a.Alternating) (haea : a.Even_Antitone) :
    a.limsup = sInf {(x:EReal) | ∃N ≥ a.m, Even N ∧x = a N} := by
      unfold limsup
      congr! 1
      ext x; simp
      constructor
      . rintro ⟨N,hN,heq⟩ 
        rw[upperseq_of_alternating_and_even_antitone haa haea hN] at heq
        simp[Int.ceilEven] at heq
        split_ifs at heq with hNe
        . use N
        use (N+1)
        split_ands
        . linarith
        . exact Int.even_add_one.mpr hNe
        assumption
      rintro ⟨N,hN,hNe,hNx⟩ 
      use N,hN
      rw[upperseq_of_alternating_and_even_antitone haa haea hN]
      simpa[Int.ceilEven,hNe]
lemma Sequence.liminf_of_alternating_and_odd_monotone {a:Sequence} (haa: a.Alternating) (haom : a.Odd_Monotone) :
    a.liminf = sSup {(x:EReal) | ∃N ≥ a.m, Odd N ∧x = a N} := by
      unfold liminf
      congr! 1
      ext x; simp
      constructor
      . rintro ⟨N,hN,heq⟩ 
        rw[lowerseq_of_alternating_and_odd_monotone haa haom hN] at heq
        simp[Int.ceilOdd] at heq
        split_ifs at heq with hNe
        . use N
        use (N+1)
        split_ands
        . linarith
        . simp at hNe; exact Even.add_one hNe
        assumption
      rintro ⟨N,hN,hNe,hNx⟩ 
      use N,hN
      rw[lowerseq_of_alternating_and_odd_monotone haa haom hN]
      simpa[Int.ceilOdd,hNe]

noncomputable abbrev Example_6_4_7 : Sequence := (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

lemma Example_6_4_7.alternating : Example_6_4_7.Alternating := by
  intro n hn
  simp at hn
  lift n to ℕ using hn
  split_ifs with hn <;> simp at hn <;> simp
  . 
    observe : (-1:ℝ) ^ n = 1
    simp[this]
    positivity
  observe : (-1:ℝ) ^ n = -1
  simp only [this, neg_mul, one_mul, neg_lt_zero]
  positivity
lemma Example_6_4_7.even_antitone : Example_6_4_7.Even_Antitone := by
  intro n hn hne
  simp at hn
  lift n to ℕ using hn
  simp at hne
  simp [show 0 ≤ (n:ℤ)+2  by linarith,
    show ((n:ℤ)+2).toNat = n + 2 by rfl
  ]
  have hne2 : Even (n+2) := by apply Even.add hne; simp
  simp[hne,hne2]
lemma Example_6_4_7.odd_monotone : Example_6_4_7.Odd_Monotone := by
  intro n hn hne
  simp at hn
  lift n to ℕ using hn
  simp at hne
  simp [show 0 ≤ (n:ℤ)+2  by linarith,
    show ((n:ℤ)+2).toNat = n + 2 by rfl
  ]
  have hne2 : Odd (n+2) := by apply Odd.add_even hne; simp
  simp[hne,hne2]

example (n:ℕ) :
    Example_6_4_7.upperseq n = if Even n then 1 + (10:ℝ)^(-(n:ℤ)-1) else 1 + (10:ℝ)^(-(n:ℤ)-2) := by
      set m := (n:ℤ)
      suffices hsubst : (if Even n then (1:ℝ ) + (10:ℝ)^(-m-1) else (1:ℝ) + (10:ℝ)^(-m-2)) = Example_6_4_7 m.ceilEven from by
        rw[hsubst]
        apply Sequence.upperseq_of_alternating_and_even_antitone
        exact Example_6_4_7.alternating
        exact Example_6_4_7.even_antitone
        exact Int.natCast_nonneg n
      unfold Int.ceilEven
      have heven : Even n ↔ Even m := by simp[m]
      simp only [← heven]
      split_ifs with hne hm hm1
      . simp[m,hne]
      . omega
      . 
        have heven1 : Even (n+1) := by exact Nat.even_add_one.mpr hne
        simp[m,heven1]
        ring
      . omega
example : Example_6_4_7.limsup = 1 := by
  suffices hans : (1:EReal) = sInf {(x:EReal) | ∃ N ≥ Example_6_4_7.m, Even N ∧ x = Example_6_4_7 N} from by
    rw[hans]
    apply Sequence.limsup_of_alternating_and_even_aititone
    exact Example_6_4_7.alternating
    exact Example_6_4_7.even_antitone
  symm
  apply IsGLB.sInf_eq
  constructor
  . intro x hx
    simp at hx
    choose N hN hNE hNx using hx
    lift N to ℕ using hN
    simp at hNx hNE
    simp[hNE] at hNx
    rw[← EReal.coe_one,
      ← EReal.coe_add
    ] at hNx
    rw[← EReal.coe_one, hNx,EReal.coe_le_coe_iff]
    simp;positivity
  intro x hx 
  rw[mem_lowerBounds] at hx
  obtain ⟨x,rfl⟩ | rfl | rfl := x.def 
  . norm_cast
    contrapose! hx
    set ε := x - 1
    observe hε : ε > 0
    choose N hN using Real.exists_decimal_lt hε 
    have hN'E := N.ceilEven_Even
    set N' := N.ceilEven 
    have hN'x := hN N' N.ceilEven_ge
    use Example_6_4_7 N'
    simp
    split_ands
    . use N'
      simp[hN'E]
    simp[hN'E]
    rw[← EReal.coe_one, ← EReal.coe_add,EReal.coe_lt_coe_iff]
    linarith
  .
    specialize hx (Example_6_4_7 0)
    simp at hx
    specialize hx 0
    simp at hx
    contradiction
  simp
example (n:ℕ) :
    Example_6_4_7.lowerseq n
    = if Even n then -(1 + (10:ℝ)^(-(n:ℤ)-2)) else -(1 + (10:ℝ)^(-(n:ℤ)-1)) := by
      set m := (n:ℤ)
      suffices hsubst : (if Even n then -((1:ℝ)  + (10:ℝ)^(-(m)-2)) else -((1:ℝ ) + (10:ℝ)^(-(m)-1)) ) = Example_6_4_7 m.ceilOdd from by
        rw[hsubst]
        apply Sequence.lowerseq_of_alternating_and_odd_monotone
        exact Example_6_4_7.alternating
        exact Example_6_4_7.odd_monotone
        simp[m]
      unfold Int.ceilOdd
      have heven : ¬ Even n ↔ Odd m := by simp[m]
      simp only [← heven]
      split_ifs with hne hm hm1
      . have : Odd (n+1) := by exact Even.add_one hne
        simp[m,this]
        ring
      . omega
      . simp at hne
        simp[m,hne]
      omega
example : Example_6_4_7.liminf = -1 := by
  suffices hans : (-1:EReal) = sSup {(x:EReal) | ∃ N ≥ Example_6_4_7.m, Odd N ∧ x = Example_6_4_7 N} from by
    rw[hans]
    apply Sequence.liminf_of_alternating_and_odd_monotone
    exact Example_6_4_7.alternating
    exact Example_6_4_7.odd_monotone
  symm
  apply IsLUB.sSup_eq
  constructor
  . intro x hx
    simp at hx
    choose N hN hNE hNx using hx
    lift N to ℕ using hN
    simp at hNx hNE
    simp[hNE] at hNx
    rw[← EReal.coe_one,
      ← EReal.coe_add
    ] at hNx
    rw[← EReal.coe_one, hNx, EReal.neg_le_neg_iff, EReal.coe_le_coe_iff]
    simp;positivity
  intro x hx 
  rw[mem_upperBounds] at hx
  obtain ⟨x,rfl⟩ | rfl | rfl := x.def 
  . rw[← EReal.coe_one,← EReal.coe_neg,EReal.coe_le_coe_iff]
    contrapose! hx
    set ε := -1 - x
    observe hε : ε > 0
    choose N hN using Real.exists_decimal_lt hε 
    have hN'E := N.ceilOdd_Odd
    set N' := N.ceilOdd 
    have hN'x := hN N' N.ceilOdd_ge
    use Example_6_4_7 N'
    simp
    split_ands
    . use N'
      simp[hN'E]
      simp_rw[← EReal.coe_one,← EReal.coe_add,← EReal.coe_neg]
      simp
    simp[hN'E]
    simp_rw[← EReal.coe_one, ← EReal.coe_add,← EReal.coe_neg, EReal.coe_lt_coe_iff]
    linarith
  .
    simp
  specialize hx (Example_6_4_7 1)
  simp at hx
  specialize hx 1
  simp at hx
  contradiction
example : Example_6_4_7.sup = (1.1:ℝ) := by
  have : (1.1:ℝ) = Example_6_4_7 (Example_6_4_7.m.ceilEven) := by
    simp[Int.ceilEven]
    norm_num
  rw[this]
  apply Sequence.sup_of_alternating_and_even_antitone
  exact Example_6_4_7.alternating
  exact Example_6_4_7.even_antitone
example : Example_6_4_7.inf = (-1.01:ℝ) := by
  have : (-1.01:ℝ) = Example_6_4_7 (Example_6_4_7.m.ceilOdd) := by
    simp[Int.ceilOdd]
    norm_num
  rw[this]
  apply Sequence.inf_of_alternating_and_odd_monotone
  exact Example_6_4_7.alternating
  exact Example_6_4_7.odd_monotone

noncomputable abbrev Example_6_4_8 : Sequence := (fun (n:ℕ) ↦ if Even n then (n+1:ℝ) else -(n:ℝ)-1)
lemma Example_6_4_8.unbounded_above : ¬ Example_6_4_8.BddAbove := by
  simp
  intro x
  choose N hN using exists_nat_gt x
  set N' := N.ceilEven 
  have hNN': N'≥ N := by exact Nat.ceilEven_ge N
  have hN'E: Even N' := by exact Nat.ceilEven_Even N
  use N'
  simp[hN'E]
  apply lt_trans hN
  norm_cast;linarith
lemma Example_6_4_8.unbounded_below : ¬ Example_6_4_8.BddBelow := by
  simp
  intro x
  wlog hx : x < 0
  . simp at hx
    use (1)
    simp;linarith
  choose N hN using exists_nat_gt (-x)
  set N' := N.ceilOdd
  have hNN' : N' ≥ N := N.ceilOdd_ge
  have hN'O : ¬ Even N' := by
    simp;exact Nat.ceilOdd_Odd N
  use N'
  simp[hN'O]
  rw[← neg_add',neg_lt]
  apply lt_trans hN
  norm_cast;linarith

example (n:ℕ) : Example_6_4_8.upperseq n = ⊤ := by
  apply Sequence.upperseq_of_unbounded_above
  exact Example_6_4_8.unbounded_above
  simp
example : Example_6_4_8.limsup = ⊤ := by
  apply Sequence.limsup_of_unbounded_above
  exact Example_6_4_8.unbounded_above
example (n:ℕ) : Example_6_4_8.lowerseq n = ⊥ := by
  apply Sequence.lowerseq_of_unbounded_below
  exact Example_6_4_8.unbounded_below
  simp
example : Example_6_4_8.liminf = ⊥ := by
  apply Sequence.liminf_of_unbounded_below
  exact Example_6_4_8.unbounded_below

noncomputable abbrev Example_6_4_9 : Sequence :=
  (fun (n:ℕ) ↦ if Even n then (n+1:ℝ)⁻¹ else -(n+1:ℝ)⁻¹)

lemma Example_6_4_9.alternating : Example_6_4_9.Alternating := by
  intro n hn
  simp at hn
  lift n to ℕ using hn
  split_ifs with hne <;> simp only [Int.even_coe_nat] at hne
  <;> simp[hne] <;>linarith
lemma Example_6_4_9.even_antitone : Example_6_4_9.Even_Antitone := by
  intro n hn hne
  simp at hn
  lift n to ℕ using hn
  simp at hne
  have : Even (n+2) := by
    apply Even.add hne
    simp
  simp[hne, show 0 ≤ (n:ℤ)+2 by linarith, show ((n:ℤ)+2).toNat = n+2 by rfl,this]
  apply inv_anti₀
  <;> linarith
lemma Example_6_4_9.odd_monotone : Example_6_4_9.Odd_Monotone  := by
  intro n hn hno
  simp at hn
  lift n to ℕ using hn
  simp at hno
  have : Odd (n+2) := by
    apply Odd.add_even hno
    simp
  observe hno' : ¬ Even n
  observe this' : ¬ Even (n+2)
  simp[hno' ,show 0 ≤ (n:ℤ)+2 by linarith,show ((n:ℤ)+2).toNat = n+2 by rfl,this']
  apply inv_anti₀
  <;> linarith

example (n:ℕ) : Example_6_4_9.upperseq n = if Even n then (n+1:ℝ)⁻¹ else (n+2:ℝ)⁻¹ := by
      set m := (n:ℤ)
      suffices hsubst : (if Even n then (n+1:ℝ)⁻¹ else (n+2:ℝ)⁻¹) = Example_6_4_9 m.ceilEven from by
        rw[hsubst]
        apply Sequence.upperseq_of_alternating_and_even_antitone
        exact Example_6_4_9.alternating
        exact Example_6_4_9.even_antitone
        exact Int.natCast_nonneg n
      unfold Int.ceilEven
      have heven : Even n ↔ Even m := by simp[m]
      simp only [← heven]
      by_cases hne : Even n
      . simp[hne,m]
      simp[hne,m, show 0 ≤ (n:ℤ)+1 by linarith]
      have : Even (n+1) := by exact Nat.even_add_one.mpr hne
      simp[this]
      ring
example : Example_6_4_9.limsup = 0 := by
  suffices hans : (0:EReal) = sInf {(x:EReal) | ∃ N ≥ Example_6_4_9.m, Even N ∧ x = Example_6_4_9 N} from by
    rw[hans]
    apply Sequence.limsup_of_alternating_and_even_aititone
    exact Example_6_4_9.alternating
    exact Example_6_4_9.even_antitone
  symm
  apply IsGLB.sInf_eq
  constructor
  . intro x hx
    simp at hx
    choose N hN hNE hNx using hx
    lift N to ℕ using hN
    simp at hNx hNE
    simp[hNE] at hNx
    rw[hNx,← EReal.coe_zero]
    simp;positivity
  . intro x hx 
    rw[mem_lowerBounds] at hx
    obtain ⟨x, rfl⟩ | rfl | rfl := x.def 
    . norm_cast
      contrapose! hx
      choose N hN hNx using Real.exists_nat_pos_inv_lt hx
      have hN'E := N.ceilEven_Even
      have hN'N := N.ceilEven_ge
      set N' := N.ceilEven
      use Example_6_4_9 N'
      split_ands
      . simp
        use N'
        simp[hN'E]
      simp[hN'E]
      apply lt_trans ?_ hNx
      rw[inv_lt_inv₀]
      norm_cast;linarith
      linarith
      norm_cast
    . specialize hx 1
      simp at hx
      specialize hx 0
      simp at hx
      contradiction
    . simp
example (n:ℕ) : Example_6_4_9.lowerseq n = if Even n then -(n+2:ℝ)⁻¹ else -(n+1:ℝ)⁻¹ := by
  set m := (n:ℤ)
  suffices hsubst: (if Even n then -(n+2:ℝ)⁻¹ else -(n+1:ℝ)⁻¹) = Example_6_4_9 m.ceilOdd from by
    rw[hsubst]
    apply Sequence.lowerseq_of_alternating_and_odd_monotone
    exact Example_6_4_9.alternating
    exact Example_6_4_9.odd_monotone
    simp[m]
  unfold Int.ceilOdd
  simp[m]
  by_cases hne : Even n
  . 
    observe hne' : ¬ Odd n
    have hne1 : ¬ Even (n+1) := by
      simp; exact Even.add_one hne
    simp[hne,hne',show 0 ≤ (n:ℤ)+1 by linarith,hne1]
    ring
  observe hne' : Odd n
  simp[hne,hne']
example : Example_6_4_9.liminf = 0 := by
  suffices hans : (0:EReal) = sSup {(x:EReal) | ∃ N ≥ Example_6_4_9.m, Odd N ∧ x = Example_6_4_9 N} from by
    rw[hans]
    apply Sequence.liminf_of_alternating_and_odd_monotone
    exact Example_6_4_9.alternating
    exact Example_6_4_9.odd_monotone
  symm
  apply IsLUB.sSup_eq
  constructor
  . intro x hx
    simp at hx
    choose N hN hNE hNx using hx
    lift N to ℕ using hN
    simp at hNx hNE
    observe hNE' : ¬ Even N
    simp[hNE'] at hNx
    rw[← EReal.coe_neg,
    ] at hNx
    rw[← EReal.coe_zero, hNx,  EReal.coe_le_coe_iff]
    simp;positivity
  intro x hx 
  rw[mem_upperBounds] at hx
  obtain ⟨x,rfl⟩ | rfl | rfl := x.def 
  . rw[← EReal.coe_zero,EReal.coe_le_coe_iff]
    contrapose! hx
    observe hx' : -x > 0
    choose N hN hNx using Real.exists_nat_pos_inv_lt hx'
    set N' := N.ceilOdd
    have hN'O: Odd N' := N.ceilOdd_Odd
    have hN'E: ¬ Even N' := by simp[hN'O]
    have hN'N : N' ≥ N := N.ceilOdd_ge
    use Example_6_4_9 N'
    split_ands
    . simp
      use N'
      simp[hN'O]
    simp[hN'E]
    rw[lt_neg] at hNx
    rw[← EReal.coe_neg]
    norm_cast
    apply lt_trans hNx
    simp
    rw[inv_lt_inv₀]
    norm_cast;linarith
    linarith
    simp[hN]
  . simp
  specialize hx (- (1+1:ℝ )⁻¹ )
  simp at hx
  specialize hx 1
  simp at hx

noncomputable abbrev Example_6_4_10 : Sequence := (fun (n:ℕ) ↦ (n+1:ℝ))
lemma Example_6_4_10.unbounded_above : ¬ Example_6_4_10.BddAbove := by
  simp
  intro x
  choose N hN using exists_nat_gt x
  use N
  simp
  linarith
lemma Example_6_4_10.lowerseq_def (n:ℕ): Example_6_4_10.lowerseq n = n+1 := by
  unfold Sequence.lowerseq
  have : (n:EReal) + 1 = Example_6_4_10.from n n := by
    simp
  rw[this]
  apply Sequence.inf_of_min
  . simp
  intro m hm
  simp at hm
  lift m to ℕ using by linarith
  simp at hm
  simp [hm]
example (n:ℕ) : Example_6_4_10.upperseq n = ⊤ := by
  apply Sequence.upperseq_of_unbounded_above
  exact Example_6_4_10.unbounded_above
  simp
example : Example_6_4_10.limsup = ⊤ := by
  apply Sequence.limsup_of_unbounded_above
  exact Example_6_4_10.unbounded_above
example (n:ℕ) : Example_6_4_10.lowerseq n = n+1 := by
  exact Example_6_4_10.lowerseq_def n
example : Example_6_4_10.liminf = ⊤ := by
  unfold Sequence.liminf
  rw[sSup_eq_top]
  intro b hb
  obtain ⟨b,rfl⟩ | rfl | rfl := b.def
  . choose N hN using exists_nat_gt b
    use N+1
    simp
    split_ands
    . use N
      simp
      simp_rw[← EReal.coe_one, ← EReal.coe_natCast, ←EReal.coe_add]
      have hn := Example_6_4_10.lowerseq_def N
      rw[hn]
      simp
    rw[← EReal.coe_one, ← EReal.coe_natCast,← EReal.coe_add,EReal.coe_lt_coe_iff]
    apply lt_trans hN
    norm_cast
    linarith

  . contradiction
  use 1
  simp
  split_ands
  use 0
  simp
  have := Example_6_4_10.lowerseq_def 0
  simp at this
  simp[this]
  exact compareOfLessAndEq_eq_lt.mp rfl


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
    simp[liminf, lt_sSup_iff] at h
    obtain ⟨_, ⟨N, ⟨hN, rfl⟩ ⟩ , ha⟩ := h; use N
    simp [hN,lowerseq] at ha ⊢ ;intro n _
    have hn' : n ≥ (a.from N).m := by grind
    apply lt_of_lt_of_le ha
    have := ((a.from N).ge_inf hn')
    simp[hn'] at this
    assumption'

/-- Proposition 6.4.12(b) -/
theorem Sequence.lt_limsup_bounds {a:Sequence} {x:EReal} (h: x < a.limsup) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n > x := by
  -- This proof is written to follow the structure of the original text.
  have hx : x < a.upperseq N := by apply lt_of_lt_of_le h (sInf_le _); simp; use N
  choose n hn hxn _ using exists_between_lt_sup hx
  grind

/-- Proposition 6.4.12(b)  -/
theorem Sequence.gt_liminf_bounds {a:Sequence} {x:EReal} (h: x > a.liminf) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n < x := by
      have hx : x > a.lowerseq N := by
        unfold liminf at h
        apply lt_of_le_of_lt ?_ h
        apply le_sSup; use N
      choose n hn hxn _ using exists_between_gt_inf hx
      grind

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/

lemma Sequence.lowerseq_monotone {a:Sequence} {n m :ℤ} (hnm : n ≥ m):
    a.lowerseq n ≥ a.lowerseq m := by
      simp
      intro x N hN hNn hNx
      simp[hN,hNn] at hNx
      simp[hNx]
      apply sInf_le
      use N
      simp[hN]
      split_ands
      . linarith
      intro hcon
      linarith

lemma Sequence.upperseq_antitone {a:Sequence} {n m :ℤ} (hnm : n ≤ m):
    a.upperseq n ≥ a.upperseq m := by
      simp
      intro x N hN hNn hNx
      simp[hN,hNn] at hNx
      simp[hNx]
      apply le_sSup
      use N
      simp[hN]
      split_ands
      . linarith
      intro hcon
      linarith
lemma Sequence.lower_le_upper {a: Sequence} {N:ℤ} (hN: N ≥ a.m) :
    a.lowerseq N ≤ a.upperseq N := by
      unfold lowerseq upperseq inf sup
      simp[hN]
      apply sInf_le_sSup
      use a N
      simp; use N
      simp

theorem Sequence.inf_le_liminf (a:Sequence) : a.inf ≤ a.liminf := by
  have : a.inf = a.lowerseq a.m := by
    congr;ext n; simp
    simp; intro hn; apply a.vanish _ hn
  rw[this]
  apply le_sSup
  use a.m

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.liminf_le_limsup (a:Sequence) : a.liminf ≤ a.limsup := by
  apply sSup_le
  intro x hx
  apply le_sInf
  intro y hy
  simp at hx hy
  obtain⟨ Nx,hNx,rfl⟩ := hx
  obtain⟨ Ny,hNy,rfl⟩ := hy
  set N := max Nx Ny
  have hlow : a.lowerseq Nx ≤ a.lowerseq N := by
    apply lowerseq_monotone
    simp[N]
  have hupp : a.upperseq Ny ≥ a.upperseq N := by
    apply a.upperseq_antitone
    simp[N]
  have hbr : a.lowerseq N ≤ a.upperseq N := by
    apply lower_le_upper
    simp[N]; left; linarith
  apply le_trans hlow 
  apply le_trans hbr hupp

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.limsup_le_sup (a:Sequence) : a.limsup ≤ a.sup := by
  have : a.sup = a.upperseq a.m := by
    congr;ext n; simp
    simp; intro hn; apply a.vanish _ hn
  rw[this]
  apply sInf_le
  use a.m


/-- Proposition 6.4.12(d) / Exercise 6.4.3 -/

lemma Sequence.limit_point_le_limsup {a:Sequence} {c:ℝ} (h: a.LimitPoint c) :
    c ≤ a.limsup := by
      by_contra! hcon
      rw[EReal.lt_iff_exists_real_btwn] at hcon
      choose m hml hmc using hcon
      simp at hmc
      choose N hN hNa using gt_limsup_bounds hml
      specialize h (c-m) (by linarith) N hN
      choose n hnN hclose using h
      simp at hnN
      simp[hnN,dist] at hclose
      specialize hNa n hnN.2
      rw[abs_le] at hclose
      simp at hNa
      linarith

lemma Sequence.liminf_le_limit_point {a:Sequence} {c:ℝ} (h: a.LimitPoint c) :
    a.liminf ≤ c := by
      by_contra! hcon
      rw[EReal.lt_iff_exists_real_btwn] at hcon
      choose m hmc hml using hcon
      simp at hmc
      choose N hN hNa using lt_liminf_bounds hml
      specialize h (m-c) (by linarith) N hN
      choose n hnN hclose using h
      simp at hnN
      simp[hnN,dist] at hclose
      specialize hNa n hnN.2
      rw[abs_le] at hclose
      simp at hNa
      linarith

theorem Sequence.limit_point_between_liminf_limsup {a:Sequence} {c:ℝ} (h: a.LimitPoint c) :
  a.liminf ≤ c ∧ c ≤ a.limsup := by
    refine⟨liminf_le_limit_point h,limit_point_le_limsup h⟩ 


/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_limsup {a:Sequence} {L_plus:ℝ} (h: a.limsup = L_plus) :
    a.LimitPoint L_plus := by
      intro ε hε N hN
      set up := L_plus + ε
      have hup : up > a.limsup := by
        simp[h];simp[up,hε]
      choose Nup hNup hNups using gt_limsup_bounds hup
      set lo := L_plus - ε
      have hlo : lo < a.limsup := by
        simp[h];simp[lo,hε]
      set Nup' := max Nup N
      have hNup' : Nup' ≥ a.m := by grind
      choose Nlo hNlo' hNlos using lt_limsup_bounds hlo hNup'
      have hNlo : Nlo ≥ Nup := by
        apply ge_trans hNlo'
        simp[Nup']
      specialize hNups Nlo hNlo
      simp at hNlos hNups
      use Nlo
      simp
      have hr1 : a.m ≤ Nlo := by linarith
      have hr2 : N ≤ Nlo := by apply le_trans ?_ hNlo'; simp[Nup']
      simp[hr1,hr2,dist]
      rw[abs_le]
      grind

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_liminf {a:Sequence} {L_minus:ℝ} (h: a.liminf = L_minus) :
    a.LimitPoint L_minus := by
      intro ε hε N hN
      set lo := L_minus - ε
      have hlo : lo < a.liminf := by
        simp[h];simp[lo,hε]
      choose Nlo hNlo hNlos using lt_liminf_bounds hlo
      set up := L_minus + ε
      have hup : up > a.liminf := by
        simp[h];simp[up,hε]
      set Nlo' := max Nlo N
      have hNlo' : Nlo' ≥ a.m := by grind
      choose Nup hNup' hNups using gt_liminf_bounds hup hNlo'
      have hNup : Nup ≥ Nlo := by
        apply ge_trans hNup'
        simp[Nlo']
      specialize hNlos Nup hNup
      simp at hNlos hNups
      use Nup
      simp
      have hr1 : a.m ≤ Nup := by linarith
      have hr2 : N ≤ Nup := by apply le_trans ?_ hNup'; simp[Nlo']
      simp[hr1,hr2,dist]
      rw[abs_le]
      grind

/-- Proposition 6.4.12(f) / Exercise 6.4.3 


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
    intro n hN; simp [←EReal.coe_neg]; rw [neg_le]
    exact (neg_le_abs _).trans (hbound n)
  split_ands
  . use a.limsup.toReal
    symm; apply EReal.coe_toReal
    . contrapose! hlimsup_bound; simp [hlimsup_bound]
    replace hliminf_bound := hliminf_bound.trans a.liminf_le_limsup
    contrapose! hliminf_bound; simp [hliminf_bound, ←EReal.coe_neg]
  use a.liminf.toReal; symm; apply EReal.coe_toReal
  . apply a.liminf_le_limsup.trans at hlimsup_bound
    contrapose! hlimsup_bound; simp [hlimsup_bound]
  contrapose! hliminf_bound; simp [hliminf_bound, ←EReal.coe_neg]

lemma Sequence.unique_limit_point_of_tendsTo {a:Sequence} {c d:ℝ} (ha : a.TendsTo c) (hd: a.LimitPoint d):
    d = c := by
      by_contra! hne
      set g := dist d c with hg
      have hg : g > 0 := by simp[g,hne]
      specialize ha (g/3) (by positivity)
      specialize hd (g/3) (by positivity)
      choose N hN hNa using ha
      specialize hd N hN
      choose n hn hna using hd
      specialize hNa n hn
      unfold Real.Close at hna hNa
      set an := (a.from N) n
      have hcon : dist d c ≤ (g/3) + (g/3) := by
        calc
          _ ≤ dist an d + dist an c := by exact dist_triangle_left d c an
          _ ≤ _ := by linarith
      linarith

theorem Sequence.tendsTo_iff_eq_limsup_liminf {a:Sequence} (c:ℝ) :
  a.TendsTo c ↔ a.liminf = c ∧ a.limsup = c := by
    constructor
    . 
      intro htends
      have hbdd : a.IsBounded  := by
        apply bounded_of_convergent
        use c
      obtain ⟨⟨lc, hlc⟩, ⟨uc,huc⟩⟩ := finite_limsup_liminf_of_bounded hbdd
      have hlcl : a.LimitPoint lc := by exact limit_point_of_limsup hlc
      have hucl : a.LimitPoint uc := by exact limit_point_of_liminf huc 
      have : lc = c := by exact unique_limit_point_of_tendsTo htends hlcl
      rw[this] at hlc
      have : uc = c := by exact unique_limit_point_of_tendsTo htends hucl
      rw[this] at huc
      tauto
    rintro ⟨hinf,hsup⟩ ε hε 
    set up := c + ε
    have hup : up > a.limsup := by
      simp[hsup];linarith
    choose Nup hNup hnup using gt_limsup_bounds hup
    set lo := c - ε
    have hlo : lo < a.liminf := by
      simp[hinf];linarith
    choose Nlo hNlo hnlo using lt_liminf_bounds hlo
    use max Nup Nlo
    simp[hNup,hNlo]
    set N := max Nup Nlo
    intro n hn
    simp at hn
    have hnNup : n ≥ Nup := by
      apply le_trans ?_ hn.2
      simp[N]
    have hnNlo : n ≥ Nlo := by
      apply le_trans ?_ hn.2
      simp[N]
    specialize hnup n hnNup
    specialize hnlo n hnNlo
    simp[dist,hn]
    simp at hnup hnlo
    simp[abs_le]
    grind

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.sup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.sup ≤ b.sup := by
      have hmid : ∀ n ≥ a.m, b n ≤ b.sup := by
        intro n hn
        rw[hm] at hn
        exact le_sup hn
      have hab : ∀ n ≥ a.m, a n ≤ b.sup := by
        intro n hn
        specialize hab n hn
        specialize hmid n hn
        apply le_trans ?_ hmid
        simpa
      apply sup_le_upper hab

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.inf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.inf ≤ b.inf := by
      apply inf_ge_lower
      intro n hn
      simp[← hm] at hn
      specialize hab n hn
      apply le_trans (ge_inf hn)
      simpa


/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.limsup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.limsup ≤ b.limsup := by
      have hupseq : ∀ N ≥ a.m, a.upperseq N ≤ b.upperseq N := by
        intro N hN
        apply sup_mono
        . simp[hm]
        intro n hn 
        simp at hn
        specialize hab n hn.1
        simp_all
      simp
      rintro bn n hn rfl
      rw[← hm] at hn
      apply sInf_le_of_le ?_ (hupseq n hn)
      simp
      use n


/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.liminf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.liminf ≤ b.liminf := by
      simp
      rintro an n hnn rfl
      apply le_sSup_of_le (b:= b.lowerseq n)
      use n; simp_all
      apply inf_mono; simp[hm]
      intro N hN
      simp_all
      apply hab
      linarith

/-- Corollary 6.4.14 (Squeeze test) / Exercise 6.4.5 -/
theorem Sequence.lim_of_between {a b c:Sequence} {L:ℝ} (hm: b.m = a.m ∧ c.m = a.m)
  (hac: ∀ n ≥ a.m, a n ≤ b n ∧ b n ≤ c n) (ha: a.TendsTo L) (hc: c.TendsTo L) :
    b.TendsTo L := by
      rw[tendsTo_iff_eq_limsup_liminf] at ha hc ⊢ 
      have hbi : b.liminf ≥ L := by
        rw[← ha.1]
        apply liminf_mono hm.1.symm
        simp_all
      have hbs : b.limsup ≤ L := by
        rw[← hc.2]
        apply limsup_mono
        <;>simp_all
      have hbil := liminf_le_limsup b
      split_ands <;> apply eq_of_le_of_ge
      assumption'
      apply le_trans hbil hbs
      apply le_trans hbi hbil

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ 2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  obtain ⟨hhcon, hhlim⟩  := Sequence.lim_harmonic
  set a := ((fun (n:ℕ)↦ (n+1:ℝ)⁻¹):Sequence)
  set b := ((fun (n:ℕ) ↦ 2/(n+1:ℝ)):Sequence)
  have hb : b = a + a := by
    ext n
    . change 0 = min 0 0
      simp
    simp[a,b]
    grind
  have ha := Sequence.lim_def hhcon
  rw[hhlim] at ha
  have := Sequence.tendsTo_add ha ha
  rw[hb]
  simpa

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ -2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  obtain ⟨hhcon, hhlim⟩  := Sequence.lim_harmonic
  set a := ((fun (n:ℕ)↦ (n+1:ℝ)⁻¹):Sequence)
  have ha := Sequence.lim_def hhcon
  rw[hhlim] at ha
  have := Sequence.tendsTo_smul (-2) ha
  simp at this
  convert this
  rw[Sequence.smul_coe]
  grind
  


/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (-1)^n/(n+1:ℝ) + 1 / (n+1)^2):Sequence).TendsTo 0 := by
  sorry

/- /-- Example 6.4.15 -/ -/
/- example : ((fun (n:ℕ) ↦ (2:ℝ)^(-(n:ℤ))):Sequence).TendsTo 0 := by -/
/-   sorry -/

/- abbrev Sequence.abs (a:Sequence) : Sequence where -/
/-   m := a.m -/
/-   seq n := |a n| -/
/-   vanish n hn := by simp [a.vanish n hn] -/


/- /-- Corollary 6.4.17 (Zero test for sequences) / Exercise 6.4.7 -/ -/
/- theorem Sequence.tendsTo_zero_iff (a:Sequence) : -/
/-   a.TendsTo (0:ℝ) ↔ a.abs.TendsTo (0:ℝ) := by -/
/-   sorry -/


/- /-- Theorem 6.4.18 (Completeness of the reals) -/ -/
/- theorem Sequence.Cauchy_iff_convergent (a:Sequence) : -/
/-   a.IsCauchy ↔ a.Convergent := by -/
/-   -- This proof is written to follow the structure of the original text. -/
/-   refine ⟨ ?_, IsCauchy.convergent ⟩; intro h -/
/-   have ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ L_minus, hL_minus ⟩ ⟩ := -/
/-     finite_limsup_liminf_of_bounded (bounded_of_cauchy h) -/
/-   use L_minus; simp [tendsTo_iff_eq_limsup_liminf, hL_minus, hL_plus] -/
/-   have hlow : 0 ≤ L_plus - L_minus := by -/
/-     have := a.liminf_le_limsup; simp [hL_minus, hL_plus] at this; grind -/
/-   have hup (ε:ℝ) (hε: ε>0) : L_plus - L_minus ≤ 2*ε := by -/
/-     specialize h ε hε; choose N hN hsteady using h -/
/-     have hN0 : N ≥ (a.from N).m := by grind -/
/-     have hN1 : (a.from N).seq N = a.seq N := by grind -/
/-     have h1 : (a N - ε:ℝ) ≤ (a.from N).inf := by -/
/-       apply inf_ge_lower; grind [Real.dist_eq, abs_le',EReal.coe_le_coe_iff] -/
/-     have h2 : (a.from N).inf ≤ L_minus := by -/
/-       simp_rw [←hL_minus, liminf, lowerseq]; apply le_sSup; simp; use N -/
/-     have h3 : (a.from N).sup ≤ (a N + ε:ℝ) := by -/
/-       apply sup_le_upper; grind [EReal.coe_le_coe_iff, Real.dist_eq, abs_le'] -/
/-     have h4 : L_plus ≤ (a.from N).sup := by -/
/-       simp_rw [←hL_plus, limsup, upperseq]; apply sInf_le; simp; use N -/
/-     replace h1 := h1.trans h2 -/
/-     replace h4 := h4.trans h3 -/
/-     grind [EReal.coe_le_coe_iff] -/
/-   obtain hlow | hlow := le_iff_lt_or_eq.mp hlow -/
/-   . specialize hup ((L_plus - L_minus)/3) ?_ <;> linarith -/
/-   grind -/

/- /-- Exercise 6.4.6 -/ -/
/- theorem Sequence.sup_not_strict_mono : ∃ (a b:ℕ → ℝ), (∀ n, a n < b n) ∧ (a:Sequence).sup ≠ (b:Sequence).sup := by -/
/-   sorry -/

/- /- Exercise 6.4.7 -/ -/
/- def Sequence.tendsTo_real_iff : -/
/-   Decidable (∀ (a:Sequence) (x:ℝ), a.TendsTo x ↔ a.abs.TendsTo x) := by -/
/-   -- The first line of this construction should be `apply isTrue` or `apply isFalse`. -/
/-   sorry -/

/- /-- This definition is needed for Exercises 6.4.8 and 6.4.9. -/ -/
/- abbrev Sequence.ExtendedLimitPoint (a:Sequence) (x:EReal) : Prop := if x = ⊤ then ¬ a.BddAbove else if x = ⊥ then ¬ a.BddBelow else a.LimitPoint x.toReal -/

/- /-- Exercise 6.4.8 -/ -/
/- theorem Sequence.extended_limit_point_of_limsup (a:Sequence) : a.ExtendedLimitPoint a.limsup := by sorry -/

/- /-- Exercise 6.4.8 -/ -/
/- theorem Sequence.extended_limit_point_of_liminf (a:Sequence) : a.ExtendedLimitPoint a.liminf := by sorry -/

/- theorem Sequence.extended_limit_point_le_limsup {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≤ a.limsup := by sorry -/

/- theorem Sequence.extended_limit_point_ge_liminf {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≥ a.liminf := by sorry -/

/- /-- Exercise 6.4.9 -/ -/
/- theorem Sequence.exists_three_limit_points : ∃ a:Sequence, ∀ L:EReal, a.ExtendedLimitPoint L ↔ L = ⊥ ∨ L = 0 ∨ L = ⊤ := by sorry -/

/- /-- Exercise 6.4.10 -/ -/
/- theorem Sequence.limit_points_of_limit_points {a b:Sequence} {c:ℝ} (hab: ∀ n ≥ b.m, a.LimitPoint (b n)) (hbc: b.LimitPoint c) : a.LimitPoint c := by sorry -/


/- end Chapter6 -/
