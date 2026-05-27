import Mathlib.Tactic
import Analysis.Section_6_1
import Analysis.Section_6_2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Analysis I, Section 6.3: Suprema and infima of sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Suprema and infima of sequences.

-/

namespace Chapter6

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.sup (a:Sequence) : EReal := sSup { x | ∃ n ≥ a.m, x = a n }

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.inf (a:Sequence) : EReal := sInf { x | ∃ n ≥ a.m, x = a n }
lemma example_6_3_3_seq_eq_set {a:Sequence} (ha : a = ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence)) :
    { x | ∃ n ≥ a.m, x = (a n:EReal)} = {1, -1} := by
      simp[ha]
      ext x
      constructor
      . intro hx
        simp at hx
        choose n hn hnx using hx
        lift n to ℕ using hn
        simp at hnx
        simp
        by_cases hn1 : Even (n+1)
        . left 
          rw[hnx]; exact Even.neg_one_pow hn1
        . simp at hn1
          right;rw[hnx];exact Odd.neg_one_pow hn1
      . intro hx
        simp at hx
        obtain (hxp | hxn ) := hx
        . rw[hxp]
          use 1
          simp
        . rw[hxn];use 0;simp

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).sup = 1 := by
  rw[Sequence.sup]
  set a := ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence) with ha
  have heq := example_6_3_3_seq_eq_set ha
  rw[heq]
  simp
  rw[EReal.le_iff]; left
  use -1, 1
  simp

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).inf = -1 := by
  rw[Sequence.inf]
  set a := ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence) with ha
  have heq := example_6_3_3_seq_eq_set ha
  rw[heq]
  simp
  rw[EReal.le_iff]; left
  use -1, 1
  simp

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).sup = 1 := by
  rw[Sequence.sup]
  apply IsLUB.sSup_eq
  constructor
  . rw[mem_upperBounds]
    intro x hx
    simp at hx
    choose n hn hnx using hx
    lift n to ℕ using hn
    simp at hnx
    rw[EReal.le_iff];left
    use (n + 1:ℝ )⁻¹,1 
    simp[hnx]
    have : (n+1:ℝ) ≥ 1 := by norm_num
    exact inv_le_one_of_one_le₀ this
  intro x hx
  rw[mem_upperBounds] at hx
  exact hx 1 (by
    use 0;simp
  )

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).inf = 0 := by
  rw[Sequence.inf,EReal.inf_eq_neg_sup]
  rw[EReal.neg_eq_zero_iff]
  apply IsLUB.sSup_eq
  constructor
  . intro x
    simp
    intro n hn hnx
    lift n to ℕ using hn
    simp at hnx
    have : -x ≥ 0 := by simp[hnx];positivity
    exact EReal.neg_nonneg.mp this
  intro u hu
  rw[mem_upperBounds] at hu
  obtain ⟨u,rfl⟩|rfl|rfl := u.def
  . rw[EReal.le_iff] 
    left; use 0, u; simp
    contrapose! hu
    observe hv : -u > 0
    choose n hnp hnv using Real.exists_nat_pos_inv_lt hv
    observe hnx : -(n:ℝ)⁻¹ > u 
    have hcancel : (n-1)+1 = n := by exact Nat.sub_add_cancel hnp
    use (-(n:ℝ)⁻¹) 
    simp;split_ands
    use (n-1)
    split_ands
    . linarith
    simp[hnp]
    norm_cast
  . simp
  specialize hu (-1) (by simp;use 0;simp)
  simp at hu;contradiction

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).sup = ⊤ := by
  rw[Sequence.sup]
  apply IsLUB.sSup_eq
  constructor
  . intro u hu
    simp
  intro u hu
  rw[mem_upperBounds] at hu
  obtain ⟨u,rfl⟩ | rfl | rfl := u.def 
  . 
    contrapose! hu
    choose x hx using exists_nat_gt u
    set xu := max x 1
    have hxu : u < xu := by 
      simp[xu,hx]
    have hxu1 : xu ≥ 1 := by simp[xu]
    use xu;split_ands
    . use (xu-1)
      simp[hxu1]
    norm_cast
  . simp
  contrapose! hu
  use 1
  split_ands
  . use 0;simp
  exact compareOfLessAndEq_eq_lt.mp rfl

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).inf = 1 := by
  rw[Sequence.inf,EReal.inf_eq_neg_sup,neg_eq_iff_eq_neg]
  apply IsLUB.sSup_eq
  constructor
  . intro x hx
    simp at hx
    choose n hn hnx using hx
    lift n to ℕ using hn
    simp at hnx
    rw[neg_eq_iff_eq_neg] at hnx
    simp[hnx]
    rw[EReal.le_iff];left
    use 1,(n+1)
    simp
  intro u hu
  simp[mem_upperBounds] at hu
  exact hu (-1) 0 (by simp) (by simp)

abbrev Sequence.BddAboveBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≤ M

abbrev Sequence.BddAbove (a:Sequence) : Prop := ∃ M, a.BddAboveBy M

abbrev Sequence.BddBelowBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≥ M

abbrev Sequence.BddBelow (a:Sequence) : Prop := ∃ M, a.BddBelowBy M

theorem Sequence.bounded_iff (a:Sequence) : a.IsBounded ↔ a.BddAbove ∧ a.BddBelow := by
  simp_rw[isBounded_def,boundedBy_def,abs_le]
  constructor
  . rintro ⟨M,hm,ham⟩ 
    split_ands
    . use M; intro n hn
      exact (ham n).2
    use -M; intro n hn
    exact (ham n).1
  rintro ⟨⟨M,hM⟩,⟨N,hN⟩⟩ 
  use max |M| (-N)
  split_ands
  . simp
  intro n
  specialize hM n
  specialize hN n
  by_cases hn : n ≥ a.m
  . simp[hn] at hM hN
    split_ands
    . apply le_trans ?_ hN
      apply neg_le_of_neg_le
      simp
    apply le_trans hM
    simp;left;
    exact le_abs_self M
  simp at hn
  have := a.vanish n hn
  simp[this]
  lemma EReal.finite_of_bounded {s:EReal} {l u : ℝ } (hsl: s ≥ l) (hsu : s ≤ u) : s.IsFinite := by
    obtain ⟨s,rfl⟩ | rfl | rfl := s.def 
    . use s
    . simp at hsu
    . simp at hsl
theorem Sequence.sup_of_bounded {a:Sequence} (h: a.IsBounded) : a.sup.IsFinite := by
  have hsl : a.sup ≥ a a.m := by
    apply le_sSup
    use a.m
  choose M hM hMa using h
  have hsu : a.sup ≤ M := by
    apply sSup_le
    intro b hb
    simp at hb
    choose n hn hnb using hb
    specialize hMa n
    rw[EReal.le_iff];left;use (a n),M
    simp[hnb]
    exact le_of_max_le_left hMa
  exact EReal.finite_of_bounded hsl hsu

theorem Sequence.inf_of_bounded {a:Sequence} (h: a.IsBounded) : a.inf.IsFinite := by
  have hsu : a.inf ≤ a (a.m) := by
    apply sInf_le
    use a.m
  choose M hM hMa using h
  have hsl : -M ≤ a.inf := by
    apply le_sInf
    intro x hx
    simp at hx
    choose n hn hnx using hx
    specialize hMa n
    rw[EReal.le_iff];left
    use -M, (a n)
    simp[hnx]
    exact neg_le_of_abs_le hMa
  exact EReal.finite_of_bounded hsl hsu


/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.le_sup {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≤ a.sup := by
  apply le_sSup
  simp;use n

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.sup_le_upper {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≤ M) : a.sup ≤ M := by
  apply sSup_le
  intro x hx
  simp at hx
  choose n hn hnx using hx
  specialize h n hn
  simpa[hnx]

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.exists_between_lt_sup {a:Sequence} {y:EReal} (h: y < a.sup ) :
    ∃ n ≥ a.m, y < a n ∧ a n ≤ a.sup := by
      obtain ⟨y,rfl⟩ |rfl |rfl := y.def 
      . 
        by_contra! hcon
        have hy : ∀ n ≥ a.m, y ≥ a n := by
          peel hcon with n hn hsec
          rw[← not_imp_not] at hsec
          observe :a.sup ≥ a n
          simpa[this] using hsec
        have hy : y ≥ a.sup := by
          apply sSup_le
          intro x hx 
          simp at hx
          choose n hn hnx using hx
          specialize hy n hn
          rw[EReal.le_iff];left
          use (a n),y
        rw[lt_iff_not_ge] at h
        contradiction
      . simp at h
      use a.m
      simp
      apply le_sup
      simp

/-- Remark 6.3.7 -/
theorem Sequence.ge_inf {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≥ a.inf := by
  apply sInf_le
  simp; use n

/-- Remark 6.3.7 -/
theorem Sequence.inf_ge_lower {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≥ M) : a.inf ≥ M := by
  apply le_sInf
  intro x hx
  simp at hx
  choose n hn hnx using hx
  specialize h n hn
  simpa[hnx]

/-- Remark 6.3.7 -/
theorem Sequence.exists_between_gt_inf {a:Sequence} {y:EReal} (h: y > a.inf ) :
    ∃ n ≥ a.m, y > a n ∧ a n ≥ a.inf := by
      obtain ⟨y,rfl⟩ |rfl |rfl := y.def 
      . 
        by_contra! hcon
        have hy : ∀ n ≥ a.m, y ≤ a n := by
          peel hcon with n hn hsec
          rw[← not_imp_not] at hsec
          observe :a.inf ≤ a n
          simpa[this] using hsec
        have hy : y ≤ a.inf := by
          apply le_sInf
          intro x hx 
          simp at hx
          choose n hn hnx using hx
          specialize hy n hn
          rw[EReal.le_iff];left
          use y, (a n)
        rw[gt_iff_lt,lt_iff_not_ge] at h
        contradiction
      . use a.m
        simp
        apply ge_inf
        simp
      simp at h

abbrev Sequence.IsMonotone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≥ a n
lemma Sequence.monotone_trans {a:Sequence} (ha: a.IsMonotone) {n m:ℤ} (hn: n ≥ a.m) (hm: m ≥ n):
    a m ≥ a n:= by
      observe hma : m ≥ a.m
      induction' m,hm using Int.le_induction with k hk hind
      . simp
      specialize ha k (by linarith)
      specialize hind (by linarith)
      linarith

abbrev Sequence.IsAntitone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≤ a n

lemma Sequence.antitone_trans {a:Sequence} (ha: a.IsAntitone ) {n m:ℤ} (hn: n ≥ a.m) (hm: m ≥ n):
    a m ≤ a n:= by
      observe hma : m ≥ a.m
      induction' m,hm using Int.le_induction with k hk hind
      . simp
      specialize ha k (by linarith)
      specialize hind (by linarith)
      linarith
/-- Proposition 6.3.8 / Exercise 6.3.3 -/
lemma Sequence.boundedBelow_of_monotone {a:Sequence} (hmono: a.IsMonotone) : a.BddBelow := by
  use a a.m
  intro n hn
  apply monotone_trans hmono (by simp) hn

lemma Sequence.tends_to_of_monotone{a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    ∃L, a.TendsTo L ∧ L = a.sup := by
      observe hbonudb : a.BddBelow
      -- hance, a is bounded
      have hbound : a.IsBounded := by
        rw[bounded_iff];tauto
      -- sup a has a real value
      choose u hu using sup_of_bounded hbound
      use u
      refine ⟨?_, hu⟩ 
      intro ε hε 
      have hy : (u-ε:EReal) < a.sup := by
        simp[← hu]; norm_cast
        simp[hε]
      obtain ⟨N,hN,hlo,hup⟩  := exists_between_lt_sup hy
      use N,hN
      intro n hn
      simp at hn
      have hnN := monotone_trans hmono hN hn.2
      simp[hn,dist]
      norm_cast at hlo
      have hnu := le_sup hn.1
      simp[← hu] at hnu
      rw[abs_of_nonpos (by simp[hnu])]
      rw[neg_sub]
      calc
        _ ≤ u - a N := by gcongr
        _ ≤ _ := by linarith 
theorem Sequence.convergent_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    a.Convergent := by
      choose L hL hLs using tends_to_of_monotone hbound hmono 
      use L

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.lim_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    lim a = a.sup := by
      choose L hL hLs using tends_to_of_monotone hbound hmono 
      rw[lim_eq] at hL
      simp[← hLs]
      tauto

lemma Sequence.boundedAbove_of_antitone {a:Sequence} (hmono: a.IsAntitone ) : a.BddAbove := by
  use a a.m
  intro n hn
  apply antitone_trans hmono (by simp) hn
lemma Sequence.tends_to_of_antitone{a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    ∃L, a.TendsTo L ∧ L = a.inf := by
      observe hbonudb : a.BddAbove 
      -- hance, a is bounded
      have hbound : a.IsBounded := by
        rw[bounded_iff];tauto
      -- sup a has a real value
      choose u hu using inf_of_bounded hbound
      use u
      refine ⟨?_, hu⟩ 
      intro ε hε 
      have hy : (u+ε:EReal) > a.inf := by
        simp[← hu]; norm_cast
        simp[hε]
      obtain ⟨N,hN,hlo,hup⟩  := exists_between_gt_inf hy
      use N,hN
      intro n hn
      simp at hn
      have hnN := antitone_trans hmono hN hn.2
      simp[hn,dist]
      norm_cast at hlo
      have hnu := ge_inf hn.1
      simp[← hu] at hnu
      rw[abs_of_nonneg (by simp[hnu])]
      calc
        _ ≤ a N - u:= by gcongr
        _ ≤ _ := by linarith 
theorem Sequence.convergent_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    a.Convergent := by
      choose L hL hLs using tends_to_of_antitone hbound hmono
      use L;

theorem Sequence.lim_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    lim a = a.inf := by
      choose L hL hLs using tends_to_of_antitone hbound hmono
      rw[lim_eq] at hL
      simp[← hLs]
      tauto

theorem Sequence.convergent_iff_bounded_of_monotone {a:Sequence} (ha: a.IsMonotone) :
    a.Convergent ↔ a.IsBounded := by
      rw[bounded_iff]
      constructor
      . intro h
        refine ⟨?_ , boundedBelow_of_monotone ha⟩ 
        have hlim := lim_def h
        use lim a
        by_contra! hcon
        simp at hcon
        choose n hn hseq using hcon
        have hcon : ∀ m ≥ n, a m - lim a ≥ a n - lim a:= by
          intro m hm
          gcongr
          exact monotone_trans ha hn hm
        observe hε : a n - lim a > 0
        set ε := a n - lim a
        specialize hlim (ε/2) (by positivity)
        choose N hN hclose using hlim
        set c := max N n
        specialize hcon c (by simp[c])
        specialize hclose c (by simp[c,hN])
        simp[dist,c,hN] at hclose
        simp[c] at hcon
        rw[abs_of_pos] at hclose
        linarith
        calc
          _ < ε := hε
          _ ≤ _ := hcon
      intro h
      refine convergent_of_monotone h.1 ha

theorem Sequence.bounded_iff_convergent_of_antitone {a:Sequence} (ha: a.IsAntitone) :
    a.Convergent ↔ a.IsBounded := by
      rw[bounded_iff]
      constructor
      . intro h
        refine ⟨ boundedAbove_of_antitone ha,?_⟩ 
        have hlim := lim_def h
        use lim a
        by_contra! hcon
        simp at hcon
        choose n hn hseq using hcon
        have hcon : ∀ m ≥ n,lim a - a m ≥ lim a - a n:= by
          intro m hm
          gcongr
          exact antitone_trans ha hn hm
        observe hε : lim a - a n > 0
        set ε := lim a - a n
        specialize hlim (ε/2) (by positivity)
        choose N hN hclose using hlim
        set c := max N n
        specialize hcon c (by simp[c])
        specialize hclose c (by simp[c,hN])
        simp[dist,c,hN] at hclose
        simp[c] at hcon
        rw[abs_of_neg] at hclose
        linarith
        calc
         _ ≤ -ε := by linarith
         _ < _ := by simp[hε]
      intro h
      refine convergent_of_antitone h.2 ha

/-- Example 6.3.9 -/
noncomputable abbrev Example_6_3_9 (n:ℕ) := ⌊ Real.pi * 10^n ⌋ / (10:ℝ)^n

/-- Example 6.3.9 -/
lemma example_6_3_9_monotone : (Example_6_3_9:Sequence).IsMonotone := by
  intro n hn
  simp at hn
  lift n to ℕ using hn
  have : (0:ℤ) ≤ (n + 1) := by linarith
  simp[Example_6_3_9,this]
  have h_pos : 0 < (10 : ℝ)^n := by positivity
  have h_pos' : 0 < (10 : ℝ)^(n+1) := by positivity
  rw[le_div_iff₀' h_pos',← mul_div_assoc,mul_comm,mul_div_assoc]
  have h_exp : (10 : ℝ)^(n+1) / 10^n = 10 := by 
    simp[pow_succ]
  rw[h_exp]
  norm_cast
  rw[Int.le_floor]
  simp[pow_succ,← mul_assoc]
  apply Int.floor_le (Real.pi * 10 ^ n)

/-- Example 6.3.9 -/
lemma example_6_3_9_bounded_by_4 : (Example_6_3_9:Sequence).BddAboveBy 4 := by
  intro n hn
  simp at hn
  lift n to ℕ using hn
  simp[Example_6_3_9]
  calc 
    _ ≤ Real.pi := by
      rw[div_le_iff₀ (by positivity)]
      exact Int.floor_le (Real.pi * 10 ^ n)
    _ ≤ _ := Real.pi_le_four

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).Convergent := by
  apply Sequence.convergent_of_monotone
  . use 4; exact example_6_3_9_bounded_by_4
  exact example_6_3_9_monotone

/-- Example 6.3.9 -/
example : lim (Example_6_3_9:Sequence) ≤ 4 := by
  have heq : lim (Example_6_3_9:Sequence) = (Example_6_3_9:Sequence).sup:= by
    refine Sequence.lim_of_monotone ?_ ?_
    use 4; exact example_6_3_9_bounded_by_4
    exact example_6_3_9_monotone
  have hle : (Example_6_3_9:Sequence).sup ≤ 4 := by
    apply Sequence.sup_le_upper
    have := example_6_3_9_bounded_by_4
    peel this with n hn h
    simp at hn
    lift n to ℕ using hn
    rw[EReal.le_iff];left
    use (Example_6_3_9:Sequence) n, 4
    simp;split_ands
    rfl
    simpa using h
  rw[← heq] at hle
  replace hle : lim (Example_6_3_9:Sequence) ≤ ((4:ℝ):EReal) := by
    apply le_trans hle
    apply le_of_eq
    rfl
  simpa using hle

/-- Proposition 6.3.1-/
theorem lim_of_exp {x:ℝ} (hpos: 0 < x) (hbound: x < 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ x^n):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ x^n):Sequence)
  have why : a.IsAntitone := by
    intro n hn
    simp[a] at hn
    lift n to ℕ using hn
    simp[a, show (0:ℤ)≤ n+1 by linarith ]
    rw[pow_succ]
    apply mul_le_of_le_one_right
    positivity
    linarith
  have hbound : a.BddBelowBy 0 := by intro n _; positivity
  have hbound' : a.BddBelow := by use 0
  have hconv := a.convergent_of_antitone hbound' why
  set L := lim a
  have : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = x * L := by
    rw [←(a.lim_smul x hconv).2]; congr; ext n; rfl
    simp [a, pow_succ', HSMul.hSMul, SMul.smul]
  have why2 : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = lim ((fun (n:ℕ) ↦ x^n):Sequence) := by
    have haL : a.TendsTo L := by exact Sequence.lim_def hconv
    rw[ Sequence.tendsTo_of_shift 1] at haL
    simp[a] at haL
    have heq : (Sequence.mk' 0 fun n ↦ if 0 ≤ (n:ℤ) + 1 then x ^ ((n:ℤ) + 1).toNat else 0) = ((fun (n:ℕ) ↦ x ^ (n + 1)):Sequence) := by
      simp
      ext n
      by_cases hn: 0 ≤ n
      .
        lift n to ℕ using hn
        simp
        have : ¬ (n:ℤ)+1 < 0 := by linarith
        simp[this]
      simp[hn]
    rw[heq,Sequence.lim_eq] at haL
    rw[haL.2]
  convert_to x * L = 1 * L at why2; simp [a,L]
  have hx : x ≠ 1 := by grind
  simp_all [-one_mul]
/-- Exercise 6.3.4 -/
theorem lim_of_exp' {x:ℝ} (hbound: x > 1) : ¬((fun (n:ℕ) ↦ x^n):Sequence).Convergent := by
  by_contra! hcon
  choose L hL using hcon
  by_cases hLz : L = 0
  . simp[hLz] at hL
    specialize hL x (by linarith)
    choose N hN hNL using hL
    simp at hN; lift N to ℕ using hN
    specialize hNL (N +2) (by simp)
    simp [dist, show 0 ≤ (N:ℤ)+2 by linarith ] at hNL
    rw[abs_of_pos (by positivity)] at hNL
    have : (x^(N+2)) > x := by
      rw[pow_succ]
      field_simp
      apply one_lt_pow₀ hbound
      simp
    rw[ show ((N:ℤ) + 2).toNat = N+2 by rfl] at hNL
    linarith
  push_neg at hLz
  have := Sequence.tendsTo_inv hL hLz
  simp[Sequence.inv_coe] at this
  ring_nf at this
  have hbound' : x⁻¹ <1 := by exact inv_lt_one_of_one_lt₀ hbound
  have hboundz : x⁻¹ >0 := by positivity
  have hpow := lim_of_exp hboundz hbound'
  rw[Sequence.lim_eq] at this
  have : L⁻¹ = 0 := by
    rw[← this.2]
    exact hpow.2
  simp at this
  contradiction

end Chapter6
