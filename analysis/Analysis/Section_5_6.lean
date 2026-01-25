import Mathlib.Tactic
import Analysis.Section_5_5


/-!
# Analysis I, Section 5.6: Real exponentiation, part I

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Exponentiating reals to natural numbers and integers.
- nth roots.
- Raising a real to a rational number.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.6.1 (Exponentiating a real by a natural number). Here we use the
    Mathlib definition coming from `Monoid`. -/

lemma Real.pow_zero (x: Real) : x ^ 0 = 1 := rfl

lemma Real.pow_succ (x: Real) (n:ℕ) : x ^ (n+1) = (x ^ n) * x := rfl

lemma Real.pow_of_coe (q: ℚ) (n:ℕ) : (q:Real) ^ n = (q ^ n:ℚ) := by induction' n with n hn <;> simp

/- The claims below can be handled easily by existing Mathlib API (as `Real` already is known
to be a `Field`), but the spirit of the exercises is to adapt the proofs of
Proposition 4.3.10 that you previously established. -/

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_add (x:Real) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  induction' m with k hind
  . simp
  rw[pow_succ,← mul_assoc,hind,← pow_succ,add_assoc]

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_mul (x:Real) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  induction' m with k hind
  . simp
  rw[pow_succ,hind,pow_add]
  congr

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.mul_pow (x y:Real) (n:ℕ) : (x*y)^n = x^n * y^n := by
  induction' n with k hind
  . simp
  rw[pow_succ,hind,pow_succ,pow_succ]
  ring

/-- Analogue of Proposition 4.3.10(b) -/
theorem Real.pow_eq_zero (x:Real) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  constructor
  . 
    contrapose!
    intro h
    simp only [ne_eq, pow_eq_zero_iff', not_and, Decidable.not_not]
    simp[h]
  . intro h;simp[h];grind

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_nonneg {x:Real} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with k hind; simp
  rw[pow_succ]
  apply mul_nonneg hind hx

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_pos {x:Real} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  induction' n with k hind; simp
  rw[pow_succ]
  apply mul_pos hind hx

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_ge_pow (x y:Real) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with k hind; simp
  simp_rw[pow_succ]
  have hpnonneg := pow_nonneg k hy
  have hx : x ≥ 0 := by order
  have hxp : x ^ k ≥ 0 := by order
  exact mul_le_mul_of_nonneg hind hxy hpnonneg hx

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_gt_pow (x y:Real) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  induction' n, hn using Nat.le_induction with k hk hind
  simp[hxy]
  simp_rw[pow_succ]
  have hx : x > 0 := by grind
  have hpy := pow_nonneg k hy
  have hpx : x ^ k > 0 := by order
  exact Right.mul_lt_mul_of_nonneg hind hxy hpy hy

/-- Analogue of Proposition 4.3.10(d) -/
theorem Real.pow_abs (x:Real) (n:ℕ) : |x|^n = |x^n| := by
  induction' n with k hind
  . simp
  simp_rw[pow_succ,hind,abs_mul]

/-- Definition 5.6.2 (Exponentiating a real by an integer). Here we use the Mathlib definition coming from `DivInvMonoid`. -/
lemma Real.pow_eq_pow (x: Real) (n:ℕ): x ^ (n:ℤ) = x ^ n := by rfl

@[simp]
lemma Real.zpow_zero (x: Real) : x ^ (0:ℤ) = 1 := by rfl

lemma Real.zpow_neg {x:Real} (n:ℕ) : x^(-n:ℤ) = 1 / (x^n) := by simp

/- lemma Real.zpow_succ {x : Real} {n : ℤ} : x ^ (n + 1) = x ^ n * x := by -/
/- /-- Analogue of Proposition 4.3.12(a) -/ -/
theorem Real.zpow_add (x:Real) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  induction' m with k hind k hind
  . simp
  . calc
      _ = x ^ n * x ^ (k:ℤ) * x := by rw[zpow_add_one₀ hx]; ring
      _ = x^(n+k) * x := by rw[hind]
      _ = _ := by rw[← zpow_add_one₀ hx];abel_nf
  calc 
    _ = x ^ n * x ^ (-k:ℤ) * x⁻¹ := by rw[zpow_sub_one₀ hx];ring
    _ = x ^ (n + (-k:ℤ)) * x⁻¹ := by rw[hind]
    _ = _ := by rw[← zpow_sub_one₀ hx];abel_nf
/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_mul (x:Real) (n m:ℤ) : (x^n)^m = x^(n*m) := by
  obtain ⟨n, (rfl|rfl)⟩ := Int.eq_nat_or_neg n <;>
  obtain ⟨m, (rfl|rfl)⟩ := Int.eq_nat_or_neg m 
  . have : (n:ℤ)*(m:ℤ) = (n*m:ℕ) := by simp
    simp_rw[this,pow_eq_pow,pow_mul];
  . have : (n:ℤ)*-(m:ℤ) = -(n*m:ℕ) := by simp
    simp_rw[this,zpow_neg,pow_eq_pow]
    ring
  . have : -(n:ℤ)*(m:ℤ) = -(n*m:ℕ) := by simp
    simp_rw[this,zpow_neg,pow_eq_pow]
    ring
  have : -(n:ℤ)*-(m:ℤ) = (n*m:ℕ) := by simp
  simp_rw[this,zpow_neg,pow_eq_pow]
  simp;ring

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.mul_zpow (x y:Real) (n:ℤ) : (x*y)^n = x^n * y^n := by
  obtain ⟨n, (rfl|rfl)⟩ := Int.eq_nat_or_neg n <;>
  simp[mul_pow]
  ring

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_pos {x:Real} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  obtain ⟨n, (rfl|rfl)⟩ := Int.eq_nat_or_neg n
  . rw[pow_eq_pow]; exact pow_pos n hx
  rw[zpow_neg];simp; exact pow_pos n hx

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_ge_zpow {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  obtain ⟨n, (rfl|rfl)⟩ := Int.eq_nat_or_neg n
  pick_goal 2; omega
  simp only[pow_eq_pow];
  apply pow_ge_pow <;> grind

theorem Real.zpow_ge_zpow_ofneg {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  obtain ⟨n, (rfl|rfl)⟩ := Int.eq_nat_or_neg n
  omega
  simp
  have := pow_ge_pow x y n hxy (by grind)
  have hxn: x^ n > 0 := pow_pos _ (by grind)
  have hyn: y^n > 0 := pow_pos _ (by grind)
  rw[inv_le_inv₀]
  assumption'

/-- Analogue of Proposition 4.3.12(c) -/
theorem Real.zpow_inj {x y:Real} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  obtain ⟨m, (hmn | hmn)⟩  := Int.eq_nat_or_neg n
  all_goals
    have hm: m ≠ 0 := by grind
    simp[hmn] at hxy
    apply (pow_left_inj₀ (by grind ) (by grind) hm).mp hxy

/-- Analogue of Proposition 4.3.12(d) -/
theorem Real.zpow_abs (x:Real) (n:ℤ) : |x|^n = |x^n| := by
  obtain ⟨m, (hmn | hmn)⟩  := Int.eq_nat_or_neg n
  <;> simp[hmn]
  rw[pow_abs, abs_inv]

/-- Definition 5.6.2.  We permit ``junk values'' when `x` is negative or `n` vanishes. -/
noncomputable abbrev Real.root (x:Real) (n:ℕ) : Real := sSup { y:Real | y ≥ 0 ∧ y^n ≤ x }

noncomputable abbrev Real.sqrt (x:Real) := x.root 2

/-- Lemma 5.6.5 (Existence of n^th roots) -/
theorem Real.rootset_nonempty {x:Real} (hx: x ≥ 0) (n:ℕ) (hn: n ≥ 1) : { y:Real | y ≥ 0 ∧ y^n ≤ x }.Nonempty := by
  use 0
  simp; norm_cast
  rw[Nat.zero_pow_of_pos n hn]
  grind

theorem Real.rootset_bddAbove {x:Real} (n:ℕ) (hn: n ≥ 1) : BddAbove { y:Real | y ≥ 0 ∧ y^n ≤ x } := by
  -- This proof is written to follow the structure of the original text.
  rw [_root_.bddAbove_def]
  obtain h | h := le_or_gt x 1
  . use 1; intro y hy; simp at hy
    by_contra! hy'
    replace hy' : 1 < y^n := by
      observe hn: n ≠ 0
      apply one_lt_pow₀ hy' hn
    linarith
  use x; intro y hy; simp at hy
  by_contra! hy'
  replace hy' : x < y^n := by
    observe hn : n ≠ 0
    observe hy1 : 1 < y
    have : y ≤ y^n := by
      refine le_self_pow₀ (by grind) hn
    linarith
  linarith
/-- Lemma 5.6.6 (ab) / Exercise 5.6.1 -/
lemma Real.root_candidate_gt_one {d: Real} (hdz : d > 0)  (hdo : d ≤ 1) {n:ℕ } (hn : n ≥ 1):
    (1 + d / 2^n) ^ n≤ (1 + d) := by
      induction' n,hn using Nat.le_induction with k hk hind generalizing d
      simp;grind
      specialize hind (half_pos hdz)
      simp[show d/2 ≤ 1 by linarith] at hind
      conv_lhs =>
        lhs
        rw[pow_succ,div_mul_eq_div_div_swap]
      rw[pow_succ]
      apply (mul_le_mul_of_nonneg_right hind (by positivity)).trans

      have h_expand : (1 + d / 2) * (1 + d / 2 / 2 ^ k) = 1 + (d / 2 + d / (2 * 2 ^ k) + (d * d) / (4 * 2 ^ k)) := by
        ring_nf
      rw[h_expand]
      simp
      have h2k : (2:Real) ^ k ≥ 2 := by norm_cast; exact Nat.le_pow hk
      have hd2 : d * d ≤ d := by
        field_simp[hdo]
      calc
       _ ≤ d / 2 + d / (2 * 2 ^ k) + d / (4 * 2 ^ k) := by gcongr
       _ = d * ( 1 / 2 + 1 / (2*2^k) + 1 / (4*2^k)):= by grind
       _ ≤ d * (1/2 + 1/(2*2) + 1 /(4*2) ) := by gcongr
       _ ≤ d * 1 := by gcongr; norm_num
       _ ≤ _ := by grind

theorem Real.root_gt_one_of_gt_one {p : Real} (hp : p > 1)  {n : ℕ} (hn : n ≥ 1)
  : ∃ y : Real, y > 1 ∧ y^n ≤ p := by
    wlog hp : p ≤ 2
    . 
      simp at hp
      specialize this (p := 2)
      simp at this
      specialize this hn
      choose y hy hyp using this
      use y
      simp[hy];linarith
    set d := p - 1
    have hpd : p = 1 + d := by linarith
    rw[hpd]
    have hdz : d > 0 := by linarith
    have hdo : d ≤ 1 := by linarith
    use (1 + d / 2^n)
    simp[hdz]
    exact Real.root_candidate_gt_one hdz hdo hn

theorem Real.not_upperBound_of_pow_lt {x y:Real}  (hx : x ≥ 0) (hy : y ≥ 0) {n:ℕ} (hn : n ≥ 1)
  (hlt : y^n < x) : y ∉ upperBounds {y | 0 ≤ y ∧ y ^ n ≤ x} := by
    -- by cases: y=0, then x > 0, and then 
    observe hnz : n ≠ 0
    simp[upperBound_def]
    obtain (hyp | hyz) := lt_or_eq_of_le' hy
    . 
      set p := x / y^n
      have hpowpos : y^n > 0 := pow_pos n hyp
      have hpownz : y^n ≠  0 := by linarith
      have hp : p > 1 := by simp[p];refine (one_lt_div₀ hpowpos).mpr hlt
      choose k hk hky using root_gt_one_of_gt_one hp hn
      use k*y
      split_ands
      . positivity
      . 
        simp[mul_pow]
        calc
        _ ≤ p * y ^n := by gcongr
        _ = _ := by simp[p];exact div_mul_cancel₀ x hpownz
      exact (lt_mul_iff_one_lt_left hyp).mpr hk
    by_cases hx' : x ≤ 1
    .
      use x; 
      refine ⟨hx,pow_le_of_le_one hx hx' hnz,?_⟩ 
      simp[hyz] at hlt
      rw[show (0:Real)^n = 0 by exact (pow_eq_zero 0 n hn).mpr rfl] at hlt
      grind
    use 1
    simp at hx'
    refine ⟨by simp, by simp;grind, by simp[hyz]⟩ 
theorem Real.root_candidate_lt_one {p:Real} (hpz : p > 0) (hpo : p < 1) {n :ℕ} (hn : n ≥ 1):
    ∃c, c = (1 - (p / 2^n))∧ c>0 ∧ c<1 ∧ c ^n ≥ 1 - p:= by
      have h2n : (2:Real)^n ≥ 2 := by norm_cast;exact Nat.le_pow hn
      observe hnz : n ≠ 0
      use (1 - (p / 2^n)) 
      split_ands;rfl
      . simp 
        calc
          _ ≤ (1:Real) / 2 ^ n := by gcongr
          _ ≤ (1:Real) / 2 := by gcongr
          _ < _ := by norm_num
      . simp[hpz]
      induction' n,hn using Nat.le_induction with k hk hind generalizing p
      simp;ring_nf;linarith
      specialize hind (half_pos hpz)
        (by linarith)
        (by norm_cast;exact Nat.le_pow hk)
        (by linarith)
      simp_rw[pow_succ]
      rw[div_mul_eq_div_div_swap]
      rw[ge_iff_le] at ⊢ hind
      have extra_nonneg : (1 - p / 2 / 2^k) ≥ 0 := by 
        simp
        calc
          _ ≤ (1:Real) / 2 / 2 ^ k := by gcongr
          _ ≤ (1:Real) / 2 / 2:= by gcongr; norm_cast; exact Nat.le_pow hk
          _ ≤ _ := by norm_num
      replace hind:= mul_le_mul_of_nonneg_right hind extra_nonneg
      refine le_trans ?_ hind
      have hexpand : (1 - p / 2) * ( 1 - p / 2/ 2^k) = 1 - (p/2 + p / 2 / 2^k - (p * p) / 4 / 2^k) := by ring
      rw[hexpand]
      gcongr
      calc
        _ ≤ p /2 + p / 2 / 2^k := by simp;positivity
        _ ≤ p / 2 + p / 2/ 2 := by gcongr;norm_cast;exact Nat.le_pow hk
        _ ≤ p  := by linarith
theorem Real.not_least_of_pow_gt {x y:Real}  (hx : x ≥ 0) (hy : y ≥ 0) {n:ℕ} (hn : n ≥ 1)
  (hgt : y^n > x) : ∃ M ∈ upperBounds {y | 0 ≤ y ∧ y ^ n ≤ x} , M < y := by
    observe hnz : n ≠ 0 
    have hyp : y > 0 := by
      by_contra! 
      have hyz : y = 0 := by linarith
      rw[hyz, show (0:Real) ^ n = 0 by exact (pow_eq_zero 0 n hn).mpr rfl] at hgt
      linarith
    by_cases hxz : x = 0
    . 
      use 0
      simp[hxz,upperBound_def,hyp]
      intro x' hx' hxn'
      have hx'z : x' = 0 := by
        by_contra!
        have hx'p : x' > 0:= by grind
        have := pow_pos n hx'p 
        linarith
      grind

    replace hx : x > 0 := by grind
    have hyn : y^n >0 := by exact pow_pos n hyp
    set p := 1 - x / y^n 
    have hpz : p > 0 := by simp[p];exact (div_lt_one₀ hyn).mpr hgt
    have hpo : p < 1 := by simp[p];exact div_pos hx hyn
    obtain ⟨c,hcp,hcz,hco,hcnp⟩  := root_candidate_lt_one hpz hpo hn
    have hpd : (1 - p) = x / y^n := by linarith
    rw[hpd] at hcnp
    use y*c
    split_ands
    . simp[upperBound_def]
      intro x' hx'z hx'n
      suffices hpn : x' ^ n ≤ (y*c)^n from by
        rwa[
          pow_le_pow_iff_left₀ 
            (by grind) 
            (by exact (mul_nonneg_iff_of_pos_right hcz).mpr hy) hnz
        ] at hpn
      rw[mul_pow]
      refine le_trans hx'n ?_ 
      rw[← div_le_iff₀' hyn]
      exact hcnp
    exact mul_lt_of_lt_one_right hyp hco

theorem Real.pow_eq_of_eq_root {x y:Real}  (hx : x ≥ 0) (hy : y ≥ 0) {n:ℕ} (hn : n ≥ 1)
  (hyE: IsLUB {y | 0 ≤ y ∧ y ^ n ≤ x} y) : y^n = x := by
    rw[isLUB_def] at hyE
    obtain ⟨hupper,hleast⟩ := hyE 
    by_contra! hne
    obtain (hlt | hgt) := lt_or_gt_of_ne hne
    . have hnup := not_upperBound_of_pow_lt hx hy hn hlt
      contradiction
    choose M hM hMy using not_least_of_pow_gt hx hy hn hgt
    specialize hleast M hM
    linarith

theorem Real.eq_root_iff_pow_eq {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  y = x.root n ↔ y^n = x := by
    simp[root]
    set E := {y | 0 ≤ y ∧ y ^ n ≤ x}
    have hEne : E.Nonempty := rootset_nonempty hx n hn
    have hEba : BddAbove E := rootset_bddAbove n hn
    have hyLUB : IsLUB E (sSup E) := ExtendedReal.sSup_of_bounded hEne hEba
    constructor
    . 
      intro hyE
      rw[← hyE] at hyLUB
      exact pow_eq_of_eq_root hx hy hn hyLUB
    -- mpr:  y^n = x → y is root
    intro hy
    suffices IsLUB E y from LUB_unique this hyLUB
    observe hyz : 0 ≤ y
    rw[isLUB_def]; split_ands
    .
      rw[upperBound_def]
      intro p hp
      simp[E] at hp
      obtain ⟨hpp, hpx⟩ := hp 
      rw[← hy] at hpx
      observe hn : n ≠ 0
      rwa[(pow_le_pow_iff_left₀ hpp hyz hn)] at hpx
    intro M hM
    rw[upperBound_def] at hM
    have : y ∈ E := by
      simp[E];
      refine⟨hyz,(by simp[hy])⟩ 
    specialize hM y this
    assumption


/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_nonneg {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n ≥ 0 := by
  by_contra! h
  rw[root] at h
  set E := {y | 0 ≤ y ∧ y ^ n ≤ x}
  have hEne : E.Nonempty := rootset_nonempty hx n hn
  have hEba : BddAbove E := rootset_bddAbove n hn
  have hyLUB : IsLUB E (sSup E) := ExtendedReal.sSup_of_bounded hEne hEba
  set y := sSup E
  obtain ⟨hup,_⟩ := hyLUB 
  rw[upperBound_def] at hup
  specialize hup 0 
  have h0E : 0 ∈ E := by
    simp[E]
    observe : (0:Real) ^ n = 0
    simp[this,hx]
  specialize hup h0E;linarith


/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_pos {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n > 0 ↔ x > 0 := by
  have := root_nonneg hx hn
  set y := x.root n with hy
  rw [eq_root_iff_pow_eq hx this hn] at hy
  rw[← hy]
  constructor
  intro hy0; exact pow_pos n hy0
  contrapose! 
  intro hy0
  have hy0:  y = 0 := by linarith
  have hx0 : y ^ n = 0 := (pow_eq_zero y n hn).mpr hy0
  grind

theorem Real.pow_of_root {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x.root n)^n = x := by
    have hy0 := root_nonneg hx hn
    set y := x.root n with hyx
    rwa[eq_root_iff_pow_eq hx hy0 hn] at hyx

theorem Real.root_of_pow {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x^n).root n = x := by
    have hy : x^n ≥ 0 := pow_nonneg n hx
    set y:= x^n 
    symm
    rw[eq_root_iff_pow_eq hy hx hn] 

/-- Lemma 5.6.6 (d) / Exercise 5.6.1 -/
theorem Real.root_mono {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : x > y ↔ x.root n > y.root n := by
  set rx := x.root n with hxrx
  set ry := y.root n with hyry
  observe hrx : rx ≥ 0
  observe hry : ry ≥ 0
  rw[eq_root_iff_pow_eq hx hrx hn] at hxrx
  rw[eq_root_iff_pow_eq hy hry hn] at hyry
  rw[← hxrx , ← hyry]
  observe hnz : n ≠ 0
  exact pow_lt_pow_iff_left₀ hry hrx hnz
  

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_gt_one {x : Real} (hx: x > 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k < x.root l := by
  set rk := x.root k with hxrk
  set rl := x.root l with hxrl
  have hxz : x ≥ 0 := by linarith
  have hk1 : k ≥ 1 := by linarith
  observe hrk0 : rk ≥ 0
  observe hrl0 : rl ≥ 0
  observe hrkp : rk^k = x 
  observe hrlp : rl^l = x 
  nth_rw 2 [← hrkp] at hrlp
  have : rk ^ l < rl ^ l := by
    rw[hrlp]
    simp[rk]
    gcongr
    by_contra! hcon
    have : x.root k ^ k ≤ 1 := by exact pow_le_one₀ hrk0 hcon
    linarith
  contrapose! this
  gcongr

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_lt_one {x : Real} (hx0: 0 < x) (hx: x < 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k > x.root l := by
  set rk := x.root k with hxrk
  set rl := x.root l with hxrl
  have hxz : x ≥ 0 := by linarith
  have hk1 : k ≥ 1 := by linarith
  observe hrk0 : rk > 0
  observe hrl0 : rl > 0
  observe hrkp : rk^k = x 
  observe hrlp : rl^l = x 
  have hrk1 : rk < 1 := by
    by_contra!
    have: rk ^ k ≥ 1 := by exact one_le_pow₀ this
    linarith
  have hrl1 : rl < 1 := by
    by_contra!
    have: rl ^ l ≥ 1 := by exact one_le_pow₀ this
    linarith
  nth_rw 2 [← hrkp] at hrlp
  have : x.root k ^ l > x.root l ^ l := by
    rw[hrlp]
    simp
    rwa[pow_lt_pow_iff_right_of_lt_one₀ hrk0 hrk1]
  contrapose! this
  gcongr

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_of_one {k: ℕ} (hk: k ≥ 1): (1:Real).root k = 1 := by
  symm
  rw[eq_root_iff_pow_eq (by simp) (by simp) hk]
  exact one_pow k

/-- Lemma 5.6.6 (f) / Exercise 5.6.1 -/
theorem Real.root_mul {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : (x*y).root n = (x.root n) * (y.root n) := by
  observe hxy : x * y ≥ 0
  observe hrxy : (x*y).root n ≥ 0
  observe hrx : x.root n ≥ 0
  observe hry : y.root n ≥ 0
  set rx := x.root n with hxrx
  set ry := y.root n with hyry
  set rxy := (x*y).root n with hxyrxy
  rw[eq_root_iff_pow_eq hx hrx hn] at hxrx
  rw[eq_root_iff_pow_eq hy hry hn] at hyry
  rw[eq_root_iff_pow_eq hxy hrxy hn] at hxyrxy
  have : rxy ^ n = rx ^ n * ry ^ n := by grind
  rw[← mul_pow] at this
  field_simp at this
  assumption'

/-- Lemma 5.6.6 (g) / Exercise 5.6.1 -/
theorem Real.root_root {x:Real} (hx: x ≥ 0) {n m:ℕ} (hn: n ≥ 1) (hm: m ≥ 1): (x.root n).root m = x.root (n*m) := by
  observe hrn : x.root n ≥ 0
  observe hrnm : (x.root n).root m ≥ 0
  set rn := x.root n with hxrn
  set rnm := rn.root m with hxrnm
  rw[eq_root_iff_pow_eq hrn hrnm hm] at hxrnm
  rw[eq_root_iff_pow_eq hx hrn hn] at hxrn
  have : (rnm ^ m) ^ n = x := by
    grind
  have hnm : n * m ≥ 1 := by exact Right.one_le_mul hn hm
  rw[eq_root_iff_pow_eq hx hrnm hnm]
  rwa[mul_comm,← pow_mul]

theorem Real.root_one {x:Real} (hx: x > 0): x.root 1 = x := by
  have hx0 : x ≥ 0 := by linarith
  have h11 : 1 ≥ 1 := by simp
  observe hrx : x.root 1 ≥ 0
  set rx := x.root 1 with hxrx
  rw[eq_root_iff_pow_eq hx0 hrx h11] at hxrx
  simpa using hxrx


theorem Real.pow_cancel {y z:Real} (hy: y > 0) (hz: z > 0) {n:ℕ} (hn: n ≥ 1)
  (h: y^n = z^n) : y = z := by
    field_simp at h
    assumption

theorem Real.root_inv {x:Real} (hx: x > 0) {n:ℕ} (hn : n ≥ 1) : 
  (x.root n)⁻¹ = (x⁻¹).root n := by
    observe hx0 : x ≥ 0
    suffices h: (x.root n)⁻¹ ^ n  = (x⁻¹).root n ^ n from by
      have hz1: (x.root n) ⁻¹ > 0 := by
        apply Right.inv_pos.mpr
        exact (root_pos hx0 hn).mpr hx
      have hz2 : (x⁻¹).root n  > 0 := by
        refine (root_pos ?_ hn).mpr ?_
        simp[hx0]
        simp[hx]
      apply pow_cancel hz1 hz2 hn h
    simp
    rw[pow_of_root hx0 hn]
    rw[pow_of_root (by simp[hx0]) hn]

example : ¬(∀ (y:Real) (z:Real) (n:ℕ) (_: n ≥ 1) (_: y^n = z^n), y = z) := by
  simp; refine ⟨ (-3), 3, 2, ?_, ?_, ?_ ⟩ <;> norm_num

/-- Definition 5.6.7 -/
noncomputable abbrev Real.ratPow (x:Real) (q:ℚ) : Real := (x.root q.den)^(q.num)

noncomputable instance Real.instRatPow : Pow Real ℚ where
  pow x q := x.ratPow q

theorem Rat.eq_quot (q:ℚ) : ∃ a:ℤ, ∃ b:ℕ, b > 0 ∧ q = a / b := by
  use q.num, q.den; have := q.den_nz
  refine ⟨ by omega, (Rat.num_div_den q).symm ⟩

/-- Lemma 5.6.8 -/
theorem Real.pow_root_eq_pow_root {a a':ℤ} {b b':ℕ} (hb: b > 0) (hb' : b' > 0)
  (hq : (a/b:ℚ) = (a'/b':ℚ)) {x:Real} (hx: x > 0) :
    (x.root b')^(a') = (x.root b)^(a) := by
  -- This proof is written to follow the structure of the original text.
  wlog ha: a > 0 generalizing a b a' b'
  . simp at ha
    obtain ha | ha := le_iff_lt_or_eq.mp ha
    . replace hq : ((-a:ℤ)/b:ℚ) = ((-a':ℤ)/b':ℚ) := by
        push_cast at *; ring_nf at *; simp [hq]
      specialize this hb hb' hq (by linarith)
      simpa [zpow_neg] using this
    have : a' = 0 := by
      symm at hq
      simp[ha] at hq
      grind
    simp_all
  have : a' > 0 := by
    have : (a':ℚ) / b' > 0 := by
      simp[← hq]
      apply div_pos <;>
      norm_cast
    simp[hb'] at this
    tauto
  field_simp at hq
  lift a to ℕ using by order
  lift a' to ℕ using by order
  norm_cast at *
  set y := x.root (a*b')
  have h1 : y = (x.root b').root a := by rw [root_root, mul_comm] <;> linarith
  have h2 : y = (x.root b).root a' := by rw [root_root, mul_comm, ←hq] <;> linarith
  have h3 : y^a = x.root b' := by rw [h1]; apply pow_of_root (root_nonneg _ _) <;> linarith
  have h4 : y^a' = x.root b := by rw [h2]; apply pow_of_root (root_nonneg _ _) <;> linarith
  rw [←h3, pow_mul, mul_comm, ←pow_mul, h4]

theorem Real.ratPow_def {x:Real} (hx: x > 0) (a:ℤ) {b:ℕ} (hb: b > 0) : x^(a/b:ℚ) = (x.root b)^a := by
  set q := (a/b:ℚ)
  convert pow_root_eq_pow_root hb _ _ hx
  . have := q.den_nz; omega
  rw [Rat.num_div_den q]

theorem Real.ratPow_eq_root {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : x^(1/n:ℚ) = x.root n := by
  have : (1 / n:ℚ) = (1:ℤ) / n := by rfl
  rw[this,
    ratPow_def hx _ hn
  ]
  simp

theorem Real.ratPow_eq_pow {x:Real} (hx: x > 0) (n:ℤ) : x^(n:ℚ) = x^n := by
  have : (n:ℚ) = (((n:ℤ) / (1:ℕ) ):ℚ ) := by simp
  rw[this,ratPow_def hx n (by simp),root_one hx]


/-- Lemma 5.6.9(a) / Exercise 5.6.2 -/
theorem Real.ratPow_pos {x:Real} (hx: x > 0) (q:ℚ) : x^q > 0 := by
  choose a b hb hqab using Rat.eq_quot q
  rw[hqab, ratPow_def hx a hb]
  observe hx' : x ≥ 0
  have : x.root b > 0 := by rwa[←  root_pos hx' hb] at hx
  apply zpow_pos a this

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_add {x:Real} (hx: x > 0) (q r:ℚ) : x^(q+r) = x^q * x^r := by
  obtain ⟨qa, qb, hqb, rfl⟩ := Rat.eq_quot q 
  obtain ⟨ra, rb, hrb, rfl⟩ := Rat.eq_quot r 
  have : (qa / qb : ℚ ) + (ra / rb:ℚ ) = (qa * rb + qb * ra : ℤ) / (qb * rb:ℕ) := by
    rw[div_add_div _ _ (by norm_cast;grind) (by norm_cast;grind)]
    simp
  rw[this,
    ratPow_def hx _ (by apply mul_pos hqb hrb)
  ]
  rw[show (qa / qb:ℚ) = ((qa * rb:ℤ):ℚ) / ((qb * rb:ℕ):ℚ ) by field_simp;ring,
    ratPow_def hx _ (by apply mul_pos hqb hrb)
  ] 
  rw[show (ra / rb:ℚ) = ((qb * ra:ℤ):ℚ) / ((qb * rb:ℕ):ℚ ) by field_simp;ring,
    ratPow_def hx _ (by apply mul_pos hqb hrb)
  ] 
  refine Eq.symm (zpow_add (x.root (qb * rb)) (qa * ↑rb) (↑qb * ra) ?_)
  suffices x.root (qb*rb) > 0 from by grind
  apply (root_pos ?_ ?_).mpr hx
  grind
  exact Right.one_le_mul hqb hrb

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_ratPow {x:Real} (hx: x > 0) (q r:ℚ) : (x^q)^r = x^(q*r) := by
  observe hxq : x ^ q > 0
  obtain ⟨qa, qb, hqb, rfl⟩ := Rat.eq_quot q 
  obtain ⟨ra, rb, hrb, rfl⟩ := Rat.eq_quot r 
  rw[ ratPow_def hx _ hqb] at hxq ⊢ 
  rw[ ratPow_def hxq _ hrb]
  rw[ show (qa / qb:ℚ ) * (ra / rb:ℚ) = (qa * ra :ℤ) / (qb * rb:ℕ) by field_simp,
    ratPow_def hx _ (by apply mul_pos hqb hrb)
  ]
  rw[← zpow_mul]
  congr
  observe hx0 : x ≥ 0
  rw[← root_root hx0 hqb hrb]
  observe hrqb : (x.root qb) > 0  
  have hxqr : (x.root qb ^ qa).root rb > 0 := by
    rwa[root_pos (by linarith) hrb ]
  have hqrq : (x.root qb).root rb ^ qa > 0 := by
    apply zpow_pos
    rwa[root_pos (by linarith) (by omega)]
  observe hbne : (rb:ℤ ) ≠ 0 
  apply zpow_inj hxqr hqrq hbne
  rw[zpow_comm];simp
  rw[pow_of_root (by linarith) (by omega)]
  rw[pow_of_root (by linarith) (by omega)]

/-- Lemma 5.6.9(c) / Exercise 5.6.2 -/
theorem Real.ratPow_neg {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = 1 / x^q := by
  obtain ⟨qa, qb, hqb, rfl⟩ := Rat.eq_quot q 
  rw[show -(qa / qb :ℚ) = ((-qa:ℤ) / qb:ℚ) by field_simp]
  rw[ratPow_def hx _ hqb]
  simp
  rw[ratPow_def hx _ hqb]

/-- Lemma 5.6.9(d) / Exercise 5.6.2 -/
theorem Real.zpow_gt_zpow {x y:Real} {n:ℤ} (hxy: x > y) (hy: y > 0) (hn: n > 0): x^n > y^n := by
  obtain ⟨n, (rfl|rfl)⟩ := Int.eq_nat_or_neg n
  pick_goal 2; omega
  apply pow_gt_pow <;> grind
theorem Real.ratPow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (h: q > 0) : x > y ↔ x^q > y^q := by
  obtain ⟨qa, qb, hqb, rfl⟩ := Rat.eq_quot q 
  rw[ratPow_def hx _ hqb]
  rw[ratPow_def hy _ hqb]
  rw[root_mono (by grind) (by grind) hqb]
  observe hx0 : x ≥ 0
  observe hy0 : y ≥ 0
  simp[hqb] at h
  constructor
  . 
    intro hgt
    apply zpow_gt_zpow hgt ?_ h
    exact (root_pos hy0 hqb).mpr hy
  . contrapose!
    simp_rw[← ge_iff_le]
    intro hge
    apply zpow_ge_zpow hge ?_ h
    exact (root_pos hx0 hqb).mpr hx

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_sub {x:Real} (hx: x > 0) (q r:ℚ) : x^(q-r) = x^q / x^r := by
  rw[_root_.sub_eq_add_neg]
  rw[ratPow_add hx]
  rw[ratPow_neg hx]
  ring


theorem Real.one_ratPow (q:ℚ) : (1:Real)^q = 1 := by
  obtain ⟨qa, qb, hqb, rfl⟩ := Rat.eq_quot q 
  rw[ratPow_def (by linarith) _ hqb]
  rw[root_of_one hqb]
  simp

theorem Real.ratPow_cmp_ratPow {x:Real} (hx : x > 0) {q r:ℚ} : x ^ q > x ^ r ↔ x ^ (q - r) > 1 := by
  have hxge0 : x ≥ 0 := by linarith
  have hxr0 := ratPow_pos hx r
  have hxq0 := ratPow_pos hx q
  simp
  rw[← div_lt_one₀ hxq0]
  rw[← ratPow_sub hx]
  rw[← neg_sub]
  rw[ratPow_neg hx]
  simp
  rw[inv_lt_one₀]
  apply ratPow_pos hx
  
theorem Real.ratPow_gt_one_iff_gt_one {x:Real} (hx: x > 1) (q: ℚ): 
  q > 0 ↔ x ^ q > 1 := by
    have hx0 : x > 0 := by linarith
    obtain ⟨qa,qb,hqb,rfl⟩ := Rat.eq_quot q
    rw[ratPow_def hx0 _ hqb] 
    set r := x.root qb
    have hxe0 : x ≥ 0 := by linarith
    have hr0 : r ≥ 0 := by simp[r];exact root_nonneg hxe0 hqb
    have hrx : x = r ^ qb := by
      symm; simp[r]; exact pow_of_root hxe0 hqb
    simp[hqb]
    have hr : r > 1 := by
      by_contra!
      have : x ≤ 1 := by
        rw[hrx];exact pow_le_one₀ hr0 this
      linarith
    rw[show 1 = r ^ (0:ℤ) by rfl]
    symm
    exact zpow_lt_zpow_iff_right₀ hr

lemma Real.inv_ratPow_eq_neg  {x:Real} (hx : x > 0 ) {q:ℚ} : x ^ q = x⁻¹ ^(-q) := by
  field_simp
  have hx' : 1/x > 0 := by positivity
  rw[ratPow_neg hx']
  obtain ⟨qa,qb,hqb,rfl⟩ := Rat.eq_quot q
  rw[ratPow_def hx _ hqb] 
  rw[ratPow_def hx' _ hqb] 
  rw[← one_div_zpow]
  congr
  simp
  rw[root_inv (by simp[hx]) (by simp;assumption)]
  simp

lemma Real.ratPow_eq_one_iff {x:Real} (hx : x > 0) (hx1 : x ≠ 1) {q:ℚ} :q = 0 ↔ x^q = 1 := by
  constructor
  . intro hq
    simp[hq]
    rfl
  intro hq
  obtain ⟨qa,qb,hqa,rfl⟩ := Rat.eq_quot q 
  rw[ratPow_def hx _ hqa] at hq
  simp;left
  observe hx0 : x ≥ 0
  observe : x.root qb ≥ 0
  have hxr1: x.root qb ≠ 1 := by
    contrapose! hx1
    have : x = x.root qb ^ qb := by exact Eq.symm (pow_of_root hx0 hqa)
    rw[this]
    rw[pow_eq_one_iff_of_ne_zero (by omega)] 
    tauto
  rwa[zpow_eq_one_iff_right₀ this hxr1] at hq

theorem Real.ratPow_lt_one_iff_lt_one {x:Real} (hx0: x > 0) (hx: x < 1) (q: ℚ):
  q < 0 ↔ x ^ q > 1  := by
    set x' := x⁻¹ 
    observe hx' : x' > 1
    have hpre := ratPow_gt_one_iff_gt_one hx' 
    specialize hpre (-q)
    rw[inv_ratPow_eq_neg (by positivity)] at hpre
    simpa using hpre

theorem Real.ratPow_mono_of_gt_one {x:Real} (hx: x > 1) {q r:ℚ} : x^q > x^r ↔ q > r := by
  have hxgt0 : x > 0 := by linarith
  rw[ratPow_cmp_ratPow hxgt0]
  have (p:ℚ) : x ^ p > 1 ↔ p > 0 := by
    symm; exact ratPow_gt_one_iff_gt_one hx p
  simp[this]

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_lt_one {x:Real} (hx0: 0 < x) (hx: x < 1) {q r:ℚ} : x^q > x^r ↔ q < r := by
  rw[ratPow_cmp_ratPow hx0]
  have (p:ℚ) : x ^ p > 1 ↔ p < 0 := by
    symm; exact ratPow_lt_one_iff_lt_one hx0 hx p
  simp[this]

/-- Lemma 5.6.9(f) / Exercise 5.6.2 -/
theorem Real.ratPow_mul {x y:Real} (hx: x > 0) (hy: y > 0) (q:ℚ) : (x*y)^q = x^q * y^q := by
  obtain ⟨qa, qb, hqb, rfl⟩ := Rat.eq_quot q 
  rw[ratPow_def (by positivity) _ hqb]
  rw[ratPow_def (by positivity) _ hqb]
  rw[ratPow_def (by positivity) _ hqb]
  rw[← mul_zpow]
  rw[root_mul]
  positivity
  positivity
  omega

/-- Exercise 5.6.3 -/
theorem Real.pow_even (x:Real) {n:ℕ} (hn: Even n) : x^n ≥ 0 := by
  rw[even_iff_exists_two_mul] at hn
  obtain ⟨b,rfl⟩ := hn 
  induction' b with k hind
  . simp
  ring_nf
  apply mul_nonneg
  exact sq_nonneg x
  rw[mul_comm];exact hind

/-- Exercise 5.6.5 -/
theorem Real.max_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  max (x^q) (y^q) = (max x y)^q := by
    wlog hgt : x > y
    . 
      simp at hgt
      obtain (rfl | hgt) := hgt.eq_or_lt
      . simp
      specialize this hy hx hq hgt
      rwa[max_comm,max_comm x]
    have hpgt : x ^ q > y ^ q := by exact (ratPow_mono hx hy hq).mp hgt
    rw[max_eq_left_of_lt hpgt]
    rw[max_eq_left_of_lt hgt]

/-- Exercise 5.6.5 -/
theorem Real.min_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  min (x^q) (y^q) = (min x y)^q := by
    wlog hgt : x > y
    . 
      simp at hgt
      obtain (rfl | hgt) := hgt.eq_or_lt
      . simp
      specialize this hy hx hq hgt
      rwa[min_comm,min_comm x]
    have hpgt : x ^ q > y ^ q := by exact (ratPow_mono hx hy hq).mp hgt
    rw[min_eq_right_of_lt hpgt]
    rw[min_eq_right_of_lt hgt]

-- Final part of Exercise 5.6.5: state and prove versions of the above lemmas covering the case of negative q.

end Chapter5
