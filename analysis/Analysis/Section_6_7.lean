import Mathlib.Tactic
import Analysis.Section_5_epilogue
import Analysis.Section_6_6

/-!
# Analysis I, Section 6.7: Real exponentiation, part II

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Real exponentiation.

Because the Chapter 5 reals have been deprecated in favor of the Mathlib reals, and Mathlib real
exponentiation is defined without first going through rational exponentiation, we will adopt a
somewhat awkward compromise, in that we will initially accept the Mathlib exponentiation operation
(with all its API) when the exponent is a rational, and use this to define a notion of real
exponentiation which in the epilogue to this chapter we will show is identical to the Mathlib operation.
-/

namespace Chapter6

open Sequence Real

/-- Lemma 6.7.1 (Continuity of exponentiation) -/
lemma ratPow_continuous {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).Convergent := by
  -- This proof is rearranged slightly from the original text.
  choose M hM hbound using bounded_of_convergent ⟨ α, hq ⟩
  wlog h : 1 < x
  . 
    simp at h
    obtain rfl| h := eq_or_lt_of_le h
    . simp;exact ⟨ 1, lim_of_const 1 ⟩
    set x' := x⁻¹ 
    have hx' : x' > 0 := by positivity
    have h' : x' > 1 := by simpa[x',one_lt_inv₀ hx]
    specialize this hx' hq M hM hbound h'
    set a' := (fun (n:ℕ) ↦ (x') ^ (q n:ℝ):Sequence)
    have ha : (a'⁻¹) = (fun (n:ℕ) ↦ x ^(q n:ℝ)) := by
      simp[a']
      rw[inv_coe]
      ext n; simp
      simp
      split_ifs with hnn
      . lift n to ℕ using hnn
        simp
        rw[Real.inv_rpow]
        simp
        linarith
      rfl
    rw[← ha] 
    choose L ha' using this
    use L⁻¹ 
    apply tendsTo_inv ha'
    rintro rfl
    specialize ha' (x' ^ (-M) / 2) (by positivity)
    choose Ncon hNcon hNa' using ha'
    simp at hNcon 
    specialize hNa' Ncon (by simpa)
    simp[hNcon,a'] at hNa'
    rw[abs_of_pos (by positivity)] at hNa'
    simp[a'] at hNcon
    lift Ncon to ℕ using hNcon
    simp at hNa'
    have hact : x' ^ (-M) /2 < x' ^ (q Ncon :ℝ) := by
      calc
       _ < x' ^ (-M) := by simp; positivity
       _ ≤ _ := by
         rw[Real.rpow_le_rpow_left_iff h']
         have : |(q Ncon:ℝ)| ≤ M := by
           specialize hbound Ncon
           simpa
         exact neg_le_of_abs_le this
    linarith
  have h': 1 ≤ x := by linarith
  rw [←Cauchy_iff_convergent]
  intro ε hε
  -- Part I
  -- wlog. qn ≥ qm dist of x^(q n) and x^(q m) is x^(q m) * (x ^ (q n - q m) - 1 ) 
  -- which is less than x^M * (x ^ (q n - q m) - 1 )
  -- Part II
  -- Since (x ^ 1/K) tends to to 1, we can find (x ^ 1/K - 1) ≤ ε/(x^M)
  -- Hence x^M * (x^1/K - 1) ≤ ε
  -- Part III
  -- Now we show that we can find the threshold N for all n m ≥ N, 1< (x ^ (qn - qm)) < x^1/K 
  -- first is simple: x > 1
  -- second can be shown by q is cauchy
 
  -- this is Part II of the skeleton: 
  choose K hK hclose using lim_of_roots hx (ε*x^(-M)) (by positivity)
  -- And Part III
  choose N hN hq using IsCauchy.convergent ⟨ α, hq ⟩ (1/(K+1:ℝ)) (by positivity)
  simp [Real.CloseSeq, Real.dist_eq] at hclose hK hN
  lift N to ℕ using hN
  lift K to ℕ using hK
  specialize hclose K (by simp) (by simp); simp at hclose

  use N, by simp
  intro n hn m hm; simp at hn hm
  specialize hq n (by simp [hn]) m (by simp [hm])
  simp [hn, hm, Real.dist_eq] at hq ⊢
  have : 0 ≤ (N:ℤ) := by simp
  lift n to ℕ using by linarith
  lift m to ℕ using by linarith
  simp at hn hm hq ⊢
  obtain hqq | hqq := le_or_gt (q m) (q n)
  . replace : x^(q m:ℝ) ≤ x^(q n:ℝ) := by rw [Real.rpow_le_rpow_left_iff h]; norm_cast
    rw [abs_of_nonneg (by linarith)]
    calc
      _ = x^(q m:ℝ) * (x^(q n - q m:ℝ) - 1) := by ring_nf; rw [←Real.rpow_add (by linarith)]; ring_nf
      _ ≤ x^M * (x^(1/(K+1:ℝ)) - 1) := by
        gcongr <;> try exact h'
        . rw [sub_nonneg]; apply Real.one_le_rpow h'; norm_cast; linarith
        . specialize hbound m; simp_all [abs_le']
        grind [abs_le']
      _ ≤ x^M * (ε * x^(-M)) := by gcongr; grind [abs_le']
      _ = ε := by rw [mul_comm, mul_assoc, ←Real.rpow_add]; simp; linarith
  replace : x^(q n:ℝ) ≤ x^(q m:ℝ) := by rw [Real.rpow_le_rpow_left_iff h]; norm_cast; linarith
  rw [abs_of_nonpos (by linarith)]
  calc
    _ = x^(q n:ℝ) * (x^(q m - q n:ℝ) - 1) := by ring_nf; rw [←Real.rpow_add]; ring_nf; positivity
    _ ≤ x^M * (x^(1/(K+1:ℝ)) - 1) := by
      gcongr <;> try exact h'
      . rw [sub_nonneg]; apply Real.one_le_rpow h'; norm_cast; linarith
      . specialize hbound n; simp_all [abs_le']
      grind [abs_le']
    _ ≤ x^M * (ε * x^(-M)) := by gcongr; simp_all [abs_le']
    _ = ε := by rw [mul_comm, mul_assoc, ←Real.rpow_add]; simp; positivity


lemma ratPow_lim_uniq {x α:ℝ} (hx: x > 0) {q q': ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α)
 (hq': ((fun n ↦ (q' n:ℝ)):Sequence).TendsTo α) :
 lim ((fun n ↦ x^(q n:ℝ)):Sequence) = lim ((fun n ↦ x^(q' n:ℝ)):Sequence) := by
 -- This proof is written to follow the structure of the original text.
  set r := q - q'
  suffices : (fun n ↦ x^(r n:ℝ):Sequence).TendsTo 1
  . rw [←mul_one (lim ((fun n ↦ x^(q' n:ℝ)):Sequence))]
    rw [lim_eq] at this
    convert (lim_mul (b := (fun n ↦ x^(r n:ℝ):Sequence)) (ratPow_continuous hx hq') this.1).2
    . rw [mul_coe]
      rcongr _ n
      rw [←Real.rpow_add (by linarith)]
      simp [r]
    grind
  intro ε hε
  have h1 := lim_of_roots hx
  have h2 := tendsTo_inv h1 (by norm_num)
  choose K1 hK1 h3 using h1 ε hε
  choose K2 hK2 h4 using h2 ε hε
  simp [Inv.inv] at hK1 hK2
  lift K1 to ℕ using hK1; lift K2 to ℕ using hK2
  simp [inv_coe] at h4
  set K := max K1 K2
  have hr := tendsTo_sub hq hq'
  rw [sub_coe] at hr
  choose N hN hr using hr (1 / (K + 1:ℝ)) (by positivity)
  refine ⟨ N, by simp_all, ?_ ⟩
  intro n hn; simp at hn
  specialize h3 K (by simp [K]); specialize h4 K (by simp [K])
  simp [hn, Real.dist_eq, abs_le', K, -Nat.cast_max] at h3 h4 ⊢
  specialize hr n (by simp [hn])
  simp [Real.Close, hn, abs_le'] at hr
  obtain h | rfl | h := lt_trichotomy x 1
  . 
    have h5 : x ^ (r n.toNat:ℝ) ≥ x^(K + 1:ℝ)⁻¹ := by
      simp
      rw[Real.rpow_le_rpow_left_iff_of_base_lt_one hx h]
      simp_all[r]
    have h6 : (x^(K + 1:ℝ)⁻¹)⁻¹ ≥ x ^ (r n.toNat:ℝ) := by
      simp
      rw [←Real.rpow_neg (by linarith)]
      rw[Real.rpow_le_rpow_left_iff_of_base_lt_one hx h]
      simp_all[r]
      linarith
    split_ands <;> linarith
  . simp; linarith
  have h5 : x ^ (r n.toNat:ℝ) ≤ x^(K + 1:ℝ)⁻¹ := by gcongr; linarith; simp_all [r]
  have h6 : (x^(K + 1:ℝ)⁻¹)⁻¹ ≤ x ^ (r n.toNat:ℝ) := by
    rw [←Real.rpow_neg (by linarith)]
    gcongr; linarith
    simp [r]; linarith
  split_ands <;> linarith

theorem Real.eq_lim_of_rat (α:ℝ) : ∃ q: ℕ → ℚ, ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α := by
  choose q hcauchy hLIM using (Chapter5.Real.equivR.symm α).eq_lim; use q
  apply lim_eq_LIM at hcauchy
  simp only [←hLIM, Equiv.apply_symm_apply] at hcauchy
  convert hcauchy; aesop

/-- Definition 6.7.2 (Exponentiation to a real exponent) -/
noncomputable abbrev Real.rpow (x:ℝ) (α:ℝ) :ℝ := lim ((fun n ↦ x^((eq_lim_of_rat α).choose n:ℝ)):Sequence)

lemma Real.rpow_eq_lim_ratPow {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 rpow x α = lim ((fun n ↦ x^(q n:ℝ)):Sequence) :=
   ratPow_lim_uniq hx (eq_lim_of_rat α).choose_spec hq

lemma Real.ratPow_tendsto_rpow {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).TendsTo (rpow x α) := by
  rw [lim_eq]
  exact ⟨ ratPow_continuous hx hq, (rpow_eq_lim_ratPow hx hq).symm ⟩

lemma Real.rpow_of_rat_eq_ratPow {x:ℝ} (hx: x > 0) {q: ℚ} :
  rpow x (q:ℝ) = x^(q:ℝ) := by
  convert rpow_eq_lim_ratPow hx (α := q) (lim_of_const _)
  exact (lim_eq.mp (lim_of_const _)).2.symm

/-- Proposition 6.7.3(a) / Exercise 6.7.1 -/

lemma Sequence.lim_of_nonneg {a: ℕ → ℝ} (ha : ∀ n, a n ≥ 0) (hconv : (a:Sequence).Convergent ):
    lim (a:Sequence) ≥ 0 := by
      have htend := lim_def hconv
      set L := lim (a:Sequence) 
      by_contra! hcon
      specialize htend (-L/2) (by simpa)
      choose N hN hclose using htend
      simp at hN; lift N to ℕ using hN
      specialize hclose N
      simp[dist,abs_le] at hclose
      have hact : a N > - L/2 + L := by
        calc
          _ ≥ (0:ℝ) := by exact ha N
          _ > _ := by ring_nf;apply mul_neg_of_neg_of_pos hcon; simp
      linarith

theorem Real.ratPow_nonneg {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x q ≥ 0 := by
  choose q' hq' using eq_lim_of_rat q
  have htendsto := ratPow_tendsto_rpow hx hq'
  rw[rpow_eq_lim_ratPow hx hq']
  apply Sequence.lim_of_nonneg
  intro n
  positivity
  exact ratPow_continuous hx hq'

/-- Proposition 6.7.3(b) -/
theorem Real.ratPow_add {x:ℝ} (hx: x > 0) (q r:ℝ) : rpow x (q+r) = rpow x q * rpow x r := by
  choose q' hq' using eq_lim_of_rat q
  choose r' hr' using eq_lim_of_rat r
  have hq'r' := tendsTo_add hq' hr'
  rw [add_coe] at hq'r'
  convert_to ((fun n ↦ ((q' n + r' n:ℚ):ℝ)):Sequence).TendsTo (q + r) at hq'r'
  . aesop
  have h1 := ratPow_continuous hx hq'
  have h2 := ratPow_continuous hx hr'
  rw [rpow_eq_lim_ratPow hx hq', rpow_eq_lim_ratPow hx hr', rpow_eq_lim_ratPow hx hq'r', ←(lim_mul h1 h2).2, mul_coe]
  rcongr n; rw [←Real.rpow_add]; simp; linarith

/-- Proposition 6.7.3(c) / Exercise 6.7.1 -/
theorem Real.ratPow_neg {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x (-q) = 1 / rpow x q := by
  sorry

/-- Proposition 6.7.3(d) / Exercise 6.7.1 -/
theorem Real.ratPow_mono {x y:ℝ} (hx: x > 0) (hy: y > 0) {q:ℝ} (h: q > 0) : x > y ↔ rpow x q > rpow y q := by
  sorry

/-- Proposition 6.7.3(e) / Exercise 6.7.1 -/
theorem Real.ratPow_mono_of_gt_one {x:ℝ} (hx: x > 1) {q r:ℝ} : rpow x q > rpow x r ↔ q > r := by
  sorry

/-- Proposition 6.7.3(e) / Exercise 6.7.1 -/
theorem Real.ratPow_mono_of_lt_one {x:ℝ} (hx0: 0 < x) (hx: x < 1) {q r:ℝ} : rpow x q < rpow x r ↔ q < r := by
  sorry

/-- Proposition 6.7.3(b) / Exercise 6.7.1 -/
lemma Sequence.lim_pos_of_bounded_away {a : ℕ → ℝ} (ha: (a:Sequence).Convergent) {M : ℝ} (hM : M > 0) (haM : ∀n, a n ≥ M):
    lim (a:Sequence) > 0 := by
      have hnonneg : lim (a:Sequence) ≥ 0 := by
        apply lim_of_nonneg ?_ ha
        peel haM
        linarith
      apply lt_of_le_of_ne hnonneg
      have htends := lim_def ha
      by_contra! hcon
      rw[← hcon] at htends
      specialize htends (M / 2) (half_pos hM)
      choose N hN hclose using htends; simp at hN; lift N to ℕ using hN
      specialize hclose N; simp[abs_le] at hclose
      have hact := haM N
      linarith

lemma Real.ratPow_pos {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x q > 0 := by
  choose q' hq' using eq_lim_of_rat q
  rw[rpow_eq_lim_ratPow hx hq']
  suffices h : ∃ M > 0, ∀ n,M ≤ x ^ (q' n:ℝ)  from by
    choose M hM hbon using h
    apply lim_pos_of_bounded_away ?_ hM hbon
    exact ratPow_continuous hx hq'
  rw[lim_eq] at hq'
  choose M hM hMbon using bounded_of_convergent hq'.1
  obtain h | rfl | h := lt_trichotomy x 1 
  pick_goal 2
  . use 1; simp
  map_tacs[use (x ^ M); use (x ^ (-M))]
  all_goals
    refine ⟨by positivity, ?_⟩ 
    intro n; 
    specialize hMbon n
    simp[abs_le] at hMbon
    choose h1 h2 using hMbon
  map_tacs[rw[Real.rpow_le_rpow_left_iff_of_base_lt_one hx h]; rw[Real.rpow_le_rpow_left_iff (by linarith)]]
  assumption'

lemma Real.ratPow_inv {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x⁻¹ q = 1 / rpow x q := by
  sorry
lemma Sequence.tendsTo_iff_div_lim_tendsTo_one {a : ℕ → ℝ} {L:ℝ} (hL: L ≠ 0):
    (a:Sequence).TendsTo L ↔ ((fun n ↦ a n / L):Sequence).TendsTo 1:= by
  have hconst : ((fun (n:ℕ) ↦ L):Sequence).TendsTo L := tendsTo_const L 0
  constructor <;> intro h
  . convert tendsTo_div h hconst hL
    . simp[div_coe]
    symm;apply div_self hL
  convert tendsTo_mul h hconst
  . rw[mul_coe]
    congr! with n
    rw[div_mul_cancel₀ _ hL]
  simp
lemma Sequence.tendsTo_iff_lim_sub_tendsTo_zero {a : ℕ → ℝ} {L:ℝ}:
    (a:Sequence).TendsTo L ↔ ((fun n ↦ L - a n):Sequence).TendsTo 0 := by 
  have hconst : ((fun (n:ℕ) ↦ L):Sequence).TendsTo L := tendsTo_const L 0
  constructor <;> intro h <;> 
  convert tendsTo_sub hconst h <;>
  simp[sub_coe]
lemma Sequence.const_mul_tendsTo_zero_of_tendsTo_zero {C:ℝ} {a: ℕ → ℝ} (ha : (a:Sequence).TendsTo 0):
    (((fun (_:ℕ) ↦ C):Sequence) * (a:Sequence)).TendsTo 0 := by
      rw[mul_coe]
      have hsmul := tendsTo_smul C ha
      simpa[smul_coe] using hsmul
lemma Sequence.zpow_tendsTo_one_of_tendsTo_one {x:ℕ → ℝ} (z:ℤ) (hxp : ∀n, x n > 0) (hx: (x:Sequence).TendsTo 1):
    ((fun n ↦ (x n) ^ z):Sequence).TendsTo 1 := by
      induction' z with k hind k hind
      . simp; exact lim_of_const 1
      . 
        norm_cast
        have hmul := tendsTo_mul hind hx
        rw[mul_coe] at hmul
        convert hmul;simp
      have hdiv := tendsTo_div hind hx (by simp)
      rw[div_coe] at hdiv
      convert hdiv using 3 with n
      . 
        rw[div_eq_mul_inv,← zpow_sub_one₀]
        specialize hxp n;linarith
      simp

lemma Sequence.root_tendsTo_one_of_tendsTo_one {x:ℕ → ℝ} (r:ℕ) (hr: r > 0) (hxp : ∀n, x n > 0) (hx: (x:Sequence).TendsTo 1):
    ((fun n ↦ (x n) ^ (r:ℝ)⁻¹ ):Sequence).TendsTo 1 := by
      peel hx with ε hε N hN n hn hclose
      simp at hN hn
      lift N to ℕ using hN
      lift n to ℕ using hn.1
      simp at hn
      simp[hn,dist,abs_le] at hclose ⊢
      obtain ⟨hlower,hupper⟩ := hclose
      specialize hxp n
      obtain hlt | heq | hgt := lt_trichotomy (x n) 1
      . 
        have hone : x n ^ (r:ℝ)⁻¹ < 1 := by 
          rw[Real.rpow_inv_lt_iff_of_pos]
          <;>simp_all;linarith
        have hlw : x n ≤ x n ^ (r:ℝ)⁻¹ := by
          rw[Real.le_rpow_inv_iff_of_pos]
          simp;apply pow_le_of_le_one
          all_goals
            try simp
            linarith
        split_ands<;>linarith
      . simp[heq];linarith
      have hone : 1 < x n ^ (r:ℝ)⁻¹  := by 
        rw[Real.lt_rpow_inv_iff_of_pos]
        <;>simp_all;linarith
      have hlw : x n ^ (r:ℝ)⁻¹ ≤ x n := by
        rw[Real.rpow_inv_le_iff_of_pos]
        simp; apply le_self_pow₀
        all_goals
          try simp
          linarith
      split_ands<;>linarith



lemma Sequence.ratPow_tendsTo_one_of_tendsTo_one {x:ℕ → ℝ} (r:ℚ) (hxp : ∀n, x n > 0) (hx: (x:Sequence).TendsTo 1):
    ((fun n ↦ (x n)^ (r:ℝ)):Sequence).TendsTo 1 := by
      rw[← r.num_div_den]
      set num := r.num
      have hden := r.den_pos
      set den := r.den

      suffices hbr : ((fun n ↦ (x n ^ num) ^ (den:ℝ)⁻¹):Sequence).TendsTo 1 from by
        convert hbr using 3 with n
        push_cast;rw[div_eq_mul_inv,Real.rpow_mul (by specialize hxp n; linarith)]
        norm_cast
      apply root_tendsTo_one_of_tendsTo_one _ hden
      . intro n ;apply zpow_pos (hxp n)
      apply zpow_tendsTo_one_of_tendsTo_one _ hxp hx


lemma Real.tendsTo_ratPow {x:ℝ} (r:ℚ) {x': ℕ → ℝ} (hx': (x':Sequence).TendsTo x) (hx: x > 0) (hx'pos: ∀ n, x' n > 0):
    ((fun n ↦ (x' n) ^ (r:ℝ)):Sequence).TendsTo (x ^ (r:ℝ)) := by
      -- x ^ r - (x' n) ^ r -> 0 => tendsTo_iff_lim_sub_tendsTo_zero
      rw[tendsTo_iff_lim_sub_tendsTo_zero]
      -- x ^ r * (1 - (x' n / x) ^ r) -> 0 => calc
      suffices hcalc : ((fun n ↦  x ^ (r:ℝ) * (1 - (x' n / x) ^ (r:ℝ))):Sequence).TendsTo 0 from by
        convert hcalc using 3 with n
        ring_nf; congr
        rw[Real.mul_rpow (by specialize hx'pos n;linarith) (by simp;linarith)]
        rw[mul_comm,Real.inv_rpow (by linarith),mul_assoc]
        field_simp
      -- (1 - (x' n / x) ^ r) -> 0 => const_mul_tendsTo_zero_of_tendsTo_zero
      rw[← mul_coe]
      apply const_mul_tendsTo_zero_of_tendsTo_zero
      -- (x' n / x) ^ r -> 1 => [<- tendsTo_iff_lim_sub_tendsTo_zero]
      rw[← tendsTo_iff_lim_sub_tendsTo_zero]
      -- (x' n / x) -> 1 => ratPow_tendsTo_one_of_tendsTo_one
      apply ratPow_tendsTo_one_of_tendsTo_one
      . peel hx'pos with n hp
        apply div_pos hp hx
      -- x' n  -> x => tendsTo_iff_div_lim_tendsTo_one
      rwa[←tendsTo_iff_div_lim_tendsTo_one (by linarith)]



lemma Real.rpow_ratPow {x q:ℝ} {r:ℚ} (hx : x > 0): (rpow x q) ^ (r:ℝ) = rpow x (q * r) := by
  observe hxq : rpow x q > 0 
  choose q' hq' using eq_lim_of_rat q
  have htend := ratPow_tendsto_rpow hx hq'
  have hpow := tendsTo_ratPow r htend hxq (by intro n; positivity)
  by_contra! hcon
  apply tendsTo_unique _ hcon ⟨hpow, ?_⟩ 

  have hsmul := tendsTo_smul r hq'
  rw[smul_coe,mul_comm] at hsmul
  norm_cast at hsmul
  convert  ratPow_tendsto_rpow hx hsmul using 3 with n
  rw[← Real.rpow_mul (by linarith),mul_comm]
  norm_cast

lemma Sequence.rat_envelop {x': ℕ → ℝ} (hx' : (x':Sequence).TendsTo 0):
    ∃ r' : ℕ → ℚ,  ((fun n ↦ (r' n:ℝ)):Sequence).TendsTo  0 ∧ ∀ n, r' n ≥ |x' n|:= by
      have hdouble {x:ℝ} (hx : x > 0) : x < 2 * x := by exact lt_two_mul_self hx
      have hspec {x:ℝ} (hx:x > 0):= (exists_rat_btwn (hdouble hx)).choose_spec
      use fun n ↦ if hx:|x' n| > 0 then (exists_rat_btwn (hdouble hx)).choose else 0
      split_ands
      . intro ε hε 
        specialize hx' (ε /2 ) (half_pos hε)
        choose N hN hClose using hx'
        simp at hN
        lift N to ℕ using hN
        use N; simp
        intro n hn 
        simp at hn
        lift n to ℕ using (by linarith)
        simp at hn
        specialize hClose n (by simpa)
        simp[dist,hn] at hClose ⊢
        split_ifs with hx
        . simp;linarith
        . specialize hspec (show |x' n| > 0 by simpa)
          rw[abs_of_pos (by linarith)] 
          linarith
      intro n
      simp
      split_ifs with hx
      simpa
      specialize hspec (show |x' n| > 0 by simpa)
      linarith
          


lemma Real.rpow_of_one {r:ℝ} : rpow 1 r = 1 := by 
  choose r' hr' using eq_lim_of_rat r
  have := ratPow_tendsto_rpow (show 1 > 0 by simp) hr'
  by_contra! hcon
  apply tendsTo_unique _ hcon ⟨this, ?_⟩ 
  simp
  exact lim_of_const 1
lemma Real.rpow_zero {x:ℝ} (hx: x > 0): rpow x 0 = 1 := by
  have : rpow x 0 = rpow x (0:ℚ) := by
    simp
  rw[this,rpow_of_rat_eq_ratPow hx]
  simp
  
lemma Real.rpow_tendsTo_one_of_tendsTo_zero {x:ℝ} (hx : x > 0) {r' : ℕ → ℝ} (hr : (r':Sequence).TendsTo 0):
    ((fun n ↦ rpow x (r' n)):Sequence).TendsTo 1 := by
      wlog hx1 : x > 1
      . simp at hx1
        obtain rfl | hx1 := hx1.eq_or_lt
        . simp[rpow_of_one]
          exact lim_of_const 1
        observe hx' : x⁻¹ > 0
        have hx'1 : 1 < x⁻¹ := by rwa[one_lt_inv₀ hx]
        set r'' : ℕ → ℝ := fun n ↦ - (r' n)
        have hr'' : (r'' : Sequence).TendsTo 0 := by
          convert tendsTo_neg hr
          simp[r'']; ext n;rfl
          simp;split_ifs;all_goals
            linarith
        specialize this hx' hr'' hx'1
        convert this using 3 with n
        unfold r''
        set r := r' n
        rw[ratPow_neg hx' r,ratPow_inv hx]
        simp
      choose q hq hqb using rat_envelop hr
      simp[abs_le] at hqb
      have hupp (n): rpow x (q n:ℝ) ≥ rpow x (r' n) := by
        specialize hqb n
        obtain heq| hlt := (hqb.2).eq_or_lt
        . rw[heq]
        apply le_of_lt
        simpa[ratPow_mono_of_gt_one hx1]
      have hlow (n) : rpow x (- q n:ℝ) ≤ rpow x (r' n) := by
        specialize hqb n
        obtain heq| hlt := (hqb.1).eq_or_lt
        . rw[heq]
        apply le_of_lt
        simpa[ratPow_mono_of_gt_one hx1]
      have huppt := ratPow_tendsto_rpow hx hq
      have hq' := tendsTo_neg hq
      simp[neg_coe] at hq'
      norm_cast at hq' hlow
      have hlowt := ratPow_tendsto_rpow hx hq'
      simp[rpow_zero hx] at huppt hlowt
      norm_cast at hlowt
      set upp :=((fun n ↦ rpow x (q n)):Sequence)
      set low :=((fun n ↦ rpow x (-q n:ℝ)):Sequence)
      set mid :=(( fun n ↦ rpow x (r' n)):Sequence)
      have hmeq : mid.m = low.m ∧ upp.m = low.m := by
        split_ands
        . simp[mid,low]
        simp[upp,low]
      apply lim_of_between hmeq
      intro n hn
      simp at hn
      lift n to ℕ using hn
      specialize hupp n
      specialize hlow n
      split_ands
      . simp[low,mid]
        norm_cast
      . simpa[mid,upp]
      simp[low]
      norm_cast
      simp only[rpow_of_rat_eq_ratPow hx]
      assumption
      simp[upp]
      simp only[rpow_of_rat_eq_ratPow hx]
      assumption
          

/- lemma Real.tendsTo_rpow {x α:ℝ} (hx: x > 0) {q: ℕ → ℝ} -/
/-  (hq: (q:Sequence).TendsTo α) : -/
/-     ((fun n ↦ rpow x (q n)):Sequence).TendsTo (rpow x α) := by -/
/-       observe hxa : rpow x α > 0  -/
/-       have hconst : ((fun (n:ℕ) ↦ rpow x α):Sequence).TendsTo (rpow x α) := lim_of_const _ -/
/-       suffices hdif : ((fun n ↦ rpow x (q n - α)):Sequence).TendsTo 1 from by -/
/-         have hmul := tendsTo_mul hdif hconst -/
/-         simp only[mul_coe, one_mul] at hmul -/
/-         convert hmul using 3 with n -/
/-         rw[← ratPow_add hx] -/
/-         simp -/
/-       apply rpow_tendsTo_one_of_tendsTo_zero hx -/
/-       rw[tendsTo_iff_lim_sub_tendsTo_zero] at hq -/
/-       convert tendsTo_neg hq -/
/-       . ext n; rfl -/
/-         simp; split_ifs with hn <;> simp -/
/-       simp -/



/- lemma Real.lim_rpow {x α:ℝ} (hx: x > 0) {q: ℕ → ℝ} -/
/-  (hq: (q:Sequence).TendsTo α) : -/
/-     lim ((fun n ↦ rpow x (q n)):Sequence) = rpow x α := by -/
/-       have htend := tendsTo_rpow hx hq -/
/-       rw[lim_eq] at htend;tauto -/

/- theorem Real.ratPow_ratPow {x:ℝ} (hx: x > 0) (q r:ℝ) : rpow (rpow x q) r = rpow x (q*r) := by -/
/-   -- unfold lhs -/
/-   observe hxq : rpow x q > 0  -/
/-   choose r' hr' using eq_lim_of_rat r -/
/-   rw[rpow_eq_lim_ratPow hxq hr'] -/
/-   simp only [rpow_ratPow hx] -/
/-   apply lim_rpow hx -/
/-   have hsmul := tendsTo_smul q hr' -/
/-   rwa[smul_coe] at hsmul -/


/- /-- Proposition 6.7.3(f) / Exercise 6.7.1 -/ -/
/- theorem Real.ratPow_mul {x y:ℝ} (hx: x > 0) (hy: y > 0) (q:ℝ) : rpow (x*y) q = rpow x q * rpow y q := by -/
/-   sorry -/

end Chapter6
