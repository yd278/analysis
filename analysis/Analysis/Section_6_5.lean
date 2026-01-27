import Mathlib.Tactic
import Analysis.Section_6_4

/-!
# Analysis I, Section 6.5: Some standard limits

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some standard limits, including limits of sequences of the form 1/n^α, x^n, and x^(1/n).

-/

namespace Chapter6

theorem Sequence.lim_of_const (c:ℝ) :  ((fun (_:ℕ) ↦ c):Sequence).TendsTo c := by
  apply tendsTo_const

instance Sequence.inst_pow: Pow Sequence ℕ where
  pow a k := {
    m := a.m
    seq n := if n ≥ a.m then a n ^ k else 0
    vanish := by grind
  }

@[simp]
lemma Sequence.pow_eval {a:Sequence} {k: ℕ} {n: ℤ} (hn : n ≥ a.m): (a ^ k) n = a n ^ k := by
  rw [HPow.hPow, instHPow, Pow.pow, inst_pow]
  grind

@[simp]
lemma Sequence.pow_one (a:Sequence) : a^1 = a := by
  ext n; rfl; simp only [HPow.hPow, Pow.pow]; split_ifs with h; simp; simp [a.vanish n (by grind)]

lemma Sequence.pow_succ (a:Sequence) (k:ℕ): a^(k+1) = a^k * a := by
  ext x
  . symm; exact Int.min_self a.m
  . simp only [mul_eval]
    by_cases h: x ≥ a.m
    · simp [pow_eval h]
      rfl
    · rw [a.vanish x (by grind), mul_zero]
      exact vanish _ _ (by simp at h; exact h)

/-- Corollary 6.5.1 -/
theorem Sequence.lim_of_power_decay {k:ℕ} :
    ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence).TendsTo 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence)
  have ha : a.BddBelow := by use 0; intro n _; simp [a]; positivity
  have ha' : a.IsAntitone := by
    intro n hn; observe hn' : 0 ≤ n+1; simp [a,hn,hn']
    rw [inv_le_inv₀, Real.rpow_le_rpow_iff] <;> try positivity
    simp
  apply convergent_of_antitone ha at ha'
  have hpow (n:ℕ): (a^(n+1)).Convergent ∧ lim (a^(n+1)) = (lim a)^(n+1) := by
    induction' n with n ih
    . simp [ha', -dite_pow]
    rw [pow_succ]; convert lim_mul ih.1 ha'; grind
  have hlim : (lim a)^(k+1) = 0 := by
    rw [←(hpow k).2]; convert lim_harmonic.2; ext; rfl
    simp only [HPow.hPow, Pow.pow, a]; split_ifs with h <;> simp
    rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
    convert Real.rpow_one _; field_simp
  simp [lim_eq, ha', pow_eq_zero hlim]

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric {x:ℝ} (hx: |x| < 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 0 := by
  wlog hxp : x > 0 
  . 
    intro ε hε
    have hx': |-x| < 1 := by simp[hx]
    specialize this hx' 
    by_cases hx0 : x = 0
    . simp[hx0]; use 1;simp
      intro n hn
      simp at hn
      lift n to ℕ using by linarith
      simp[hn]
      rw[zero_pow (by omega)];linarith
    have hxn : -x > 0 := by grind
    specialize this hxn ε hε 
    choose N hN hNx using this
    use N
    simp[hN]
    peel hNx with n hn hclose 
    simp at hn
    lift n to ℕ using hn.1
    simpa[dist,hn] using hclose
  have hx1 : x < 1 := by rwa[abs_of_pos hxp] at hx
  have ans := lim_of_exp hxp hx1
  have := lim_def ans.1
  rwa[ans.2] at this


/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric' {x:ℝ} (hx: x = 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 1 := by
  intro ε hε
  use 0;simp
  intro n hn
  simp at hn
  simp[hn,hx]
  linarith

/-- Lemma 6.5.2 / Exercise 6.5.2 -/

lemma Sequence.IsCauchy.abs {a:ℕ → ℝ } (ha: (a:Sequence).IsCauchy):
  (a : Sequence).abs.IsCauchy := by
    peel ha with ε hε N hN n hn m hm ha
    simp at hN
    lift N to ℕ using hN
    simp at hn hm
    lift n to ℕ using by grind
    lift m to ℕ using by grind
    simp at hn hm
    simp[hn,hm,dist] at ha ⊢ 
    have :|(|a n| - |a m|)| ≤ |a n - a m| := by
      exact abs_abs_sub_abs_le (a n) (a m)
    grind

theorem Sequence.lim_of_geometric'' {x:ℝ} (hx: x = -1 ∨ |x| > 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Divergent := by
      obtain rfl | hx := hx
      . simp
        intro r
        use 0.5;norm_num
        intro N hN
        lift N to ℕ using hN
        by_contra! hdist
        have case1 := hdist N
        simp at case1
        have case2 := hdist (N+1)
        simp [show 0 ≤ (N:ℤ)+1 by linarith]at case2
        by_cases hNp : Even N
        . have hNop : Odd (N+1) := by exact Even.add_one hNp
          simp[hNp] at case1
          simp[hNop,dist_comm] at case2
          have tri := dist_triangle 1 r (-1)
          rw[show dist (1:ℝ) (-1) = 2 by simp[dist];norm_num]  at tri
          linarith
        . have hNop : Even (N+1) := by exact Nat.even_add_one.mpr hNp
          simp at hNp
          simp[hNp] at case1
          simp[hNop,dist_comm] at case2
          have tri := dist_triangle (-1) r 1
          rw[show dist (-1:ℝ) (1) = 2 by simp[dist];norm_num]  at tri
          linarith
      wlog hx1 : x > 1
      . 
        set f := fun (n:ℕ) ↦ x ^ n
        have hxa: |(|x|)| > 1 := by simpa
        specialize this hxa hx
        set fa := fun (n:ℕ) ↦ |x| ^ n
        have hff : (f:Sequence).abs = fa := by
          simp[f,fa];ext n
          split_ifs <;> simp
        rw[divergent_def,← Cauchy_iff_convergent] at this ⊢ 
        contrapose! this
        rw[← hff]
        exact IsCauchy.abs this
        
      exact lim_of_exp' hx1

/-- Lemma 6.5.3 / Exercise 6.5.3 -/
lemma Sequence.unbounded_above_of_divergent_monotone {a:Sequence} (had : a.Divergent) (ham : a.IsMonotone):
    ¬ a.BddAbove := by
      contrapose! had
      rw[divergent_def];push_neg
      exact convergent_of_monotone had ham
lemma Sequence.root_eventually_lt_of_gt_one {x ε:ℝ} (hx : x > 1) (hε:ε >0):
  ∃N : ℕ,∀ n ≥ N, x ^ (1/(n+1:ℝ)) ≤ 1+ε := by 
  suffices h : ∃ N:ℕ, x ≤ (1+ε) ^ (N+1:ℝ) from by
    peel h with N hle
    intro n hn;simp
    rw[Real.rpow_inv_le_iff_of_pos]
    . apply le_trans hle
      gcongr; linarith
    all_goals
      linarith
  set f := ((fun n:ℕ ↦ (1+ε) ^ n):Sequence)
  have hub : ¬ f.BddAbove := by
    apply unbounded_above_of_divergent_monotone
    apply lim_of_geometric''; right; rw[abs_of_pos (by positivity)]; linarith
    intro n hn
    simp at hn
    simp[f,hn, show 0 ≤ n+1 by linarith]
    lift n to ℕ using hn
    simp
    gcongr<;>linarith
  simp at hub;specialize hub x
  choose N hN hNb using hub
  simp[f] at hN
  lift N to ℕ using hN; use N
  apply le_of_lt
  apply lt_trans hNb
  simp[f]
  rw[ ← Nat.cast_add_one, Real.rpow_natCast]
  gcongr <;> linarith

lemma Sequence.root_eventually_gt_of_le_one {x ε:ℝ} (hx0 : x > 0) (hx : x ≤  1) (hε1 : ε < 1) (hε:ε >0):
  ∃N : ℕ,∀ n ≥ N, x ^ (1/(n+1:ℝ)) ≥  1-ε := by 
  suffices h : ∃ (n:ℕ), (1-ε) ^ (n+1) ≤ x from by
    peel h with N hN
    intro n hn
    
    rw[one_div,ge_iff_le,Real.le_rpow_inv_iff_of_pos (by linarith) (by linarith) (by linarith)]
    apply le_trans ?_ hN
    rw[ ← Nat.cast_add_one, Real.rpow_natCast]
    apply pow_le_pow_of_le_one
    <;> linarith
  set f := ((fun n:ℕ↦ (1-ε)^n):Sequence)
  have : f.TendsTo 0 := by
    apply lim_of_geometric
    rw[abs_of_pos] <;> linarith
  specialize this x hx0
  choose n hn hnc using this
  simp[f] at hn; lift n to ℕ using hn
  specialize hnc n (by simp[f])
  simp[dist,f] at hnc
  rw[abs_of_pos (by linarith)] at hnc
  use n; apply le_trans ?_ hnc
  rw[_root_.pow_succ]
  apply mul_le_of_le_one_right
  . apply pow_nonneg; linarith
  linarith

theorem Sequence.lim_of_roots {x:ℝ} (hx: x > 0) :
    ((fun (n:ℕ) ↦ x^(1/(n+1:ℝ))):Sequence).TendsTo 1 := by
      intro ε hε
      by_cases hx1 : x > 1
      . 
        choose N helt using root_eventually_lt_of_gt_one hx1 hε
        use N; simp
        intro n hn; simp at hn; lift n to ℕ using by linarith
        simp at hn
        specialize helt n hn
        field_simp [hn,dist,abs_le]
        split_ands
        . have hxp : x ^ (1/ (n+1:ℝ))  > 1 := by
            simp
            rw[Real.lt_rpow_inv_iff_of_pos]
            <;> simp_all
            <;> linarith
          linarith
        linarith
      simp at hx1
      wlog hε1 : ε<1
      . 
        simp at hε1
        set ε' := (1/2:ℝ)
        have hε' : ε' > 0 := by norm_num
        have hε'1 : ε' < 1 := by norm_num
        specialize this hx ε' hε' hx1  hε'1 
        peel this with N hN n hn hclose
        apply Real.Close.mono hclose
        simp[ε'];linarith
      choose N hegt using root_eventually_gt_of_le_one hx hx1 hε1 hε
      use N; simp
      intro n hn; simp at hn; lift n to ℕ using by linarith
      simp at hn
      specialize hegt n hn
      field_simp [hn,dist,abs_le]
      split_ands
      . linarith
      . have hxp : x ^ (1/ (n+1:ℝ))  ≤ 1 := by
          simp
          rw[Real.rpow_inv_le_iff_of_pos]
          <;> simp_all
          <;> linarith
        linarith

/-- Exercise 6.5.1 -/
lemma Sequence.tendsTo_zero_pow {a :Sequence}  {k:ℕ} (hk: k > 0)(ha : a.TendsTo 0):
    (a^k).TendsTo (0) := by
      intro ε hε
      wlog hε1 : ε < 1
      . simp at hε1
        set ε':= (1/2:ℝ)
        specialize this hk ha (1/2) (by simp) (by norm_num)
        peel this with N hN n hn hclose
        apply Real.Close.mono hclose
        linarith
      specialize ha ε hε
      peel ha with N hN n hn hclose
      simp at hN hn
      have hmn : a.m  = (a^k).m := by rfl
      simp[hn,hmn] at hclose ⊢ 
      apply le_trans ?_ hclose
      apply pow_le_of_le_one
      simp
      linarith
      omega
      

theorem Sequence.lim_of_rat_power_decay {q:ℚ} (hq: q > 0) :
    (fun (n:ℕ) ↦ 1/((n+1:ℝ)^(q:ℝ)):Sequence).TendsTo 0 := by
      rw[← q.num_div_den]
      simp[← Rat.num_pos] at hq
      set p := q.num
      set k := q.den - 1
      have : k ≥ 0 := by simp[k]
      have hk : q.den = k + 1 := by
        simp[k]
        rw[Nat.sub_add_cancel]
        have := q.den_pos;omega
      suffices h : (((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence) ^ (p.toNat)).TendsTo 0 from by
        convert h
        ext n; simp;rfl
        simp[hk]
        split_ifs with hn
        . lift n to ℕ using hn
          simp
          rw[← Real.rpow_mul_natCast]
          rw[ show ((p.toNat):ℝ) = p by norm_cast; simp;linarith]
          field_simp;linarith
        symm
        apply Sequence.vanish
        simp at hn
        convert hn
      apply tendsTo_zero_pow
      . simp[hq]
      exact lim_of_power_decay

/-- Exercise 6.5.1 -/
theorem Sequence.lim_of_rat_power_growth {q:ℚ} (hq: q > 0) :
    (fun (n:ℕ) ↦ ((n+1:ℝ)^(q:ℝ)):Sequence).Divergent := by
      by_contra! hcon 
      choose n hn using hcon
      have h1 := lim_of_rat_power_decay hq
      have hn0 : n ≠ 0 := by
        by_contra! hn0
        simp[hn0] at hn
        specialize hn (1/2) (by simp)
        choose N hN hclose using hn
        specialize hclose N (by simp[hN])
        simp[dist,hN] at hclose
        simp at hN
        lift N to ℕ using hN
        rw[abs_of_pos (by positivity)] at hclose
        simp at hclose
        have : (N+1:ℝ)^(q:ℝ)  ≥ 1 := by
          apply Real.one_le_rpow
          simp
          simp;linarith
        linarith
      have := tendsTo_inv hn hn0
      simp[Sequence.inv_coe] at this
      simp at h1
      have hcont : n⁻¹ ≠ 0 := by simpa
      apply Sequence.tendsTo_unique _ hcont ⟨this, h1⟩

end Chapter6
