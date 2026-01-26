import Mathlib.Tactic

/-!
# Analysis I, Section 4.3: Absolute value and exponentiation

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Basic properties of absolute value and exponentiation on the rational numbers (here we use the
  Mathlib rational numbers `ℚ` rather than the Section 4.2 rational numbers).

Note: to avoid notational conflict, we are using the standard Mathlib definitions of absolute
value and exponentiation.  As such, it is possible to solve several of the exercises here rather
easily using the Mathlib API for these operations.  However, the spirit of the exercises is to
solve these instead using the API provided in this section, as well as more basic Mathlib API for
the rational numbers that does not reference either absolute value or exponentiation.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


/--
  This definition needs to be made outside of the Section 4.3 namespace for technical reasons.
-/
def Rat.Close (ε : ℚ) (x y:ℚ) := |x-y| ≤ ε


namespace Section_4_3

/-- Definition 4.3.1 (Absolute value) -/
abbrev abs (x:ℚ) : ℚ := if x > 0 then x else (if x < 0 then -x else 0)

theorem abs_of_pos {x: ℚ} (hx: 0 < x) : abs x = x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_neg {x: ℚ} (hx: x < 0) : abs x = -x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_zero : abs 0 = 0 := rfl

/--
  (Not from textbook) This definition of absolute value agrees with the Mathlib one.
  Henceforth we use the Mathlib absolute value.
-/
theorem abs_eq_abs (x: ℚ) : abs x = |x| := by
  by_cases hx : x > 0
  . simp[abs,hx]
    have ha := _root_.abs_of_pos hx
    symm;assumption
  by_cases heq : x = 0
  . 
    simp[abs,heq]
  have : x < 0 := by grind
  simp[abs,hx,this]
  symm
  exact _root_.abs_of_neg this

abbrev dist (x y : ℚ) := |x - y|

/--
  Definition 4.2 (Distance).
  We avoid the Mathlib notion of distance here because it is real-valued.
-/
theorem dist_eq (x y: ℚ) : dist x y = |x-y| := rfl

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_nonneg (x: ℚ) : |x| ≥ 0 := by
  simp

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_eq_zero_iff (x: ℚ) : |x| = 0 ↔ x = 0 := by simp
/-- Proposition 4.3.3(b) / Exercise 4.3.1 -/
theorem abs_add (x y:ℚ) : |x + y| ≤ |x| + |y| := by
  exact _root_.abs_add x y
  -- fInE 
  /- by_cases hx : x >= 0 <;> -/
  /- by_cases hy : y >= 0 -/
  /- .  -/
  /-   have : x + y >= 0 := by grind -/
  /-   simp[abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg this] -/
  /- .  -/
  /-   simp at hy -/
  /-   by_cases hxy : x + y >= 0 -/
  /-   .  -/
  /-     simp[abs_of_nonneg hx, _root_.abs_of_neg hy, abs_of_nonneg hxy] -/
  /-     grind -/
  /-   .  -/
  /-     simp at hxy -/
  /-     simp[abs_of_nonneg hx, _root_.abs_of_neg hy, _root_.abs_of_neg hxy] -/
  /-     grind -/
  /- . simp at hx -/
  /-   by_cases hxy : x + y >= 0 -/
  /-   .  -/
  /-     simp[_root_.abs_of_neg hx, _root_.abs_of_nonneg hy, abs_of_nonneg hxy] -/
  /-     grind -/
  /-   .  -/
  /-     simp at hxy -/
  /-     simp[_root_.abs_of_neg hx, _root_.abs_of_nonneg hy, _root_.abs_of_neg hxy] -/
  /-     grind -/
  /- simp at hx hy -/
  /- have : x + y < 0 := by grind -/
  /- simp[_root_.abs_of_neg hx, _root_.abs_of_neg hy, _root_.abs_of_neg this] -/

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem abs_le_iff (x y:ℚ) : -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by
  by_cases hx : x >= 0
  map_tacs[simp[abs_of_nonneg hx];(push_neg at hx;simp[_root_.abs_of_neg hx])]
  all_goals
    by_cases hy : y >= 0 <;>
    simp at hy <;>
    grind

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem le_abs (x:ℚ) : -|x| ≤ x ∧ x ≤ |x| := by
  by_cases hx : x >= 0
  map_tacs[simp[abs_of_nonneg hx];(push_neg at hx;simp[_root_.abs_of_neg hx])]
  all_goals
    grind

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_mul (x y:ℚ) : |x * y| = |x| * |y| := by
  by_cases hx : x >= 0
  map_tacs[simp[abs_of_nonneg hx];(push_neg at hx;simp[_root_.abs_of_neg hx])]
  all_goals
    by_cases hy : y >= 0
    map_tacs[simp[abs_of_nonneg hy];(push_neg at hy;simp[_root_.abs_of_neg hy])]
  . apply mul_nonneg hx hy
  . apply mul_nonpos_of_nonneg_of_nonpos hx (by grind)
  . apply mul_nonpos_of_nonpos_of_nonneg (by grind) hy
  . apply mul_nonneg_of_nonpos_of_nonpos
    grind; grind;

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_neg (x:ℚ) : |-x| = |x| := by simp

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_nonneg (x y:ℚ) : dist x y ≥ 0 := by simp

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_eq_zero_iff (x y:ℚ) : dist x y = 0 ↔ x = y := by
  simp;grind

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_symm (x y:ℚ) : dist x y = dist y x := by
  unfold dist
  have : x - y = - (y - x) := by grind
  rw[this]; 
  exact abs_neg (y - x)

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_le (x y z:ℚ) : dist x z ≤ dist x y + dist y z := by
  unfold dist
  set a := x - y;
  set b := y - z;
  rw[show x - z = a + b by simp[a,b]] 
  exact abs_add a b

/--
  Definition 4.3.4 (eps-closeness).  In the text the notion is undefined for ε zero or negative,
  but it is more convenient in Lean to assign a "junk" definition in this case.  But this also
  allows some relaxations of hypotheses in the lemmas that follow.
-/
theorem close_iff (ε x y:ℚ): ε.Close x y ↔ |x - y| ≤ ε := by rfl

/-- Examples 4.3.6 -/
example : (0.1:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by 
  simp[Rat.Close]
  have : (0.99:ℚ) - 1.01 < 0 := by norm_num
  simp[_root_.abs_of_neg this]
  norm_num

/-- Examples 4.3.6 -/
example : ¬ (0.01:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  simp[Rat.Close]
  have : (0.99:ℚ) - 1.01 < 0 := by norm_num
  simp[_root_.abs_of_neg this]
  norm_num

/-- Examples 4.3.6 -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by
  simp[Rat.Close]
  grind

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by simp[Rat.Close]

/-- Proposition 4.3.7(a) / Exercise 4.3.2 -/
theorem eq_if_close (x y:ℚ) : x = y ↔ ∀ ε:ℚ, ε > 0 → ε.Close x y := by
  simp[Rat.Close]
  constructor
  . intro heq ep hep
    simp[heq];grind
  intro a;
  contrapose! a
  use |x - y|/2
  simp; contrapose! a; rwa[sub_eq_zero] at a

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by
  simp[Rat.Close]
  have := dist_symm x y
  unfold dist at this
  rw[this]

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by
      unfold Rat.Close at *
      have := dist_le x y z
      unfold dist at this
      calc  
        _ ≤ |x - y| + |y - z| := by exact this
        _ ≤ _ := by simp[add_le_add hxy hyz]

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x+z) (y+w) := by
      unfold Rat.Close at *
    
      -- |a| <= ε , |b| <= δ ,
      have : x + z - (y + w) = (x - y)+ (z - w) := by ring
      simp[this]
      set a := x - y
      set b := z - w
      calc 
        _ <= |a| + |b| := abs_add _ _
        _ <= _ := add_le_add hxy hzw

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem sub_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x-z) (y-w) := by
      unfold Rat.Close at *
      have : x - z - (y - w) = x - y + (w - z) := by ring
      simp[this]
      have : |z - w| = |w - z| := by
        rw[← neg_sub, abs_neg]
      rw[this] at hzw
      set a := x - y
      set b := w - z
      calc 
        _ <= |a| + |b| := abs_add _ _
        _ <= _ := add_le_add hxy hzw

/-- Proposition 4.3.7(e) / Exercise 4.3.2, slightly strengthened -/
theorem close_mono {ε ε' x y:ℚ} (hxy: ε.Close x y) (hε: ε' ≥  ε) :
    ε'.Close x y := by
      unfold Rat.Close at *
      grind

/-- Proposition 4.3.7(f) / Exercise 4.3.2 -/
lemma close_between_case {ε x y z w:ℚ} (hxy : ε.Close x y) (hxz: ε.Close x z)
 (hbetween: y <= w ∧ w <= z) : ε.Close  x w := by
    unfold Rat.Close at *
    by_cases hw : x < w
    . 
      have hb := hbetween.2
      rw[_root_.abs_of_neg (by rwa[sub_lt_zero])]
      have :x < z := by grind
      rw[_root_.abs_of_neg (by rwa[sub_lt_zero])] at hxz
      grind
    have hb := hbetween.1
    push_neg at hw
    rw[abs_of_nonneg (by simpa)]
    have : y <= x := by grind
    rw[abs_of_nonneg (by simpa)] at hxy
    grind

theorem close_between {ε x y z w:ℚ} (hxy: ε.Close x y) (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by
    obtain hb1 | hb2 := hbetween
    . 
      exact close_between_case hxy hxz hb1
    exact close_between_case hxz hxy hb2


/-- Proposition 4.3.7(g) / Exercise 4.3.2 -/
theorem close_mul_right {ε x y z:ℚ} (hxy: ε.Close x y) :
    (ε*|z|).Close (x * z) (y * z) := by 
  unfold Rat.Close at *
  have : x * z - y * z = (x - y) * z := by ring
  have: |x * z - y * z| = |x - y| * |z| := by
    calc
      _ = |(x-y) * z| := by rw[this]
      _ = |_| * |z| := by exact abs_mul _ z
  simp[this]
  apply mul_le_mul_of_nonneg hxy (by simp) (by simp) (by simp)

/-- Proposition 4.3.7(h) / Exercise 4.3.2 -/
theorem close_mul_mul {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) := by
  -- The proof is written to follow the structure of the original text, though
  -- non-negativity of ε and δ are implied and don't need to be provided as
  -- explicit hypotheses.
  have hε : ε ≥ 0 := le_trans (abs_nonneg _) hxy
  set a := y-x
  have ha : y = x + a := by grind
  have haε: |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by grind
  rw [close_symm, close_iff]
  calc
    _ = |a * z + b * x + a * b| := by grind
    _ ≤ |a * z + b * x| + |a * b| := abs_add _ _
    _ ≤ |a * z| + |b * x| + |a * b| := by grind [abs_add]
    _ = |a| * |z| + |b| * |x| + |a| * |b| := by grind [abs_mul]
    _ ≤ _ := by gcongr

/-- This variant of Proposition 4.3.7(h) was not in the textbook, but can be useful
in some later exercises. -/
theorem close_mul_mul' {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|y|).Close (x * z) (y * w) := by
      set a := x-y
      have ha : x = y + a := by grind
      have haε : |a| <= ε := by rwa[close_iff] at hxy
      set b := w-z
      have hb : w = z + b := by grind
      have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
      have : x * z - y * w = a * z - b * y := by grind
      rw[close_iff,this]
      calc
        _ <= |a*z| + |b*y| := by apply abs_sub
        _ <= |a| * |z| + |b| * |y| := by simp[abs_mul]
        _ <= ε * |z| + δ * |y| := by gcongr

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_zero (x:ℚ) : x^0 = 1 := rfl

example : (0:ℚ)^0 = 1 := pow_zero 0

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_add (x:ℚ) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  induction' m with k hind
  . simp
  rw[pow_succ,← mul_assoc,hind,← pow_succ,add_assoc]

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_mul (x:ℚ) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  induction' m with k hind
  . simp
  rw[pow_succ,hind,pow_add]
  ring

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem mul_pow (x y:ℚ) (n:ℕ) : (x*y)^n = x^n * y^n := by
  induction' n with k hind
  . simp
  rw[pow_succ,hind]
  ring

/-- Proposition 4.3.10(b) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_eq_zero (x:ℚ) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  refine ⟨?_,by intro hx; simp[hx];grind⟩ 
  intro hx
  contrapose! hx with hne
  induction' n with k hind
  . contradiction
  rw[pow_succ,mul_ne_zero_iff]
  simp[hne]

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_nonneg {x:ℚ} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with k hind
  . simp
  simp
  rw[pow_succ,mul_nonneg_iff]
  left;tauto

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_pos {x:ℚ} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  induction' n with k hind
  . simp
  simp
  rw[pow_succ,mul_pos_iff]
  tauto

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with k hind
  . simp
  simp_rw[pow_succ]
  simp
  apply mul_le_mul_of_nonneg hind hxy (pow_nonneg k hy) (by grind)

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  induction' n,hn using Nat.le_induction with k hk hind
  simp[hxy]
  simp_rw[pow_succ]
  have hx : x > 0 := by grind
  have hpy : y ^ k ≥ 0 := by exact pow_nonneg k hy
  have hpx : x ^ k > 0 := by order
  exact Right.mul_lt_mul_of_nonneg hind hxy hpy hy

/-- Proposition 4.3.10(d) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_abs (x:ℚ) (n:ℕ) : |x|^n = |x^n| := by
  induction' n with k hind
  . simp
  simp_rw[pow_succ,hind,abs_mul]

/--
  Definition 4.3.11 (Exponentiation to a negative number).
  Here we use the Mathlib notion of integer exponentiation
-/
theorem zpow_neg (x:ℚ) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

example (x:ℚ): x^(-3:ℤ) = 1/(x^3) := zpow_neg x 3

example (x:ℚ): x^(-3:ℤ) = 1/(x*x*x) := by convert zpow_neg x 3; ring

theorem pow_eq_zpow (x:ℚ) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n

    

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/

theorem zpow_add (x:ℚ) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
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

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_mul (x:ℚ) (n m:ℤ) : (x^n)^m = x^(n*m) := by
  obtain ⟨n, (rfl|rfl)⟩ := Int.eq_nat_or_neg n <;>
  obtain ⟨m, (rfl|rfl)⟩ := Int.eq_nat_or_neg m 
  . have : (n:ℤ)*(m:ℤ) = (n*m:ℕ) := by simp
    simp_rw[this,pow_eq_zpow,pow_mul];
  . have : (n:ℤ)*-(m:ℤ) = -(n*m:ℕ) := by simp
    simp_rw[this,zpow_neg,pow_eq_zpow]
    ring
  . have : -(n:ℤ)*(m:ℤ) = -(n*m:ℕ) := by simp
    simp_rw[this,zpow_neg,pow_eq_zpow]
    ring
  have : -(n:ℤ)*-(m:ℤ) = (n*m:ℕ) := by simp
  simp_rw[this,zpow_neg,pow_eq_zpow]
  simp;ring

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem mul_zpow (x y:ℚ) (n:ℤ) : (x*y)^n = x^n * y^n := by
  obtain ⟨n, (rfl|rfl)⟩ := Int.eq_nat_or_neg n <;>
  simp[mul_pow]
  ring


/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_pos {x:ℚ} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  obtain ⟨n, (rfl|rfl)⟩ := Int.eq_nat_or_neg n
  . rw[pow_eq_zpow]; exact pow_pos n hx
  rw[zpow_neg];simp; exact pow_pos n hx

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_ge_zpow {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  obtain ⟨n, (rfl|rfl)⟩ := Int.eq_nat_or_neg n
  pick_goal 2; omega
  simp only[pow_eq_zpow];
  apply pow_ge_pow <;> grind

theorem zpow_ge_zpow_ofneg {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  obtain ⟨n, (rfl|rfl)⟩ := Int.eq_nat_or_neg n
  omega
  simp
  have := pow_ge_pow x y n hxy (by grind)
  have hxn: x^ n > 0 := pow_pos _ (by grind)
  have hyn: y^n > 0 := pow_pos _ (by grind)
  rw[inv_le_inv₀]
  assumption'



/-- Proposition 4.3.12(c) (Properties of exponentiation, II) / Exercise 4.3.4 -/
lemma pow_inj  {x y:ℚ} {n:ℕ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  obtain (h | h|h) := lt_trichotomy x y
  . 
    have := pow_gt_pow y x n h (by grind) (by omega)
    linarith
  . assumption
  have := pow_gt_pow x y n h (by grind) (by omega)
  linarith
   
theorem zpow_inj {x y:ℚ} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  obtain ⟨m, (hmn | hmn)⟩  := Int.eq_nat_or_neg n
  all_goals
    have hm: m ≠ 0 := by grind
    simp[hmn] at hxy
    apply pow_inj hx hy hm hxy

/-- Proposition 4.3.12(d) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_abs (x:ℚ) (n:ℤ) : |x|^n = |x^n| := by
  obtain ⟨m, (hmn | hmn)⟩  := Int.eq_nat_or_neg n
  <;> simp[hmn]
  rw[pow_abs, abs_inv]
/-- Exercise 4.3.5 -/
theorem two_pow_geq (N:ℕ) : 2^N ≥ N := by
  suffices hlt : 2^N > N from by grind
  induction' N with k hind
  . simp
  rw[gt_iff_lt,lt_iff_exists_pos_add] at hind
  rw[_root_.pow_succ]
  obtain ⟨d,hposd,heq⟩  := hind
  rw[← heq] 
  omega
