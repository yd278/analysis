import Mathlib.Tactic
import Analysis.Section_4_3

/-!
# Analysis I, Section 5.1: Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a sequence of rationals
- Notions of `ε`-steadiness, eventual `ε`-steadiness, and Cauchy sequences

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/--
  Definition 5.1.1 (Sequence). To avoid some technicalities involving dependent types, we extend
  sequences by zero to the left of the starting point `n₀`.
-/
@[ext]
structure Sequence where
  n₀ : ℤ
  seq : ℤ → ℚ
  vanish : ∀ n < n₀, seq n = 0

/-- Sequences can be thought of as functions from ℤ to ℚ. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℚ) where
  coe := fun a ↦ a.seq

/--
Functions from ℕ to ℚ can be thought of as sequences starting from 0; `ofNatFun` performs this conversion.

The `coe` attribute allows the delaborator to print `Sequence.ofNatFun f` as `↑f`, which is more concise; you may safely remove this if you prefer the more explicit notation.
-/
@[coe]
def Sequence.ofNatFun (a : ℕ → ℚ) : Sequence where
    n₀ := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by grind

-- Notice how the delaborator prints this as `↑fun x ↦ ↑x ^ 2 : Sequence`.
#check Sequence.ofNatFun (· ^ 2)

/--
If `a : ℕ → ℚ` is used in a context where a `Sequence` is expected, automatically coerce `a` to `Sequence.ofNatFun a` (which will be pretty-printed as `↑a`)
-/
instance : Coe (ℕ → ℚ) Sequence where
  coe := Sequence.ofNatFun

abbrev Sequence.mk' (n₀:ℤ) (a: { n // n ≥ n₀ } → ℚ) : Sequence where
  n₀ := n₀
  seq n := if h : n ≥ n₀ then a ⟨n, h⟩ else 0
  vanish := by grind

lemma Sequence.eval_mk {n n₀:ℤ} (a: { n // n ≥ n₀ } → ℚ) (h: n ≥ n₀) :
    (Sequence.mk' n₀ a) n = a ⟨ n, h ⟩ := by grind

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℚ) : (a:Sequence) n = a n := by norm_cast

@[simp]
lemma Sequence.eval_coe_at_int (n:ℤ) (a: ℕ → ℚ) : (a:Sequence) n = if n ≥ 0 then a n.toNat else 0 := by norm_cast

@[simp]
lemma Sequence.n0_coe (a: ℕ → ℚ) : (a:Sequence).n₀ = 0 := by norm_cast

/-- Example 5.1.2 -/
abbrev Sequence.squares : Sequence := ((fun n:ℕ ↦ (n^2:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.squares n = n^2 := Sequence.eval_coe _ _

/-- Example 5.1.2 -/
abbrev Sequence.three : Sequence := ((fun (_:ℕ) ↦ (3:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.three n = 3 := Sequence.eval_coe _ (fun (_:ℕ) ↦ (3:ℚ))

/-- Example 5.1.2 -/
abbrev Sequence.squares_from_three : Sequence := mk' 3 (·^2)

/-- Example 5.1.2 -/
example (n:ℤ) (hn: n ≥ 3) : Sequence.squares_from_three n = n^2 := Sequence.eval_mk _ hn

-- need to temporarily leave the `Chapter5` namespace to introduce the following notation

end Chapter5

/--
A slight generalization of Definition 5.1.3 - definition of ε-steadiness for a sequence with an
arbitrary starting point n₀
-/
abbrev Rat.Steady (ε: ℚ) (a: Chapter5.Sequence) : Prop :=
  ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m)

lemma Rat.steady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m) := by rfl

namespace Chapter5

/--
Definition 5.1.3 - definition of ε-steadiness for a sequence starting at 0
-/
lemma Rat.Steady.coe (ε : ℚ) (a:ℕ → ℚ) :
    ε.Steady a ↔ ∀ n m : ℕ, ε.Close (a n) (a m) := by
  constructor
  · intro h n m; specialize h n ?_ m ?_ <;> simp_all
  intro h n hn m hm
  lift n to ℕ using hn
  lift m to ℕ using hm
  simp [h n m]

/--
Not in textbook: the sequence 3, 3 ... is 1-steady
Intended as a demonstration of `Rat.Steady.coe`
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  simp [Rat.Steady.coe, Rat.Close]

/--
Compare: if you need to work with `Rat.Steady` on the coercion directly, there will be side
conditions `hn : n ≥ 0` and `hm : m ≥ 0` that you will need to deal with.
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  intro n _ m _; simp_all [Sequence.n0_coe, Sequence.eval_coe_at_int, Rat.Close]

/--
Example 5.1.5: The sequence `1, 0, 1, 0, ...` is 1-steady.
-/
example : (1:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m
  -- Split into four cases based on whether n and m are even or odd
  -- In each case, we know the exact value of a n and a m
  split_ifs <;> simp [Rat.Close]

/--
Example 5.1.5: The sequence `1, 0, 1, 0, ...` is not ½-steady.
-/
example : ¬ (0.5:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h; specialize h 0 1; simp [Rat.Close] at h
  norm_num at h

/--
Example 5.1.5: The sequence 0.1, 0.01, 0.001, ... is 0.1-steady.
-/
example : (0.1:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m; unfold Rat.Close
  wlog h : m ≤ n
  · specialize this m n (by linarith); rwa [abs_sub_comm]
  rw [abs_sub_comm, abs_of_nonneg]
  . rw [show (0.1:ℚ) = (10:ℚ)^(-1:ℤ) - 0 by norm_num]
    gcongr <;> try grind
    positivity
  linarith [show (10:ℚ) ^ (-(n:ℤ)-1) ≤ (10:ℚ) ^ (-(m:ℤ)-1) by gcongr; norm_num]

/--
Example 5.1.5: The sequence 0.1, 0.01, 0.001, ... is not 0.01-steady. Left as an exercise.
-/
example : ¬(0.01:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw[Rat.Steady.coe]
  by_contra h
  specialize h 0 1; simp[Rat.Close] at h
  norm_num at h
  simp[abs_of_pos] at h
  grind

/-- Example 5.1.5: The sequence 1, 2, 4, 8, ... is not ε-steady for any ε. Left as an exercise.
-/
lemma two_pow_gt (n : ℕ) : n + 1 <  2 ^ (n + 2)  := by
  induction' n with k hind
  . simp
  rw[add_assoc k 1 2,add_comm 1 2,← add_assoc,pow_succ,mul_two]
  linarith


example (ε:ℚ) : ¬ ε.Steady ((fun n:ℕ ↦ (2 ^ (n):ℚ) ):Sequence) := by
  simp;use 0;simp[Rat.Close]
  set c := ⌈ε⌉  
  set p := (|c| + 2)
  have : p >= 0 := by
    simp[p]
    calc
      _ <= |c| := by simp
      _ <= _ := by simp
  use p;
  simp[this]
  rw[abs_of_nonpos]
  pick_goal 2; rw[sub_nonpos]
  induction' p.toNat with k hind
  . simp
  ring_nf;linarith
  rw[neg_sub]
  have : p.toNat  = |c|.toNat + 2 := by
    simp[p]
    apply Int.toNat_add_nat
    simp
  simp[this]
  suffices h : |c|.toNat  < (2:ℚ) ^ (|c|.toNat  + 2) - 1 from by
    calc
      _ <= (c:ℚ)  := by exact Int.le_ceil ε
      _ <= |c| := by norm_cast; exact le_abs_self c
      _ <= |c|.toNat := by norm_cast; exact Int.self_le_toNat |c|
      _ < _ := by assumption
  have := two_pow_gt (|c|.toNat)
  apply lt_sub_left_of_add_lt
  rw[add_comm];norm_cast

/-- Example 5.1.5:The sequence 2, 2, 2, ... is ε-steady for any ε > 0.
-/
example (ε:ℚ) (hε: ε>0) : ε.Steady ((fun _:ℕ ↦ (2:ℚ) ):Sequence) := by
  rw [Rat.Steady.coe]; simp [Rat.Close]; positivity

/--
The sequence 10, 0, 0, ... is 10-steady.
-/
example : (10:ℚ).Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]; intro n m
  -- Split into 4 cases based on whether n and m are 0 or not
  split_ifs <;> simp [Rat.Close]

/--
The sequence 10, 0, 0, ... is not ε-steady for any smaller value of ε.
-/
example (ε:ℚ) (hε:ε<10):  ¬ ε.Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  contrapose! hε; rw [Rat.Steady.coe] at hε; specialize hε 0 1; simpa [Rat.Close] using hε

/--
  a.from n₁ starts `a:Sequence` from `n₁`.  It is intended for use when `n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence `a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (n₁:ℤ) : Sequence :=
  mk' (max a.n₀ n₁) (fun n ↦ a (n:ℤ))

lemma Sequence.from_eval (a:Sequence) {n₁ n:ℤ} (hn: n ≥ n₁) :
  (a.from n₁) n = a n := by simp [hn]; intro h; exact (a.vanish _ h).symm

end Chapter5

/-- Definition 5.1.6 (Eventually ε-steady) -/
abbrev Rat.EventuallySteady (ε: ℚ) (a: Chapter5.Sequence) : Prop := ∃ N ≥ a.n₀, ε.Steady (a.from N)

lemma Rat.eventuallySteady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.EventuallySteady a ↔ ∃ N ≥ a.n₀, ε.Steady (a.from N) := by rfl

namespace Chapter5

/--
Example 5.1.7: The sequence 1, 1/2, 1/3, ... is not 0.1-steady
-/
lemma Sequence.ex_5_1_7_a : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) := by
  intro h; rw [Rat.Steady.coe] at h; specialize h 0 2; simp [Rat.Close] at h; norm_num at h
  rw [abs_of_nonneg] at h <;> grind

/--
Example 5.1.7: The sequence a_10, a_11, a_12, ... is 0.1-steady
-/
lemma Sequence.ex_5_1_7_b : (0.1:ℚ).Steady (((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence).from 10) := by
  rw [Rat.Steady]
  intro n hn m hm; simp at hn hm
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  simp_all [Rat.Close]
  wlog h : m ≤ n
  · specialize this m n _ _ _ <;> try omega
    rwa [abs_sub_comm] at this
  rw [abs_sub_comm]
  have : ((n:ℚ) + 1)⁻¹ ≤ ((m:ℚ) + 1)⁻¹ := by gcongr
  rw [abs_of_nonneg (by linarith), show (0.1:ℚ) = (10:ℚ)⁻¹ - 0 by norm_num]
  gcongr
  · norm_cast; omega
  positivity

/--
Example 5.1.7: The sequence 1, 1/2, 1/3, ... is eventually 0.1-steady
-/
lemma Sequence.ex_5_1_7_c : (0.1:ℚ).EventuallySteady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) :=
  ⟨10, by simp, ex_5_1_7_b⟩

/--
Example 5.1.7

The sequence 10, 0, 0, ... is eventually ε-steady for every ε > 0. Left as an exercise.
-/
lemma Sequence.ex_5_1_7_d {ε:ℚ} (hε:ε>0) :
    ε.EventuallySteady ((fun n:ℕ ↦ if n=0 then (10:ℚ) else (0:ℚ) ):Sequence) := by
      use 1; simp
      intro m hm n hn;
      simp[Rat.Close]
      simp_all
      have: ¬m<=0:=by grind
      simp[this]
      have: ¬n<=0:=by grind
      simp[this]
      grind

abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℚ), ε.EventuallySteady a

lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℚ), ε.EventuallySteady a := by rfl

/-- Definition of Cauchy sequences, for a sequence starting at 0 -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℚ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (a j) (a k) ≤ ε := by
  constructor <;> intro h ε hε
  · choose N hN h' using h ε hε
    lift N to ℕ using hN; use N
    intro j _ k _; simp [Rat.steady_def] at h'; specialize h' j _ k _ <;> try omega
    simp_all; exact h'
  choose N h' using h ε hε
  refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := ?_
  have mpos : 0 ≤ m := ?_
  lift n to ℕ using npos
  lift m to ℕ using mpos
  simp [hn, hm]; specialize h' n _ m _
  all_goals try omega
  norm_cast

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℚ) :
    (mk' n₀ a).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  constructor <;> intro h ε hε <;> choose N hN h' using h ε hε
  · refine ⟨ N, hN, ?_ ⟩; dsimp at hN; intro j _ k _
    simp only [Rat.Steady, show max n₀ N = N by omega] at h'
    specialize h' j _ k _ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
    exact h'
  refine ⟨ max n₀ N, by simp, ?_ ⟩
  intro n _ m _; simp_all
  apply h' n _ m <;> omega

noncomputable def Sequence.sqrt_two : Sequence := (fun n:ℕ ↦ ((⌊ (Real.sqrt 2)*10^n ⌋ / 10^n):ℚ))

/--
  Example 5.1.10. (This requires extensive familiarity with Mathlib's API for the real numbers.)
-/

lemma partial_fract (x n m b: ℝ) (hb: b > 0) (hn: n >= b⁻¹ ) (hm : m >= b⁻¹ )  :  |(⌊x * n⌋ / n) - (⌊x * m⌋ / m)| ≤ b := by
  wlog hnm : n >= m
  . specialize this x m n b hb hm hn (by grind)
    rwa[abs_sub_comm]
  have : b⁻¹ > 0 := by exact Right.inv_pos.mpr hb
  rw[div_sub_div _ _ (by grind ) (by grind)]
  have hnf := Int.self_sub_fract (x * n) 
  have hmf := Int.self_sub_fract (x * m) 
  have hhnf := Int.fract_lt_one (x * n)
  have hhmf := Int.fract_lt_one (x * m)
  have hnfp := Int.fract_nonneg (x * n)
  have hmfp := Int.fract_nonneg (x * m)
  rw[← hnf, ← hmf]
  set p := Int.fract (x * n)
  set q := Int.fract (x * m)
  have: ((x * ↑n - p) * ↑m - ↑n * (x * ↑m - q)) / (↑n * ↑m) = (q / m - p / n) := by grind
  simp[this]
  rw[abs_le]
  split_ands
  .
    apply neg_le_of_neg_le
    rw[neg_sub]
    have hp : q / m >= 0 := by
      apply div_nonneg hmfp (by grind)
    have hq : p / n < b := by
      rw[div_lt_iff₀' (by grind)]
      calc
        _ < (1:ℝ) := hhnf
        _ = b⁻¹ * b := by rw[inv_mul_cancel₀ (by grind)] 
        _ ≤  _ := by exact (mul_le_mul_iff_of_pos_right hb).mpr hn
    grind
  . 
    have hp : p / n >= 0 := by
      apply div_nonneg hnfp (by grind)
    have hq : q / m < b := by
      rw[div_lt_iff₀' (by grind)]
      calc
        _ < (1:ℝ) := hhmf
        _ = b⁻¹ * b := by rw[inv_mul_cancel₀ (by grind)] 
        _ ≤  _ := by exact (mul_le_mul_iff_of_pos_right hb).mpr hm
    grind

theorem Sequence.ex_5_1_10_a : (1:ℚ).Steady sqrt_two := by
  intro n hn m hm
  simp_all[sqrt_two,Rat.Close]
  wlog hnm : n >= m
  . 
    specialize this m n hm hn (by grind)
    rwa[abs_sub_comm]
  lift n to ℕ using hn
  lift m to ℕ using hm
  simp_all
  rify
  have := partial_fract (Real.sqrt 2) (10^n) (10^m) 1  (by simp) (by simp; norm_cast; exact Nat.one_le_pow' n 9) (by simp; norm_cast; exact Nat.one_le_pow' m 9)
  assumption

/--
  Example 5.1.10. (This requires extensive familiarity with Mathlib's API for the real numbers.)
-/

theorem Sequence.ex_5_1_10_b : (0.1:ℚ).Steady (sqrt_two.from 1) := by 
  intro n hn m hm
  simp [sqrt_two] at hn hm
  unfold Rat.Close
  rw[(sqrt_two).from_eval hn,(sqrt_two).from_eval hm]
  simp[sqrt_two, show 0 <= n by grind,show 0 <= m by grind]
  lift n to ℕ using (by grind)
  lift m to ℕ using (by grind)
  simp at hn hm ⊢ 
  have hlb (n:ℕ) (hn : n>= 1) : (10:ℝ) ^ n >= (0.1⁻¹) := by
    set n' := n - 1
    have : n = n' + 1 := by
      simp[n']
      exact (Nat.sub_eq_iff_eq_add hn).mp rfl
    simp[this]
    induction' n' with k hind
    . 
      simp
      calc 
        _ = (1 / 0.1:ℝ) := by exact inv_eq_one_div 0.1
        _ = (1 / (1 / 10)) := by norm_num
        _ <= _ := by simp
    rw[pow_succ]
    calc
      _ <= (10:ℝ) ^ (k+1) := by exact hind
      _ <= _ := by simp

  have := partial_fract (Real.sqrt 2) (10 ^ n) (10 ^ m) 0.1 (by norm_num) (hlb n hn) (hlb m hm)
  rify
  assumption

theorem Sequence.ex_5_1_10_c : (0.1:ℚ).EventuallySteady sqrt_two := by
  use 1; simp[sqrt_two]
  exact ex_5_1_10_b

/-- Proposition 5.1.11. The harmonic sequence, defined as a₁ = 1, a₂ = 1/2, ... is a Cauchy sequence. -/
theorem Sequence.IsCauchy.harmonic : (mk' 1 (fun n ↦ (1:ℚ)/n)).IsCauchy := by
  rw [IsCauchy.mk]
  intro ε hε
  -- We go by reverse from the book - first choose N such that N > 1/ε
  obtain ⟨ N, hN : N > 1/ε ⟩ := exists_nat_gt (1 / ε)
  have hN' : N > 0 := by
    observe : (1/ε) > 0
    observe : (N:ℚ) > 0
    norm_cast at this
  refine ⟨ N, by norm_cast, ?_ ⟩
  intro j hj k hk
  lift j to ℕ using (by linarith)
  lift k to ℕ using (by linarith)
  norm_cast at hj hk
  simp [show j ≥ 1 by linarith, show k ≥ 1 by linarith]

  have hdist : Section_4_3.dist ((1:ℚ)/j) ((1:ℚ)/k) ≤ (1:ℚ)/N := by
    rw [Section_4_3.dist_eq, abs_le']
    /-
    We establish the following bounds:
    - 1/j ∈ [0, 1/N]
    - 1/k ∈ [0, 1/N]
    These imply that the distance between 1/j and 1/k is at most 1/N - when they are as "far apart" as possible.
    -/
    have : 1/j ≤ (1:ℚ)/N := by gcongr
    observe : (0:ℚ) ≤ 1/j
    have : 1/k ≤ (1:ℚ)/N := by gcongr
    observe : (0:ℚ) ≤ 1/k
    grind
  simp at *; apply hdist.trans
  rw [inv_le_comm₀] <;> try positivity
  order

abbrev BoundedBy {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : Prop := ∀ i, |a i| ≤ M

/--
  Definition 5.1.12 (bounded sequences). Here we start sequences from 0 rather than 1 to align
  better with Mathlib conventions.
-/
lemma boundedBy_def {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : BoundedBy a M ↔ ∀ i, |a i| ≤ M := by rfl

abbrev Sequence.BoundedBy (a:Sequence) (M:ℚ) : Prop := ∀ n, |a n| ≤ M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℚ) : a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.isBounded_def (a:Sequence) : a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

/-- Example 5.1.13 -/
example : BoundedBy ![1,-2,3,-4] 4 := by intro i; fin_cases i <;> norm_num

/-- Example 5.1.13 -/
example : ¬((fun n:ℕ ↦ (-1)^n * (n+1:ℚ)):Sequence).IsBounded := by
  by_contra h
  obtain ⟨M, hM,hbon⟩ := h 
  set m := ⌈M⌉
  have hm : m >= 0 := by
    qify
    calc
      _ <= M := hM
      _ <= m := by exact Int.le_ceil M
  specialize hbon m
  simp[hm] at hbon
  rw[abs_mul] at hbon
  simp at hbon
  rw[abs_of_pos] at hbon
  have : M <= m.toNat := by
    calc
      _ <= (m:ℚ) := by exact Int.le_ceil M
      _ = (m.toNat) := by norm_cast; exact Int.eq_natCast_toNat.mpr hm
  grind
  exact Nat.cast_add_one_pos m.toNat

/-- Example 5.1.13 -/
example : ((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsBounded := by
  refine ⟨ 1, by norm_num, ?_ ⟩; intro i; by_cases h: 0 ≤ i <;> simp [h]

/-- Example 5.1.13 -/
example : ¬((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  by_contra h; specialize h (1/2 : ℚ) (by norm_num)
  choose N h using h; specialize h N _ (N+1) _ <;> try omega
  by_cases h': Even N
  · simp [h'.neg_one_pow, (h'.add_one).neg_one_pow, Section_4_3.dist] at h
    norm_num at h
  observe h₁: Odd N
  observe h₂: Even (N+1)
  simp [h₁.neg_one_pow, h₂.neg_one_pow, Section_4_3.dist] at h
  norm_num at h

/-- Lemma 5.1.14 -/
lemma IsBounded.finite {n:ℕ} (a: Fin n → ℚ) : ∃ M ≥ 0,  BoundedBy a M := by
  -- this proof is written to follow the structure of the original text.
  induction' n with n hn
  . use 0; simp
  set a' : Fin n → ℚ := fun m ↦ a m.castSucc
  choose M hpos hM using hn a'
  have h1 : BoundedBy a' (M + |a (Fin.ofNat _ n)|) := fun m ↦ (hM m).trans (by simp)
  have h2 : |a (Fin.ofNat _ n)| ≤ M + |a (Fin.ofNat _ n)| := by simp [hpos]
  refine ⟨ M + |a (Fin.ofNat _ n)|, by positivity, ?_ ⟩
  intro m; obtain ⟨ j, rfl ⟩ | rfl := Fin.eq_castSucc_or_eq_last m
  . grind
  convert h2; simp

lemma IsBounded.steady {a: Sequence} {ε :ℚ }(ha: ε.Steady a) (hε : ε >= 0) : ∃M ≥ 0 , a.BoundedBy M := by
  specialize ha a.n₀ (by simp)
  set a₀ := |a a.n₀|
  use a₀ + ε 
  split_ands
  . have : a₀ ≥ 0 := by simp[a₀] 
    grind
  intro m
  specialize ha m
  by_cases hm : m >= a.n₀
  . specialize ha hm
    set aₘ := |a.seq m|
    unfold Rat.Close  at ha
    apply le_add_of_sub_left_le
    rw[abs_sub_comm] at ha
    have : aₘ - a₀ <= |a m - a a.n₀| := by
      have := abs_add (a m - a a.n₀) (a a.n₀)
      have : aₘ <= |a m - a a.n₀| + a₀ := by
        simp[aₘ,a₀]
        simpa[sub_add_cancel] using this
      exact abs_sub_abs_le_abs_sub (a.seq m) (a.seq a.n₀)
    grind
  push_neg at hm
  have := a.vanish m hm
  simp[this]
  calc
    _ <= a₀ := by simp[a₀]
    _ <= _ := by grind

/-- Lemma 5.1.15 (Cauchy sequences are bounded) / Exercise 5.1.1 -/
lemma Sequence.isBounded_of_isCauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  specialize h 1 (by simp)
  choose N hN hste using h
  rw[ge_iff_le,le_iff_exists_nonneg_add] at hN
  choose c hc hdiff using hN
  lift c to ℕ using hc
  have hbon1 := IsBounded.steady (hste) (by simp)
  obtain ⟨u1, hu1, hbon1⟩ := hbon1
  set a' : Fin c → ℚ := fun i ↦ a (a.n₀ +i)
  choose u2 hu2 hbon2 using IsBounded.finite a'
  use max u1 u2
  split_ands
  . simp;tauto
  intro i
  by_cases hi : i >= N
  . specialize hbon1 i
    rw[from_eval _ hi] at hbon1
    simp;left;assumption
  push_neg at hi
  by_cases hi' : i >= a.n₀
  . 
    rw[ge_iff_le,le_iff_exists_nonneg_add] at hi'
    choose c' hc hca using hi'
    lift c' to ℕ using hc
    have hcc': c' < c := by
      simpa[← hca,← hdiff] using hi
    have : a i = a' ⟨c',hcc'⟩  := by
      simp[a',hca]
    simp[this];right
    specialize hbon2 ⟨c',hcc'⟩ 
    assumption
  push_neg at hi'
  have := a.vanish i hi'
  simp[this];tauto

/-- Exercise 5.1.2 -/
theorem Sequence.isBounded_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a + b:Sequence).IsBounded := by
      choose ua hua hbona using ha
      choose ub hub hbonb using hb
      use ua+ub
      refine ⟨by grind, ?_ ⟩ 
      intro i
      specialize hbona i
      specialize hbonb i
      by_cases hi : 0 <= i
      . 
        lift i to ℕ using hi
        simp at hbona hbonb ⊢ 
        calc
          _ <= |a i| + |b i| := abs_add _ _
          _ <= _ := by grind
      simp[hi]
      grind

theorem Sequence.isBounded_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a - b:Sequence).IsBounded := by
      choose ua hua hbona using ha
      choose ub hub hbonb using hb
      use ua+ub
      refine ⟨by grind, ?_ ⟩ 
      intro i
      specialize hbona i
      specialize hbonb i
      by_cases hi : 0 <= i
      . 
        lift i to ℕ using hi
        simp at hbona hbonb ⊢ 
        rw[sub_eq_add_neg]
        calc
         _ <= |a i| + |-b i| := abs_add _ _
         _ = |a i| + |b i| := by simp
         _ <= _ := by grind
      simp[hi]
      grind

theorem Sequence.isBounded_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a * b:Sequence).IsBounded := by
      choose ua hua hbona using ha
      choose ub hub hbonb using hb
      use ua*ub
      split_ands
      . simp[mul_nonneg_iff];left;tauto
      intro i
      specialize hbona i
      specialize hbonb i
      by_cases hi : 0 <= i
      . 
        lift i to ℕ using hi
        simp at hbona hbonb ⊢ 
        rw[abs_mul];
        apply mul_le_mul_of_nonneg
        map_tacs[assumption;assumption;simp;assumption]
      simp[hi,mul_nonneg_iff];left;tauto
end Chapter5
