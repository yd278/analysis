import Mathlib.Tactic

/-!
# Analysis I, Section 4.4: gaps in the rational numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Irrationality of √2, and related facts about the rational numbers

Many of the results here can be established more quickly by relying more heavily on the Mathlib
API; one can set oneself the exercise of doing so.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Proposition 4.4.1 (Interspersing of integers by rationals) / Exercise 4.4.1 -/
lemma Rat.between_int_pos (x:ℚ) (hx : x > 0) : ∃! n : ℤ, n ≤ x ∧ x < n + 1 := by
  have hab := x.num_div_den
  have hbnz := x.den_ne_zero
  set az := x.num
  have haz : az > 0 := by exact num_pos.mpr hx
  set b := x.den
  have hbp : b > 0 := by grind
  qify at hbp
  obtain ⟨a,(hpos|hneg)⟩ := Int.eq_nat_or_neg az 
  pick_goal 2; simp[hneg] at haz; contradiction;
  set c := a % b with hc
  symm at hc
  rw[Nat.mod_eq_iff] at hc
  simp[hbnz] at hc
  obtain ⟨hcb, ⟨d, hbcd⟩ ⟩ := hc 
  simp[hpos] at hab 
  apply existsUnique_of_exists_of_unique  
  . 
    use d; simp
    rw[← hab] 
    split_ands
    . 
      have : a >= d * b := by
        rw[mul_comm]
        linarith
      qify at this
      exact (le_div_iff₀ hbp).mpr this
    . 
      have : a < (d + 1 ) * b := by
        ring_nf
        simpa[mul_comm,hbcd]
      qify at this
      exact (div_lt_iff₀ hbp).mpr this
  rintro y1 y2 ⟨hy11,hy12⟩ ⟨hy21,hy22⟩  
  have : y1 < y2 + 1 := by qify; grind
  have : y2 < y1 + 1 := by qify; grind
  grind

theorem Rat.between_int (x:ℚ) : ∃! n:ℤ, n ≤ x ∧ x < n+1 := by
  obtain ( hpos|hzero|hneg) := lt_trichotomy 0 x
  . 
    apply between_int_pos
    assumption
  . 
    symm at hzero
    use 0; simp[hzero]
    intro y hy hyp
    have : 0 < y + 1 := by 
      qify; assumption
    grind
  
  set x' := -x
  have hx' : x = -x' := by simp[x']
  have hpos : x' > 0 := by grind
  obtain ⟨n', ⟨hn'le,hn'gt⟩ , huni⟩ := between_int_pos x' hpos 
  rw[le_iff_lt_or_eq] at hn'le
  obtain (hn'lt | hn'eq) := hn'le 
  . 
    use -(n' + 1)
    simp[hx']
    split_ands
    . grind
    . grind
    intro y hyle hlty
    specialize huni (-(1+y))
    suffices hy : -(1 + y) = n' from by simp[← hy]
    apply huni
    split_ands
    . rw[add_comm]; simp; grind
    simp
    apply le_neg_of_le_neg at hyle
    have : n' < -y := by
      qify; grind
    rw[Int.lt_iff_add_one_le] at this
    qify at this
    grind
  simp[x'] at hn'eq
  use -n'
  simp[hn'eq]
  intro y hy hyp
  have: y <= -n' := by qify; grind
  have: -n' < y + 1 := by qify; grind
  linarith

theorem Nat.exists_gt (x:ℚ) : ∃ n:ℕ, n > x := by
  obtain ⟨l,⟨hl1,hl2⟩ ,huni⟩ := Rat.between_int x
  have : (l+1).toNat ≥ (l+1) := by simp
  use (l+1).toNat 
  qify at this
  grind

/-- Proposition 4.4.3 (Interspersing of rationals) -/
theorem Rat.exists_between_rat {x y:ℚ} (h: x < y) : ∃ z:ℚ, x < z ∧ z < y := by
  -- This proof is written to follow the structure of the original text.
  -- The reader is encouraged to find shorter proofs, for instance
  -- using Mathlib's `linarith` tactic.
  use (x+y)/2
  have h' : x/2 < y/2 := by
    rw [show x/2 = x*(1/2) by ring, show y/2 = y*(1/2) by ring]
    apply mul_lt_mul_of_pos_right h; positivity
  constructor
  . convert add_lt_add_right h' (x/2) using 1 <;> ring
  convert add_lt_add_right h' (y/2) using 1 <;> ring

/-- Exercise 4.4.2 (a) -/
theorem Nat.no_infinite_descent : ¬ ∃ a:ℕ → ℕ, ∀ n, a (n+1) < a n := by
  by_contra h
  obtain ⟨a,ha⟩ := h 
  have hcon : ∀ n k : ℕ, a n ≥ k := by
    intro n k
    induction' k with p hind generalizing n
    . simp
    specialize hind (n+1)
    specialize ha n
    grind
  specialize hcon 0 (a 0 + 1)
  omega

/-- Exercise 4.4.2 (b) -/
def Int.infinite_descent : Decidable (∃ a:ℕ → ℤ, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue
  use fun n ↦ -(n:ℤ)
  simp

/-- Exercise 4.4.2 (b) -/
def Rat.pos_infinite_descent : Decidable (∃ a:ℕ → {x: ℚ // 0 < x}, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

theorem Nat.even_or_odd'' (n:ℕ) : Even n ∨ Odd n := by
  set c := n % 2 with hc
  rw[Nat.mod_eq_iff] at hc
  simp at hc
  obtain ⟨hlt ,⟨k,hk⟩ ⟩ := hc
  by_cases hc1 : c = 1
  . 
    change n = 2 * k + c at hk
    simp [hc1] at hk
    right
    exact odd_iff.mpr hc1
  . have hc0 : c = 0 := by omega
    left
    exact even_iff.mpr hc0

theorem Nat.not_even_and_odd (n:ℕ) : ¬ (Even n ∧ Odd n) := by
  by_contra h
  obtain ⟨he,ho⟩ := h 
  rw[even_iff] at he
  rw[odd_iff] at ho
  simp[he] at ho

#check Nat.rec

/-- Proposition 4.4.4 / Exercise 4.4.3  -/
theorem Rat.not_exist_sqrt_two : ¬ ∃ x:ℚ, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; choose x hx using h
  have hnon : x ≠ 0 := by aesop
  wlog hpos : x > 0
  . apply this _ _ _ (show -x>0 by simp; order) <;> grind
  have hrep : ∃ p q:ℕ, p > 0 ∧ q > 0 ∧ p^2 = 2*q^2 := by
    use x.num.toNat, x.den
    observe hnum_pos : x.num > 0
    observe hden_pos : x.den > 0
    refine ⟨ by simp [hpos], hden_pos, ?_ ⟩
    rw [←num_div_den x] at hx; field_simp at hx
    have hnum_cast : x.num = x.num.toNat := Int.eq_natCast_toNat.mpr (by positivity)
    rw [hnum_cast] at hx; norm_cast at hx
  set P : ℕ → Prop := fun p ↦ p > 0 ∧ ∃ q > 0, p^2 = 2*q^2
  have hP : ∃ p, P p := by aesop
  have hiter (p:ℕ) (hPp: P p) : ∃ q, q < p ∧ P q := by
    obtain hp | hp := p.even_or_odd''
    . rw [even_iff_exists_two_mul] at hp
      obtain ⟨ k, rfl ⟩ := hp
      choose q hpos hq using hPp.2
      have : q^2 = 2 * k^2 := by linarith
      use q; constructor
      . apply lt_of_pow_lt_pow_left' 2
        simp[this]; ring_nf
        have :k > 0 := by
          by_contra hk;simp at hk
          simp[hk] at this; simp[this] at hpos
        rw[mul_lt_mul_left];simp
        simp[this]
      exact ⟨ hpos, k, by linarith [hPp.1], this ⟩
    have h1 : Odd (p^2) := by
      rw[odd_iff_exists_bit1] at hp ⊢ 
      obtain ⟨b,rfl⟩ := hp
      ring_nf
      use ( b * 2 + b ^ 2 * 2)
      ring
    have h2 : Even (p^2) := by
      choose q hpos hq using hPp.2
      rw [even_iff_exists_two_mul]
      use q^2
    observe : ¬(Even (p ^ 2) ∧ Odd (p ^ 2))
    tauto
  classical
  set f : ℕ → ℕ := fun p ↦ if hPp: P p then (hiter p hPp).choose else 0
  have hf (p:ℕ) (hPp: P p) : (f p < p) ∧ P (f p) := by
    simp [f, hPp]; exact (hiter p hPp).choose_spec
  choose p hP using hP
  set a : ℕ → ℕ := Nat.rec p (fun n p ↦ f p)
  have ha (n:ℕ) : P (a n) := by
    induction n with
    | zero => exact hP
    | succ n ih => exact (hf _ ih).2
  have hlt (n:ℕ) : a (n+1) < a n := by
    have : a (n+1) = f (a n) := n.rec_add_one p (fun n p ↦ f p)
    grind
  exact Nat.no_infinite_descent ⟨ a, hlt ⟩


/-- Proposition 4.4.5 -/
theorem Rat.exist_approx_sqrt_two {ε:ℚ} (hε:ε>0) : ∃ x ≥ (0:ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! h
  have (n:ℕ): (n*ε)^2 < 2 := by
    induction' n with n hn; simp
    simp [add_mul]
    apply lt_of_le_of_ne (h (n*ε) (by positivity) hn)
    have := not_exist_sqrt_two
    aesop
  choose n hn using Nat.exists_gt (2/ε)
  rw [gt_iff_lt, div_lt_iff₀', mul_comm, ←sq_lt_sq₀] at hn <;> try positivity
  grind

/-- Example 4.4.6 -/
example :
  let ε:ℚ := 1/1000
  let x:ℚ := 1414/1000
  x^2 < 2 ∧ 2 < (x+ε)^2 := by norm_num
