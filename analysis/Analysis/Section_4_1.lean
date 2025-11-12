import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.1: The integers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of
  natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of ℕ.

- Equivalence with the Mathlib integers `_root_.Int` (or `ℤ`), which we will use going forward.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl x := by simp -- commu
    symm  := by 
      intro x y sim
      omega
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [Setoid.r] at *
    calc
      _ = (a+b') + (c+d') := by abel
      _ = (a'+b) + (c'+d) := by rw [h1,h2]
      _ = _ := by abel)

/-- Definition 4.1.2 (Definition of addition) -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2; simp at h1 h2
    convert mul_congr _ _ <;> simpa
    )


/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  constructor
  . 
    rw[ofNat_eq,natCast_eq,eq]
    intro hn; simpa using hn
  . 
    intro hn;rw[hn];rfl


/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    intro ⟨a1, a2⟩ ⟨b1, b2⟩ hab  
    simp at hab
    simp only [Int.eq]
    omega
  )

theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
  AddGroup.ofLeftAxioms (by 
    intro a b c  
    obtain ⟨a1,a2,ha⟩ := eq_diff a 
    obtain ⟨b1,b2,hb⟩ := eq_diff b 
    obtain ⟨c1,c2,hc⟩ := eq_diff c 
    simp_rw[ha,hb,hc,add_eq,eq]
    abel
  ) (by 
      intro a
      obtain ⟨a1,a2,ha⟩ := eq_diff a 
      simp[ha,ofNat_eq,add_eq]
  ) (by 
      intro a
      obtain ⟨a1,a2,ha⟩ := eq_diff a 
      simp_rw[ha,neg_eq,add_eq,ofNat_eq,eq]
      abel
  )

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by 
    intro a b
    obtain ⟨a1,a2,ha⟩ := eq_diff a 
    obtain ⟨b1,b2,hb⟩ := eq_diff b 
    simp_rw[ha,hb,add_eq,eq]
    abel

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := by 
    intro a b
    obtain ⟨a1,a2,rfl⟩ := eq_diff a 
    obtain ⟨b1,b2,rfl⟩ := eq_diff b 
    simp_rw[mul_eq,eq]
    ring
  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq]; congr 1 <;> ring
  one_mul := by
    intro a
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    simp_rw[ofNat_eq,mul_eq,eq]
    ring
  mul_one := by 
    intro a
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    simp_rw[ofNat_eq,mul_eq,eq]
    ring

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := by
    intro a b c
    obtain ⟨a1, a2, rfl⟩ := eq_diff a 
    obtain ⟨b1, b2, rfl⟩ := eq_diff b 
    obtain ⟨c1, c2, rfl⟩ := eq_diff c 
    simp only [mul_eq,add_eq,eq]
    ring
  right_distrib := by
    intro a b c
    obtain ⟨a1, a2, rfl⟩ := eq_diff a 
    obtain ⟨b1, b2, rfl⟩ := eq_diff b 
    obtain ⟨c1, c2, rfl⟩ := eq_diff c 
    simp only [mul_eq,add_eq,eq]
    ring
  zero_mul := by
    intro a
    obtain ⟨a1, a2, rfl⟩ := eq_diff a 
    simp_rw[ofNat_eq,mul_eq,eq]
    ring
  mul_zero := by
    intro a
    obtain ⟨a1, a2, rfl⟩ := eq_diff a 
    simp_rw[ofNat_eq,mul_eq,eq]
    ring

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  simp_rw[sub_eq,natCast_eq,neg_eq,add_eq,eq]
  omega

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  contrapose! h
  obtain ⟨ha, hb⟩ := h 
  have tria := trichotomous a
  have trib := trichotomous b
  have neg_ne_zero (x : Int) : -x ≠ 0 ↔ x ≠ 0 := by simp
  obtain (haz| hap| hap) := tria <;> 
  obtain (hbz| hbp| hbp) := trib <;> 
  try contradiction 
  all_goals
    obtain ⟨an, ⟨han, rfl⟩ ⟩ := hap 
    obtain ⟨bn, ⟨hbn, rfl⟩ ⟩ := hbp
    by_contra! eqz
    simp only[natCast_eq,neg_eq,ofNat_eq,mul_eq,eq] at eqz
    ring_nf at eqz
  pick_goal 2; symm at eqz
  pick_goal 3; symm at eqz
  all_goals
    rw[Nat.mul_eq_zero] at eqz
    obtain (nz | nz ) := eqz
  all_goals
    rw[← cast_eq_0_iff_eq_0] at nz
    try rw[neg_ne_zero] at *
    contradiction

/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  have distr : (a - b) * c = 0 := by
    ring_nf; simp[h]
  apply mul_eq_zero at distr
  simp[hc] at distr
  apply_fun fun exp ↦ exp + b at distr
  simpa using distr


/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

theorem Int.lt_iff_le_and_ne (a b:Int): a < b ↔ a ≤ b ∧ a ≠ b := by rfl
/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) : a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  constructor
  . rintro ⟨⟨d,hdab⟩,hne ⟩
    use d; refine ⟨?_,hdab⟩ 
    contrapose! hne with heq
    simp[heq] at hdab
    symm;assumption
  rintro ⟨n,⟨hn,rfl⟩⟩ 
  split_ands
  . use n
  contrapose! hn
  simp at hn
  rwa[cast_eq_0_iff_eq_0] at hn

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  obtain ⟨⟨d,hadb⟩,hne ⟩ := h 
  split_ands
  . use d; simp[hadb];abel
  contrapose! hne
  simp [hadb] at *; assumption


/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  obtain ⟨⟨d,hadb⟩,hne ⟩:= hab 
  rw[hadb];ring_nf
  obtain ⟨⟨c,rfl⟩,hcne⟩ := hc
  simp only[zero_add] at hcne
  split_ands
  . use c * d;simp
  simp; by_contra h
  obtain (hc | hd) := mul_eq_zero h 
  . symm at hcne; contradiction
  simp[hd] at hadb
  symm at hne; contradiction

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  obtain ⟨⟨d,rfl⟩,hdb ⟩ := h 
  simp at hdb
  split_ands
  . use d; simp
  simpa

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
  obtain ⟨d,rfl⟩ := h 
  use d; simp

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  rw[lt_iff_exists_positive_difference] at hab hbc
  obtain ⟨d1, ⟨hnz1,rfl⟩ ⟩ := hab
  obtain ⟨d2, ⟨hnz2,rfl⟩ ⟩ := hbc
  set id1 :=  (d1 : Int) with hid1
  rw[natCast_eq] at hid1
  set id2 :=  (d2 : Int) with hid2
  rw[natCast_eq] at hid2
  split_ands
  . use d1 + d2; simp; abel
  obtain ⟨a1, a2, rfl⟩ := eq_diff a 
  simp_rw[hid1,hid2,add_eq]
  by_contra! heq
  simp only [eq] at heq
  abel_nf at heq; simp at heq
  tauto

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  set d := a - b with hd
  have tri := trichotomous d
  obtain (h1|h2|h3) := tri
  . right; right; rw[h1] at hd
    apply_fun fun exp ↦ exp + b at hd; simp at hd
    symm; assumption
  . obtain ⟨dn,hdn,hk⟩ := h2 
    left
    split_ands
    . use dn; simp[← hk,hd]
    contrapose! hdn; simp_all; rwa[cast_eq_0_iff_eq_0] at hd
  right;left
  obtain ⟨dn,hdn,hk⟩ := h3
  have : -d = dn := by aesop
  split_ands
  . use dn; simp[<- this, hd]
  contrapose! hdn; 
  simp [hdn,hk] at hd
  rw[cast_eq_0_iff_eq_0] at hd
  simpa


/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b):= by
  by_contra h
  obtain ⟨h1, h2⟩ := h 
  simp only[lt_iff_exists_positive_difference] at h1 h2
  obtain ⟨d1,⟨hd1nz,rfl⟩ ⟩ := h1 
  obtain ⟨d2,⟨hd2nz,x⟩ ⟩ := h2 

  set id1 :=  (d1 : Int) with hid1
  rw[natCast_eq] at hid1
  set id2 :=  (d2 : Int) with hid2
  rw[natCast_eq] at hid2
  obtain ⟨b1, b2, rfl⟩ := eq_diff b 
  simp_rw[hid1,hid2,add_eq,eq] at *
  abel_nf at x; simp at x
  tauto

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by
  by_contra h
  obtain ⟨h1,h2⟩:= h 
  obtain ⟨h1,hx⟩ := h1 
  symm at hx
  contradiction

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by
  by_contra h
  obtain ⟨h1,h2⟩:= h 
  obtain ⟨h1,hx⟩ := h1 
  contradiction

theorem Int.le_iff_lt_or_eq (a b:Int) : a ≤ b ↔ a < b ∨ a = b:= by
  simp[lt_iff_le_and_ne]
  constructor
  . tauto
  rintro (⟨h1,h2⟩ | h1) ;tauto
  use 0; simp[h1]

theorem Int.not_le_iff_gt (a b:Int) : ¬ a ≤ b ↔ a > b := by
  simp[le_iff_lt_or_eq]
  have nle:= not_lt_and_eq a b
  have nge:= not_gt_and_eq a b
  have ngl:= not_gt_and_lt a b
  have tri := trichotomous' a b
  tauto

/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        rw[le_iff_exists_add] at h
        obtain ⟨diff ,hdif⟩ := h 
        use diff
        set id1 :=  (diff : Int) with hid1
        rw[natCast_eq] at hid1
        rw[hid1]
        simp_rw[add_eq,eq]
        omega
      | isFalse h =>
        apply isFalse
        contrapose! h
        rw[le_iff] at h
        obtain⟨dif, hdin⟩ := h 
        rw[le_iff_exists_add]
        use dif
        set id1 :=  (dif : Int) with hid1
        rw[natCast_eq] at hid1
        rw[hid1]at hdin
        simp_rw[add_eq,eq] at hdin
        omega

  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by simp

/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := by intro a; use 0; simp
  le_trans := by 
    intro a b c hab hbc 
    obtain ⟨d1,rfl⟩ := hab 
    obtain ⟨d2,rfl⟩ := hbc
    use (d1 + d2); abel_nf; simp
  lt_iff_le_not_ge := by
    intro a b
    simp[not_le_iff_gt,lt_iff_le_and_ne]
  le_antisymm := by
    intro a b hab hba
    simp[le_iff_lt_or_eq] at *
    have ngl := not_gt_and_lt a b
    tauto
  le_total := by
    intro a b
    have tri := trichotomous' a b
    simp[le_iff_lt_or_eq]
    tauto
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
-- surely you can simply simp it but..
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by
  -- simp only [neg_mul, one_mul]
  obtain ⟨a1, a2, rfl⟩ := eq_diff a 
  simp_rw[ofNat_eq,neg_eq,mul_eq,eq]
  simp

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by
  let P (n :Int):= n + 1 > 0
  use P;simp[P]
  split_ands
  . use 1; simp
  . simp
  . intro n hn
    apply add_lt_add_right 1 at hn
    simp at hn
    have : (0:Int) < 1:= by
      split_ands;use 1; simp; simp
    order
  . use -2; use 1;
    simp_rw[ofNat_eq,natCast_eq,neg_eq,add_eq,eq]

/-- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by
  obtain ⟨nn,rfl⟩:= h 
  use (nn * nn)
  simp

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by
  have tri := trichotomous n
  obtain (h1 | h2 | h3) := tri
  . rw[h1];simp
  . obtain ⟨nn,⟨hnl,rfl⟩ ⟩ := h2 
    use (nn * nn); simp
  . obtain ⟨nn,⟨hnl,rfl⟩ ⟩ := h3
    use (nn * nn); simp

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by
  have tri := trichotomous n
  obtain (h1 | h2 | h3) := tri
  . use 0; simp[h1]
  . obtain ⟨nn,⟨hnl,rfl⟩ ⟩ := h2 
    use (nn * nn); simp
  . obtain ⟨nn,⟨hnl,rfl⟩ ⟩ := h3
    use (nn * nn); simp

/--
  Not in textbook: create an equivalence between Int and ℤ.
  This requires some familiarity with the API for Mathlib's version of the integers.
-/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ a - b) (by
    intro ⟨a1, a2⟩ ⟨b1, b2⟩ hab  
    simp[ ← _root_.Int.ofNat_inj] at hab
    simp
    omega
    )
  invFun z := by
    by_cases h: z≥ 0 
    . set zn := _root_.Int.toNat z
      exact (zn : Int)
    set zn := _root_.Int.toNat (-z)
    exact -(zn : Int)
  left_inv n := by
    obtain ⟨n1,n2,rfl⟩ := eq_diff n 
    by_cases hn: n2 ≤ n1 
    . simp[hn,sub_eq_formal_sub]
    simp[hn]
    set d := n2 - n1 with hdn
    have hd : d > 0 := by omega
    set di := (d : Int) with hdi
    rw[natCast_eq] at hdi
    simp_rw[hdi,neg_eq,eq,hdn]
    omega
  right_inv z := by
    by_cases h: z≥ 0 
    . simp[h];
      set zi := (z.toNat : Int) with hzi
      rw[natCast_eq] at hzi
      simp[hzi];omega
    simp[h]
    set z' := -z
    have neg_rfl : z = -z' := by omega
    simp[neg_rfl]
    set zi := (((z').toNat) : Int) with hzi
    rw[natCast_eq] at hzi
    simp[hzi,neg_eq]
    omega

lemma Int.map_add : ∀ (x y : Int),(equivInt (x + y)  ) = (equivInt x ) + (equivInt y ) := by
  intro x y
  set z := x + y with hz
  obtain ⟨x1,x2,hxn⟩ := eq_diff x 
  obtain ⟨y1,y2,hyn⟩ := eq_diff y
  obtain ⟨z1,z2,hzn⟩ := eq_diff z
  have hex : equivInt x = (x1:ℤ) - x2 := by simp[hxn]
  have hey : equivInt y = (y1:ℤ) - y2 := by simp[hyn]
  have hez : equivInt z = (z1:ℤ) - z2 := by simp[hzn]
  simp_rw [hz,hxn,hyn,add_eq,eq]at hzn
  omega

lemma Int.map_mul : ∀ (x y : Int),(equivInt (x * y)  ) = (equivInt x ) * (equivInt y ) := by
  intro x y
  set z := x * y with hz
  obtain ⟨x1,x2,hxn⟩ := eq_diff x 
  obtain ⟨y1,y2,hyn⟩ := eq_diff y
  obtain ⟨z1,z2,hzn⟩ := eq_diff z
  have hex : equivInt x = (x1:ℤ) - x2 := by simp[hxn]
  have hey : equivInt y = (y1:ℤ) - y2 := by simp[hyn]
  have hez : equivInt z = (z1:ℤ) - z2 := by simp[hzn]
  simp_rw[hz,hxn,hyn,mul_eq,eq] at hzn
  set cis := x1 * y1 + x2 * y2
  set trans := x1 * y2 + x2 * y1
  apply_fun Int.ofNat at hzn 
  simp at hzn
  simp_rw[hex,hey,hez]
  calc
  _ = (z1:ℤ ) + trans - z2 -trans := by ring
  _ = cis + z2 - z2 - trans := by rw [← hzn]
  _ = (cis - trans) := by simp
  _ = _ := by simp[cis,trans];ring
lemma Int.map_le_map_iff : ∀ (x y : Int) , equivInt x ≤ equivInt y ↔ x ≤ y := by
  intro x y
  constructor
  pick_goal 2
  rintro ⟨dif,hdif⟩ 
  obtain ⟨x1,x2,hxn⟩ := eq_diff x 
  obtain ⟨y1,y2,hyn⟩ := eq_diff y
  set dI := (dif : Int ) with hdI
  simp[natCast_eq] at hdI
  have hey : equivInt y = equivInt x + equivInt dif := by rw[hdif];apply map_add
  have hex : equivInt x = (x1:ℤ) - x2 := by simp[hxn]
  have hed : equivInt dif = (dif : ℤ ) - 0 := by simp[dI,hdI]
  simp [hex,hey,hed]
  -- -- -- --
  set xZ := equivInt x with hxZ
  set yZ := equivInt y with hyZ
  intro le
  rw[Int.le_def] at le
  apply Int.NonNeg.elim at le
  choose n hn using le
  use n
  apply_fun equivInt
  have hn' : yZ = xZ + n := by simp[← hn]
  rw[map_add,← hxZ, ← hyZ]
  simp_rw[hn']
  congr
/-- Not in textbook: equivalence preserves order and ring operations -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := by
    intro a b
    exact map_le_map_iff a b

end Section_4_1
