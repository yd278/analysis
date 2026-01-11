import Mathlib.Tactic
import Analysis.Section_5_5
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.2: The extended real number system

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some API for Mathlib's extended reals `EReal`, particularly with regard to the supremum
  operation `sSup` and infimum operation `sInf`.

-/

open EReal

/-- Definition 6.2.1 -/
theorem EReal.def (x:EReal) : (∃ (y:Real), y = x) ∨ x = ⊤ ∨ x = ⊥ := by
  revert x
  simp [EReal.forall]

theorem EReal.real_neq_infty (x:ℝ) : (x:EReal) ≠ ⊤ := coe_ne_top _

theorem EReal.real_neq_neg_infty (x:ℝ) : (x:EReal) ≠ ⊥ := coe_ne_bot _

theorem EReal.infty_neq_neg_infty : (⊤:EReal) ≠ (⊥:EReal) := add_top_iff_ne_bot.mp rfl

abbrev EReal.IsFinite (x:EReal) : Prop := ∃ (y:Real), y = x

abbrev EReal.IsInfinite (x:EReal) : Prop := x = ⊤ ∨ x = ⊥

theorem EReal.infinite_iff_not_finite (x:EReal): x.IsInfinite ↔ ¬ x.IsFinite := by
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def x <;> simp [IsFinite, IsInfinite]

/-- Definition 6.2.2 (Negation of extended reals) -/
theorem EReal.neg_of_real (x:Real) : -(x:EReal) = (-x:ℝ) := rfl

#check EReal.neg_top
#check EReal.neg_bot

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.le_iff (x y:EReal) :
    x ≤ y ↔ (∃ (x' y':Real), x = x' ∧ y = y' ∧ x' ≤ y') ∨ y = ⊤ ∨ x = ⊥ := by
  obtain ⟨ x', rfl ⟩ | rfl | rfl := EReal.def x <;> obtain ⟨ y', rfl ⟩ | rfl | rfl := EReal.def y <;> simp

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.lt_iff (x y:EReal) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

#check EReal.coe_lt_coe_iff

/-- Examples 6.2.4 -/
example : (3:EReal) ≤ (5:EReal) := by rw [le_iff]; left; use (3:ℝ), (5:ℝ); norm_cast


/-- Examples 6.2.4 -/
example : (3:EReal) < ⊤ := by simp [lt_iff]; exact real_neq_infty 3


/-- Examples 6.2.4 -/
example : (⊥:EReal) < ⊤ := by simp


/-- Examples 6.2.4 -/
example : ¬ (3:EReal) ≤ ⊥ := by
  by_contra h
  simp at h
  exact real_neq_neg_infty 3 h

#check instCompleteLinearOrderEReal

/-- Proposition 6.2.5(a) / Exercise 6.2.1 -/
theorem EReal.refl (x:EReal) : x ≤ x := by simp

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.trichotomy (x y:EReal) : x < y ∨ x = y ∨ x > y := by
  obtain ⟨xr, rfl⟩ | rfl | rfl := x.def  <;>
  obtain ⟨yr, rfl⟩ | rfl | rfl := y.def  <;>
  simp
  exact lt_trichotomy xr yr

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_eq (x y:EReal) : ¬ (x < y ∧ x = y) := by
  obtain ⟨xr, rfl⟩ | rfl | rfl := x.def  <;>
  obtain ⟨yr, rfl⟩ | rfl | rfl := y.def  <;>
  simp
  apply ne_of_lt

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_gt_and_eq (x y:EReal) : ¬ (x > y ∧ x = y) := by
  obtain ⟨xr, rfl⟩ | rfl | rfl := x.def  <;>
  obtain ⟨yr, rfl⟩ | rfl | rfl := y.def  <;>
  simp
  apply ne_of_gt

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_gt (x y:EReal) : ¬ (x < y ∧ x > y) := by
  obtain ⟨xr, rfl⟩ | rfl | rfl := x.def  <;>
  obtain ⟨yr, rfl⟩ | rfl | rfl := y.def  <;>
  simp
  apply le_of_lt

/-- Proposition 6.2.5(c) / Exercise 6.2.1 -/
theorem EReal.trans {x y z:EReal} (hxy : x ≤ y) (hyz: y ≤ z) : x ≤ z := by
  obtain ⟨xr, rfl⟩ | rfl | rfl := x.def  <;>
  obtain ⟨yr, rfl⟩ | rfl | rfl := y.def  <;>
  obtain ⟨zr, rfl⟩ | rfl | rfl := z.def  <;>
  simp_all
  apply le_trans hxy hyz

/-- Proposition 6.2.5(d) / Exercise 6.2.1 -/
theorem EReal.neg_of_lt {x y:EReal} (hxy : x ≤ y): -y ≤ -x := by
  obtain ⟨xr, rfl⟩ | rfl | rfl := x.def  <;>
  obtain ⟨yr, rfl⟩ | rfl | rfl := y.def  <;>
  simp_all

/-- Definition 6.2.6 -/
theorem EReal.sup_of_bounded_nonempty {E: Set ℝ} (hbound: BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = sSup E := calc
  _ = sSup
      ((fun (x:WithTop ℝ) ↦ (x:WithBot (WithTop ℝ))) '' ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E)) := by
    rw [←Set.image_comp]; congr
  _ = sSup ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E) := by
    symm; apply WithBot.coe_sSup'
    . simp [hnon]
    exact WithTop.coe_mono.map_bddAbove hbound
  _ = ((sSup E : ℝ) : WithTop ℝ) := by congr; symm; exact WithTop.coe_sSup' hbound
  _ = _ := rfl

/-- Definition 6.2.6 -/
theorem EReal.sup_of_unbounded_nonempty {E: Set ℝ} (hunbound: ¬ BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = ⊤ := by
  rw [sSup_eq_top]
  intro b hb
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def b
  . simp; contrapose! hunbound; exact ⟨ y, hunbound ⟩
  . simp at hb
  simpa

/-- Definition 6.2.6 -/
theorem EReal.sup_of_empty : sSup (∅:Set EReal) = ⊥ := sSup_empty

/-- Definition 6.2.6 -/
theorem EReal.sup_of_infty_mem {E: Set EReal} (hE: ⊤ ∈ E) : sSup E = ⊤ := csSup_eq_top_of_top_mem hE

/-- Definition 6.2.6 -/
theorem EReal.sup_of_neg_infty_mem {E: Set EReal} : sSup E = sSup (E \ {⊥}) := (sSup_diff_singleton_bot _).symm

theorem EReal.inf_eq_neg_sup (E: Set EReal) : sInf E = - sSup (-E) := by
  simp_rw [←isGLB_iff_sInf_eq, isGLB_iff_le_iff, EReal.le_neg]
  intro b
  simp [lowerBounds]
  constructor
  . intro h a ha; specialize h (-a) (by simp [ha]); grind [neg_le_neg_iff]
  grind [EReal.le_neg_of_le_neg]

/-- Example 6.2.7 -/
abbrev Example_6_2_7 : Set EReal := { x | ∃ n:ℕ, x = -((n+1):EReal)} ∪ {⊥}

example : sSup Example_6_2_7 = -1 := by
  rw [EReal.sup_of_neg_infty_mem]
  simp
  apply IsLUB.sSup_eq
  constructor
  . intro x hx
    simp at hx
    choose n hn using hx
    rw[hn]
    norm_num;norm_cast
    simp
  . intro x hx
    rw[mem_upperBounds] at hx
    specialize hx (-1:EReal) (by 
      use 0; simp
    )
    simpa
    

example : sInf Example_6_2_7 = ⊥ := by
  rw [EReal.inf_eq_neg_sup]
  simp

/-- Example 6.2.8 -/
abbrev Example_6_2_8 : Set EReal := { x | ∃ n:ℕ, x = (1 - (10:ℝ)^(-(n:ℤ)-1):Real)}

example : sInf Example_6_2_8 = (0.9:ℝ) := by
  rw [EReal.inf_eq_neg_sup,neg_eq_iff_eq_neg]
  apply IsLUB.sSup_eq
  simp[Example_6_2_8 ]
  constructor
  . intro x hx
    simp at hx
    choose n hn using hx
    rw[neg_eq_iff_eq_neg] at hn
    rw[hn]
    norm_num;norm_cast;
    calc
     _ ≤ (1:ℝ) - (10 ^ (-1:ℤ)) := by norm_num
     _ ≤ _ := by gcongr; simp ; linarith
  intro x hx
  rw[mem_upperBounds] at hx
  specialize hx ((-0.9:ℝ):EReal) (by
    use 0
    simp;norm_cast; norm_num
  )
  simpa

example : sSup Example_6_2_8 = 1 := by 
  simp[Example_6_2_8]
  apply IsLUB.sSup_eq
  constructor
  . -- 1 is upper bound
    intro x hx
    simp at hx; choose n hn using hx
    rw[hn];norm_cast;field_simp;positivity
  -- 1 is least
  -- by contradiction
  intro x hx
  rw[mem_upperBounds] at hx
  by_contra! hxcon
  obtain ⟨x,rfl⟩ | rfl | rfl := EReal.def x
  . norm_cast at hxcon
    observe hd : 1-x > 0
    set d := 1 - x
    obtain ⟨n,hn⟩  := exists_pow_lt_of_lt_one hd (show (1/10:ℝ) < 1 by linarith)
    set dif  := (10:ℝ) ^ (- (n:ℤ) - 1)
    have hdif : dif < d := by
      calc
      _ ≤ (1/10:ℝ )^ n := by simp[dif]; rw[neg_sub_left,zpow_neg];norm_cast;gcongr;simp;simp
      _ < _ := hn
    specialize hx (1-dif)
    simp at hx
    specialize hx n (by simp[dif])
    norm_cast at hx
    linarith
  . simp at hxcon
  . specialize hx (0.9:ℝ) (by
      simp;use 0
      norm_cast;norm_num)
    simp at hx


/-- Example 6.2.9 -/
abbrev Example_6_2_9 : Set EReal := { x | ∃ n:ℕ, x = n+1}

example : sInf Example_6_2_9 = 1 := by
  rw [EReal.inf_eq_neg_sup,neg_eq_iff_eq_neg]
  apply IsLUB.sSup_eq
  simp[Example_6_2_9]
  constructor
  . intro x hx
    simp at hx
    choose n hn using hx
    rw[neg_eq_iff_eq_neg] at hn
    rw[hn]
    simp;norm_cast;linarith
  . intro x hx
    rw[mem_upperBounds] at hx
    specialize hx (-1)
    simp at hx
    specialize hx 0
    simpa using hx
  
example : sSup Example_6_2_9 = ⊤ := by
  apply IsLUB.sSup_eq
  simp[Example_6_2_9]
  constructor
  . intro x hx 
    simp
  . intro x hx 
    rw[mem_upperBounds] at hx
    contrapose! hx
    obtain ⟨x,rfl⟩ | rfl | rfl := x.def 
    . choose n hn using exists_nat_gt x
      use (n:ℝ) +1 ; simp;
      split_ands
      use n
      norm_cast;apply lt_trans hn
      simp
    . simp at hx
    . use 1; simp
      split_ands; use 0; simp
      exact compareOfLessAndEq_eq_lt.mp rfl

example : sInf (∅ : Set EReal) = ⊤ := by
  simp

example (E: Set EReal) : sSup E < sInf E ↔ E = ∅ := by
  constructor
  . intro h
    contrapose! h
    choose x hx using h
    have h1: sInf E ≤ x := by 
      exact CompleteSemilatticeInf.sInf_le E x hx
    have h2:x ≤ sSup E := by
      exact CompleteLattice.le_sSup E x hx
    apply le_trans h1 h2
  intro h
  rw[h]
  simp



/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_le_sup (E: Set EReal) {x:EReal} (hx: x ∈ E) : x ≤ sSup E := by
  exact CompleteLattice.le_sSup E x hx

/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_ge_inf (E: Set EReal) {x:EReal} (hx: x ∈ E) : x ≥ sInf E := by
  exact CompleteSemilatticeInf.sInf_le E x hx

/-- Theorem 6.2.11 (b) / Exercise 6.2.2 -/
theorem EReal.sup_le_upper (E: Set EReal) {M:EReal} (hM: M ∈ upperBounds E) : sSup E ≤ M := by
  exact CompleteSemilatticeSup.sSup_le E M hM

/-- Theorem 6.2.11 (c) / Exercise 6.2.2 -/
theorem EReal.inf_ge_loower (E: Set EReal) {M:EReal} (hM: M ∈ lowerBounds E) : sInf E ≥ M := by
  exact CompleteLattice.le_sInf E M hM


#check isLUB_iff_sSup_eq
#check isGLB_iff_sInf_eq

/-- Not in textbook: identify the Chapter 5 extended reals with the Mathlib extended reals.
-/
noncomputable abbrev Chapter5.ExtendedReal.toEReal (x:ExtendedReal) : EReal := match x with
  | real r => ((Real.equivR r):EReal)
  | infty => ⊤
  | neg_infty => ⊥

theorem Chapter5.ExtendedReal.coe_inj : Function.Injective toEReal := by
  intro e1 e2 heq
  obtain bot1 | r1 | top1 := e1<;>
  obtain bot2 | r2 | top2 := e2 <;>
  all_goals
    try simp at heq
    try rfl
  simp
  apply Real.equivR.injective heq

theorem Chapter5.ExtendedReal.coe_surj : Function.Surjective toEReal := by
  intro r
  obtain ⟨r,rfl⟩ | rfl |rfl := r.def 
  . use Real.equivR.symm r
    simp
    exact Equiv.apply_symm_apply Real.equivR r
  use infty
  use neg_infty
noncomputable abbrev Chapter5.ExtendedReal.equivEReal : Chapter5.ExtendedReal ≃ EReal := by
  apply Equiv.ofBijective toEReal
  refine⟨coe_inj,coe_surj⟩ 
