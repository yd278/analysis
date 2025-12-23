import Mathlib.Tactic
import Analysis.Section_5_6

/-!
# Analysis I, Chapter 5 epilogue: Isomorphism with the Mathlib real numbers

In this (technical) epilogue, we show that the "Chapter 5" real numbers `Chapter5.Real` are
isomorphic in various standard senses to the standard real numbers `ℝ`.  This we do by matching
both structures with Dedekind cuts of the (Mathlib) rational numbers `ℚ`.

From this point onwards, `Chapter5.Real` will be deprecated, and we will use the standard real
numbers `ℝ` instead.  In particular, one should use the full Mathlib API for `ℝ` for all
subsequent chapters, in lieu of the `Chapter5.Real` API.

Filling the sorries here requires both the Chapter5.Real API and the Mathlib API for the standard
natural numbers `ℝ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5


structure DedekindCut where
  E : Set ℚ
  nonempty : E.Nonempty
  bounded : BddAbove E
  lower: IsLowerSet E
  nomax : ∀ q ∈ E, ∃ r ∈ E, r > q

theorem isLowerSet_iff (E: Set ℚ) : IsLowerSet E ↔ ∀ q r, r < q → q ∈ E → r ∈ E :=
  isLowerSet_iff_forall_lt

abbrev Real.toSet_Rat (x:Real) : Set ℚ := { q | (q:Real) < x }

lemma Real.toSet_Rat_nonempty (x:Real) : x.toSet_Rat.Nonempty := by
  obtain (hx | hx | hx) := trichotomous x
  . 
    use -1;simp[hx]
  . obtain ⟨⟨q,hq,hqx⟩, ⟨n,hn⟩ ⟩  := exists_rat_le_and_nat_ge hx
    use q-1; simp;linarith
  have hx' : (-x).IsPos  := by exact (neg_iff_pos_of_neg x).mp hx
  obtain ⟨⟨q,hq,hqx⟩, ⟨n,hn⟩ ⟩  := exists_rat_le_and_nat_ge hx'
  use (-n)
  simp
  linarith

lemma Real.toSet_Rat_bounded (x:Real) : BddAbove x.toSet_Rat := by
  obtain (hx | hx | hx) := trichotomous x
  . 
    use 1
    rw[mem_upperBounds]
    intro q hq
    simp[hx] at hq
    linarith
  . obtain ⟨⟨q,hq,hqx⟩, ⟨n,hn⟩ ⟩  := exists_rat_le_and_nat_ge hx
    use n
    rw[mem_upperBounds]
    intro r hr; simp at hr
    suffices h: (r:Real) ≤ (n : Real) from by
      simpa using h
    linarith
  have hx' : (-x).IsPos  := by exact (neg_iff_pos_of_neg x).mp hx
  obtain ⟨⟨q,hq,hqx⟩, ⟨n,hn⟩ ⟩  := exists_rat_le_and_nat_ge hx'
  use (-q)
  rw[mem_upperBounds]
  intro r hr
  simp at hr
  have : (-q) ≥ x := by exact le_neg_of_le_neg hqx
  suffices h :  (r:Real) ≤ ((-q):Real) from by
    norm_cast at h
  linarith


lemma Real.toSet_Rat_lower (x:Real) : IsLowerSet x.toSet_Rat := by
  intro a b hab ha
  simp at ha ⊢ 
  replace hab : (b:Real) ≤ (a:Real) := by simpa
  linarith

lemma Real.toSet_Rat_nomax {x:Real} : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by
  intro q hq
  simp at hq
  obtain ⟨r,hrq,hrx⟩ := rat_between hq
  use r
  simp[hrx]
  simpa using hrq

abbrev Real.toCut (x:Real) : DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }
@[ext]
theorem DedekindCut.ext (a b : DedekindCut) (h : a.E = b.E) : a = b := by
  have ⟨_,_,_,_,_⟩ := a 
  have ⟨_,_,_,_,_⟩ := b
  subst h 
  congr

abbrev DedekindCut.toSet_Real (c: DedekindCut) : Set Real := (fun (q:ℚ) ↦ (q:Real)) '' c.E

lemma DedekindCut.toSet_Real_nonempty (c: DedekindCut) : c.toSet_Real.Nonempty := by 
  simp
  exact c.nonempty

lemma DedekindCut.toSet_Real_bounded (c: DedekindCut) : BddAbove c.toSet_Real := by
  have := c.bounded
  unfold toSet_Real
  choose ub hub using this
  use ub
  rw[mem_upperBounds] at hub ⊢ 
  intro x hx
  simp at hx
  choose q hqe hqx using hx
  specialize hub q hqe
  rw[← hqx];simpa

noncomputable abbrev DedekindCut.toReal (c: DedekindCut) : Real := sSup c.toSet_Real

lemma DedekindCut.toReal_isLUB (c: DedekindCut) : IsLUB c.toSet_Real c.toReal :=
  ExtendedReal.sSup_of_bounded c.toSet_Real_nonempty c.toSet_Real_bounded

noncomputable abbrev Real.equivCut : Real ≃ DedekindCut where
  toFun := toCut
  invFun := DedekindCut.toReal
  left_inv x := by
    have := DedekindCut.toReal_isLUB (x.toCut)
    set cut := x.toCut
    have hxLUB : IsLUB cut.toSet_Real x := by
      rw[isLUB_def]
      split_ands
      . 
        rw[mem_upperBounds]
        intro x' hx'
        choose q hqE hqx using hx'
        simp at hqx
        simp[cut,hqx] at hqE
        linarith
      intro M hM
      rw[mem_upperBounds] at hM
      by_contra! hMcon
      choose q hqM hqx using rat_between hMcon
      have hqin : (q:Real) ∈ cut.toSet_Real := by
        simp[cut,hqx]
      specialize hM q hqin
      linarith
    exact LUB_unique this hxLUB
  right_inv c := by
    have := DedekindCut.toReal_isLUB c
    set x := c.toReal
    ext q
    simp
    rw[isLUB_def] at this
    obtain ⟨hup,hleast⟩  := this
    rw[mem_upperBounds] at hup
    constructor
    . intro hqx
      by_contra! hqEcon
      choose up hupq hupx using rat_between hqx
      specialize hleast up (by
        rw[mem_upperBounds]
        intro x' hx'
        choose qx' hqE hqx' using hx'
        simp at hqx'
        rw[← hqx']
        have : qx' ≤  q  := by
          have := c.lower
          rw[isLowerSet_iff] at this
          by_contra! thi
          specialize this qx' q thi hqE
          contradiction
        simp at ⊢ hupq
        linarith
      )
      linarith
    intro hqE

    have hqle := hup q (by simpa)
    have hqne : q ≠ x := by
      by_contra! hqx
      have := c.nomax q hqE
      choose r hr hrq using this
      have hrle := hup r (by simpa)
      simp[← hqx] at hrle
      linarith

    exact lt_of_le_of_ne hqle hqne

end Chapter5

/-- Now to develop analogous results for the Mathlib reals. -/

abbrev Real.toSet_Rat (x:ℝ) : Set ℚ := { q | (q:ℝ) < x }

lemma Real.toSet_Rat_nonempty (x:ℝ) : x.toSet_Rat.Nonempty := by
  choose q hq using  exists_rat_lt x
  use q
  simpa

lemma Real.toSet_Rat_bounded (x:ℝ) : BddAbove x.toSet_Rat := by
  choose q hq using exists_rat_gt x
  use q
  rw[mem_upperBounds]
  intro p hp
  simp at hp
  have : (p:ℝ) < (q:ℝ) := by linarith
  simp at this
  linarith

lemma Real.toSet_Rat_lower (x:ℝ) : IsLowerSet x.toSet_Rat := by
  intro q r hrq hqx
  simp at hqx ⊢ 
  rify at hrq
  linarith

lemma Real.toSet_Rat_nomax (x:ℝ) : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by
  intro q hq
  simp at hq
  obtain ⟨r,hrq,hrx⟩  := exists_rat_btwn hq
  use r
  simp at hrq
  simp;tauto

abbrev Real.toCut (x:ℝ) : Chapter5.DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

namespace Chapter5

abbrev DedekindCut.toSet_R (c: DedekindCut) : Set ℝ := (fun (q:ℚ) ↦ (q:ℝ)) '' c.E

lemma DedekindCut.toSet_R_nonempty (c: DedekindCut) : c.toSet_R.Nonempty := by
  simp
  exact c.nonempty

lemma DedekindCut.toSet_R_bounded (c: DedekindCut) : BddAbove c.toSet_R := by
  have := c.bounded
  unfold toSet_R
  choose ub hub using this
  use ub
  rw[mem_upperBounds] at hub ⊢ 
  intro x hx
  simp at hx
  choose q hqe hqx using hx
  specialize hub q hqe
  rw[← hqx];simpa


noncomputable abbrev DedekindCut.toR (c: DedekindCut) : ℝ := sSup c.toSet_R

lemma DedekindCut.toR_isLUB (c: DedekindCut) : IsLUB c.toSet_R c.toR :=
  isLUB_csSup c.toSet_R_nonempty c.toSet_R_bounded

end Chapter5

noncomputable abbrev Real.equivCut : ℝ ≃ Chapter5.DedekindCut where
  toFun := _root_.Real.toCut
  invFun := Chapter5.DedekindCut.toR
  left_inv x := by
    have := Chapter5.DedekindCut.toR_isLUB (x.toCut)
    set cut := x.toCut
    have hxLUB : IsLUB cut.toSet_R x := by
      constructor
      . rw[mem_upperBounds]
        intro x' hx'
        simp[cut] at hx'
        choose q' hqx hqx' using hx'
        rw[← hqx']
        linarith
      . rw[mem_lowerBounds]
        intro M hM
        rw[mem_upperBounds] at hM
        by_contra! hcon
        choose q hqM hqx using exists_rat_btwn hcon
        specialize hM q (by simpa)
        linarith
    exact this.unique hxLUB
    
  right_inv c := by
    ext q
    simp
    have := Chapter5.DedekindCut.toR_isLUB c
    set x := c.toR
    choose hup hleast using this
    constructor
    . intro hqx
      by_contra! hcon
      choose M hMq hMx using exists_rat_btwn hqx
      rw[mem_lowerBounds] at hleast
      specialize hleast M
      rw[mem_upperBounds] at hleast
      specialize hleast (by
        intro x' hx'
        choose qx' hqE hqx' using hx'
        simp at hqx'
        rw[← hqx']
        have : qx' ≤ q := by
          have hlower := c.lower
          rw[Chapter5.isLowerSet_iff] at hlower
          by_contra! hqqx
          specialize hlower qx' q hqqx hqE
          contradiction
        simp at ⊢ hMq
        linarith
      )
      linarith
    intro hqE
    rw[mem_upperBounds] at hup
    have hqle := hup q (by simpa)
    have hqne : q ≠ x := by
      by_contra! hqx
      have := c.nomax q hqE
      choose r hr hrq using this
      have hrle := hup r (by simpa)
      simp[← hqx] at hrle
      linarith

    exact lt_of_le_of_ne hqle hqne

lemma Real.equivCut_left_inv {x:ℝ} : x.toCut.toR = x := by
  have := equivCut.left_inv x
  simpa 

namespace Chapter5

/-- The isomorphism between the Chapter 5 reals and the Mathlib reals. -/
noncomputable abbrev Real.equivR : Real ≃ ℝ := Real.equivCut.trans _root_.Real.equivCut.symm

lemma Real.equivR_iff (x : Real) (y : ℝ) : y = Real.equivR x ↔ y.toCut = x.toCut := by
  simp only [equivR, Equiv.trans_apply, ←Equiv.apply_eq_iff_eq_symm_apply]
  rfl
lemma Real.equivR_iff_lt (x : Real) (y : ℝ) : y = equivR x ↔ ∀ (q:ℚ), q < y ↔ q < x := by 
  rw[equivR_iff x y]
  simp
  rw[Set.ext_iff]
  simp

/-- The isomorphism preserves order and ring operations -/
instance Real.instArchimedean : Archimedean Real where
  arch := by
    intro x y hy

    rw[← gt_iff_lt,← isPos_iff] at hy
    have har := le_mul hy x
    choose M hM0 hMxy using har
    use M
    simp;linarith



lemma Real.eq_rat_if_exists_of_eq_lower_cut {K1 K2: Type _}  
  [LinearOrder K1] [Field K1] [IsStrictOrderedRing K1] [Archimedean K1]  
  [LinearOrder K2] [Field K2] [IsStrictOrderedRing K2] [Archimedean K2]  
  {x:K1} {y:K2}  (heq: ∀ (q:ℚ),q < x ↔ q < y) {q:ℚ }(hqx: q = x) : q = y := by
    by_contra! hqy
    obtain (hlt|hgt) := hqy.lt_or_gt
    . specialize heq q
      rw[← heq] at hlt;linarith 
    . choose mid hmy hmq using exists_rat_btwn hgt
      specialize heq mid
      have : mid < x := by rw[← hqx] ;norm_cast at ⊢ hmq
      rw[heq] at this
      linarith

lemma Real.gt_of_gt_of_eq_lower_cut {K1 K2: Type}
  [LinearOrder K1] [Field K1] [IsStrictOrderedRing K1] [Archimedean K1]  
  [LinearOrder K2] [Field K2] [IsStrictOrderedRing K2] [Archimedean K2]  
  {x:K1} {y:K2}  (heq: ∀ (q:ℚ),q < x ↔ q < y) {q:ℚ} (hqx: q>x ) :   q > y := by
    have heqq := heq q
    have heqinv : ∀ (q:ℚ), q < y ↔ q < x := by exact fun q ↦ (fun {a b} ↦ iff_comm.mp) (heq q)
    rw[← not_iff_not] at heqq
    push_neg at heqq
    have hyle := heqq.mp (by linarith)
    have hyne : y ≠ q := by
      by_contra! hye
      symm at hye
      have  := eq_rat_if_exists_of_eq_lower_cut heqinv hye
      linarith
    grind

lemma Real.eq_upper_cut_of_eq_lower_cut {K1 K2: Type}
  [LinearOrder K1] [Field K1] [IsStrictOrderedRing K1] [Archimedean K1]  
  [LinearOrder K2] [Field K2] [IsStrictOrderedRing K2] [Archimedean K2]  
  {x:K1} {y:K2}  (heq: ∀ (q:ℚ),q < x ↔ q < y) : (∀ (q:ℚ), q > x ↔ q > y) := by
    intro q
    constructor <;> intro hqx
    exact gt_of_gt_of_eq_lower_cut heq hqx
    have heq' : ∀ (q:ℚ), q < y ↔ q < x := by exact fun q ↦ (fun {a b} ↦ iff_comm.mp) (heq q)
    exact gt_of_gt_of_eq_lower_cut heq' hqx

lemma Real.eq_lower_cut_of_eq_upper_cut {K1 K2: Type}
  [LinearOrder K1] [Field K1] [IsStrictOrderedRing K1] [Archimedean K1]  
  [LinearOrder K2] [Field K2] [IsStrictOrderedRing K2] [Archimedean K2]  
  {x:K1} {y:K2}  (heq: ∀ (q:ℚ),q > x ↔ q > y) : (∀ (q:ℚ), q < x ↔ q < y) := by
    replace heq : ∀ (q:ℚ), q < -x ↔ q < -y := by
      intro q; specialize heq (-q)
      simpa[lt_neg] using heq
    suffices h : ∀(q:ℚ), q > -x ↔ q > -y from by
      intro q;specialize h (-q)
      simpa[neg_lt] using h
    exact eq_upper_cut_of_eq_lower_cut heq


lemma Real.equivR_iff_gt (x : Real) (y : ℝ) : y = equivR x ↔ ∀ (q:ℚ), q > y ↔ q > x := by 
  rw[equivR_iff_lt]
  constructor <;> intro heq
  exact eq_upper_cut_of_eq_lower_cut heq
  exact eq_lower_cut_of_eq_upper_cut heq

lemma Real.split_add_real_lt {K: Type _}  
  [LinearOrder K] [Field K] [IsStrictOrderedRing K] 
  [Archimedean K] 
  {x y : K} {q:ℚ } (hq: q < (x + y)) :  ∃ (xq yq: ℚ), xq < x ∧ yq < y ∧ xq + yq = q := by
    let ε := (x + y - q) / 2
    have hε : ε > 0 := by simp[ε,hq]
    set x' := x - ε 
    have hgap :x' < x := by exact sub_lt_self x hε
    choose xq hxqx' hxqx using exists_rat_btwn hgap
    use xq, (q-xq)
    refine⟨hxqx,?_,by simp⟩ 
    calc
      _ < q - x' := by simpa
      _ = q - x + ε := by simp[x'];ring
      _ < q - x + 2 * ε := by simp; exact lt_two_mul_self hε
      _ = y := by simp[ε]; ring

theorem Real.map_add (x y : Real) : equivR (x + y) = equivR (x) + equivR (y) := by
  -- skeleton:
  -- show that xR + yR is also LUB of (x+y)
  set xR := equivR x with hxR
  set yR := equivR y with hyR
  rw[Real.equivR_iff_lt] at hxR
  rw[Real.equivR_iff_lt] at hyR

  simp
  set sumC := (x+y).toCut
  have hlhs := DedekindCut.toR_isLUB sumC
  suffices hrhs : IsLUB sumC.toSet_R (xR + yR) from by
    exact hlhs.unique hrhs
  constructor
  -- upper: xR larger than all rats < x, similarly for yR
  --   for all rats sq < x + y , they can be written as sq =  xq + yq where  xq < x and yq < y
  --   hence, xq < xR and yq < yR , xq + yq < xR + yR
  .
    rw[mem_upperBounds]
    intro sumR hsumR
    simp at hsumR
    choose sumQ hsumQE hsumQR using hsumR
    simp[sumC] at hsumQE
    choose  xq yq hxq hyq heq using split_add_real_lt hsumQE
    rw[← hxR] at hxq
    rw[← hyR] at hyq
    have : (xq + yq:ℚ) < xR + yR := by simp;linarith
    rw[← hsumQR]
    rw[heq] at this
    linarith

  -- least: forall upperbounds uR > all rats sq < x + y, uR ≥ (xR + yR)
  --   assume UR < xR + yR, then there is a rat between
  --   and hence that rat can be written as xq + yq where xq < xR and yq < yR
  --   therefore xq < x and yq < y, xq + yq < x + y is in the set
  rw[mem_lowerBounds]
  intro uR huR
  rw[mem_upperBounds] at huR
  contrapose! huR with hlt
  choose uQ huQuR huQsum using exists_rat_btwn hlt
  choose xQ yQ hxQ hyQ heq using split_add_real_lt huQsum
  use uQ
  refine⟨?_, huQuR⟩ 
  simp[sumC]
  rw[hxR] at hxQ
  rw[hyR] at hyQ
  rw[← heq];simp;linarith


theorem Real.equivR_zero : equivR 0 = 0 := by
  symm;rw[equivR_iff_lt]
  simp

theorem Real.equivR_pos {x:Real} (hxp : x > 0 ) : equivR x > 0 := by
  set xR := equivR x with hxR
  rw[Real.equivR_iff_lt] at hxR
  have := (hxR 0).mpr hxp
  simpa

theorem Real.equivR_pos_iff {x:Real}: x > 0 ↔ equivR x > 0 := by
  set xR := equivR x with hxR
  rw[Real.equivR_iff_lt] at hxR
  specialize hxR 0
  simp at hxR
  exact id (Iff.symm hxR)

theorem Real.equivR_neg {x : Real}  :  - equivR x = equivR (-x) := by
  -- only consider  x > 0
  wlog hx:x > 0
  . simp at hx
    obtain (rfl | hx) := hx.eq_or_lt
    . rw[Real.equivR_zero,neg_zero,neg_zero,Real.equivR_zero]
    have hx : -x > 0 := by exact Left.neg_pos_iff.mpr hx
    specialize this hx
    rw[neg_neg,neg_eq_iff_eq_neg] at this
    symm
    assumption

  simp[neg_eq_iff_eq_neg]
  set xCp := x.toCut
  set xCn := (-x).toCut
  have hLUBp := DedekindCut.toR_isLUB xCp
  have hLUBn := DedekindCut.toR_isLUB xCn
  set xRp := xCp.toR
  set xRn := xCn.toR

  -- hence xRn < 0
  have hxRn : xRn < 0 := by
    have hadd := map_add x (-x)
    simp only[add_neg_cancel,Real.equivR_zero] at hadd
    apply equivR_pos at hx
    have : equivR (-x) < 0 := by linarith
    simp at this
    simpa[xRn,xCn]
  

  obtain ⟨hupn, hleastn⟩ := hLUBn 
  rw[mem_upperBounds] at hupn
  simp[mem_lowerBounds,mem_upperBounds] at hleastn


  -- -xRn is LUB as well
  suffices h: IsLUB xCp.toSet_R (-xRn) from hLUBp.unique h
  constructor
  . 


    -- (-xRn) is ub
    rintro m ⟨mQ,hmQE,rfl⟩ 
    simp; simp [xCp] at hmQE
    replace hmQE : -x ≤ -mQ := by linarith
    suffices h: xRn ≤ -mQ from by linarith
    specialize hleastn (-mQ) (by
      intro a ha
      simp[xCn] at ha
      have :(a:Real) < (-mQ:Real) := by linarith
      norm_cast at this ⊢ 
      linarith
    )
    assumption

  -- -xRn is least
  intro u hu
  simp[mem_upperBounds,xCp] at hu
  -- means that forall upperbounds u of (x) , (-xRn) ≤ u
  -- u is an upperbound means that forall rat m < x ; m < u
  -- by contra, assume -xRn > u, hence there exists a mid ,
  by_contra! hcon1
  choose mid hmidu hmidxRn using exists_rat_btwn hcon1
  -- mid > u and mid < -xRn, the later means that -mid > xRn hence a upper bound
  -- therefore -mid < -u 
  -- hence -mid <= -x
  have hcon2 : -mid ≤ -x := by
    specialize hu mid
    rw[← not_imp_not] at hu
    simp[hmidu] at hu
    linarith
  
  -- another rat in between -mid and xrn ,called quat,is in the cut
  replace hmidxRn : xRn < -mid :=by linarith
  choose qua hquamid hquaxRn using exists_rat_btwn hmidxRn
  simp[xCn] at hupn
  norm_cast at hquaxRn
  specialize hupn qua (by 
    calc
     _ < (-mid:Real) := by norm_cast
     _ ≤  _ := by exact hcon2
  )
  linarith

lemma Real.split_mul_real_lt {K: Type _}  [LinearOrder K] 
   [Field K] [IsStrictOrderedRing K] 
   [Archimedean K] 
  {x y : K} {q:ℚ } (hqz : q ≥ 0) (hq: q < (x * y)) (hxp : 0 < x) (hyp: 0 < y):  ∃ (xq yq: ℚ), xq ≥  0 ∧  xq < x ∧ yq ≥  0 ∧  yq < y ∧ xq * yq = q := by
    by_cases hqez : q = 0
    . use 0, 0
      simp[hxp,hyp,hqez]
    observe hqgtzz : q > 0
    have hr1 : (x * y) / q > 1 := by
      simp
      rw[one_lt_div₀]
      exact hq
      simpa
    set r := (x * y) / q

    have hqr : q = (x / r) * y := by field_simp[r];ring
    set x' := x / r
    have hgap : x' < x := by simp[x'];apply div_lt_self hxp hr1
    have hx'z : x' > 0 := by simp[x'];apply div_pos hxp (by linarith)
    choose xq hxq' hxq using exists_rat_btwn hgap
    use xq, (q/xq)
    have hxqz : xq ≥ 0 := by 
      have: (xq:K) > (0:K) := by linarith
      simp at this;linarith
    refine ⟨hxqz,hxq,Rat.div_nonneg hqz hxqz,?_,?_⟩ 
    . 
      calc
        _ < q / x' := by simp;gcongr;
        _ = y := by field_simp[hqr]
    apply mul_div_cancel₀
    by_contra!
    simp[this] at hxq'
    linarith


theorem Real.map_mul (x y : Real) : equivR (x * y) = equivR (x) * equivR (y) := by
  wlog hxp : x > 0
  . simp at hxp
    obtain (rfl|hxn) := hxp.eq_or_lt 
    . rw[zero_mul,Real.equivR_zero]
      simp
    specialize this (-x) y (by simp[hxn])  
    rw[neg_mul,← equivR_neg, ← equivR_neg] at this
    simpa
  wlog hyp : y > 0
  . simp at hyp
    obtain (rfl|hyn) := hyp.eq_or_lt 
    . rw[mul_zero,Real.equivR_zero]
      simp
    specialize this x (-y) hxp (by simp[hyn])  
    rw[mul_neg,← equivR_neg, ← equivR_neg] at this
    simpa
  set xR := equivR x with hxR
  set yR := equivR y with hyR
  observe hxRp : xR > 0
  observe hyRp : yR > 0
  rw[Real.equivR_iff_lt] at hxR
  rw[Real.equivR_iff_lt] at hyR

  simp
  set prdC := (x*y).toCut
  have hlhs := DedekindCut.toR_isLUB prdC
  suffices hrhs : IsLUB prdC.toSet_R (xR * yR) from by
    exact hlhs.unique hrhs

  constructor
  -- upper: xR larger than all rats < x, similarly for yR
  --   for all rats sq < x * y , they can be written as sq =  xq * yq where  xq < x and yq < y
  --   hence, xq < xR and yq < yR , xq + yq < xR + yR
  .
    rw[mem_upperBounds]
    intro prdR hprdR
    simp at hprdR
    choose prdQ hprdQE hprdQR using hprdR
    by_cases hprdz : prdQ < 0
    . have : xR * yR > 0 := by simp[xR,yR]; exact Left.mul_pos hxRp hyRp
      rw[← hprdQR]
      rify at hprdz
      linarith
    simp[prdC] at hprdQE
    simp at hprdz
    choose  xq yq hxqz hxq hyqz hyq heq using split_mul_real_lt hprdz hprdQE hxp hyp
    rw[← hxR] at hxq
    rw[← hyR] at hyq
    have : (xq * yq:ℚ) < xR * yR := by
      simp
      apply mul_lt_mul'' hxq hyq (by simp[hxqz]) (by simp[hyqz])
    rw[← hprdQR]
    rw[heq] at this
    linarith
  -- least: forall upperbounds uR > all rats sq < x * y, uR ≥ (xR + yR)
  --   assume UR < xR * yR, then there is a rat between
  --   and hence that rat can be written as xq * yq where xq < xR and yq < yR
  --   therefore xq < x and yq < y, xq + yq < x + y is in the set
  rw[mem_lowerBounds]
  intro uR huR
  rw[mem_upperBounds] at huR
  contrapose! huR with hlt
  choose uQ huQuR huQprd using exists_rat_btwn hlt
  by_cases huQz : uQ < 0
  . use 0
    simp[prdC]
    rify at huQz
    refine⟨Left.mul_pos hxp hyp, by linarith⟩ 
  simp at huQz
  choose xQ yQ hxQz hxQ hyQz hyQ heq using split_mul_real_lt huQz huQprd hxRp hyRp
  use uQ
  refine⟨?_, huQuR⟩ 
  simp[prdC]
  rw[hxR] at hxQ
  rw[hyR] at hyQ
  rw[← heq];simp;
  apply mul_lt_mul'' hxQ hyQ
  simp;linarith
  simp;linarith
    
noncomputable abbrev Real.equivR_ordered_ring : Real ≃+*o ℝ where
  toEquiv := equivR
  map_add' x y := by
    exact map_add x y
  map_mul' x y := by 
    exact map_mul x y
  map_le_map_iff' := by 
    intro x y
    rw[← not_iff_not];push_neg
    suffices h: equivR x - equivR y > 0↔ x - y > 0 from by
      rw[lt_iff, neg_iff_pos_of_neg, neg_sub,isPos_iff]
      rw[← h]
      exact Iff.symm sub_pos
    have hsubeq : equivR x - equivR y = equivR (x - y) := by
      simp_rw[_root_.sub_eq_add_neg]
      rw[equivR_neg, map_add]
    rw[hsubeq]
    exact Iff.symm equivR_pos_iff

theorem Real.pow_of_equivR (x:Real) (n:ℕ) : equivR (x^n) = (equivR x)^n := by
  induction' n with k hk
  . simp only [_root_.pow_zero ]
    symm
    rw[Real.equivR_iff_lt]
    intro q; norm_cast
  simp_rw[_root_.pow_succ]
  rw[← hk]
  exact map_mul (x ^ k) x
theorem Real.equivR_inv {x:Real}: equivR (x⁻¹) = (equivR x) ⁻¹ := by
  -- makesure both are positive
  wlog hx : x > 0
  .
    push_neg at hx
    obtain (rfl | hlt) := hx.eq_or_lt
    simp only [_root_.inv_zero]
    rw[Real.equivR_zero]
    simp
    have hnx: -x > 0 := by linarith
    specialize this hnx
    rwa[inv_neg,← equivR_neg,← equivR_neg,inv_neg,neg_inj] at this
  set xR := equivR x with hxRx
  have hxR : xR>0 := equivR_pos hx

  -- prove by of same cut 
  rw[equivR_iff_gt] at hxRx
  symm;rw[equivR_iff_lt]
  intro q
  by_cases hq : q ≤ 0
  .
    have hqxR : q < xR⁻¹ := LT.lt.trans_le' (inv_pos.mpr hxR) (by simpa)
    have hqx : q < x⁻¹ := LT.lt.trans_le' (inv_pos.mpr hx) (by simpa)
    simp[hqxR,hqx]

  push_neg at hq
  rw[lt_inv_comm₀ (by simpa) hxR]
  rw[lt_inv_comm₀ (by simpa) hx]
  specialize hxRx (q⁻¹)
  simpa using hxRx



theorem Real.zpow_of_equivR (x:Real) (n:ℤ) : equivR (x^n) = (equivR x)^n := by
  obtain ⟨m, (rfl|rfl)⟩  := n.eq_nat_or_neg
  norm_cast;exact pow_of_equivR x m
  simp_rw[_root_.zpow_neg]
  norm_cast
  rw[equivR_inv,pow_of_equivR]

-- This doesn't really work as the ratPow doesn't defined for neg values
/- theorem Real.ratPow_of_equivR (x:Real) (q:ℚ) : equivR (x^q) = (equivR x)^(q:ℝ) := by -/
/-   sorry -/


end Chapter5
