import Mathlib.Tactic
import Analysis.Section_5_3


/-!
# Analysis I, Section 5.4: Ordering the reals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordering on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5


/--
  Definition 5.4.1 (sequences bounded away from zero with sign). Sequences are indexed to start
  from zero as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayPos (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
abbrev BoundedAwayNeg (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayPos_def (a:ℕ → ℚ) : BoundedAwayPos a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c := by
  rfl

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayNeg_def (a:ℕ → ℚ) : BoundedAwayNeg a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c := by
  rfl

/-- Examples 5.4.2 -/
example : BoundedAwayPos (fun n ↦ 1 + 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : BoundedAwayNeg (fun n ↦ -1 - 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayPos (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 1; grind

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayNeg (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 0; grind

/-- Examples 5.4.2 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := ⟨ 1, by norm_num, by intros; simp ⟩

theorem BoundedAwayZero.boundedAwayPos {a:ℕ → ℚ} (ha: BoundedAwayPos a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rwa [abs_of_nonneg (by linarith)]


theorem BoundedAwayZero.boundedAwayNeg {a:ℕ → ℚ} (ha: BoundedAwayNeg a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rw [abs_of_neg (by linarith)]; linarith

theorem not_boundedAwayPos_boundedAwayNeg {a:ℕ → ℚ} : ¬ (BoundedAwayPos a ∧ BoundedAwayNeg a) := by
  intro ⟨ ⟨ _, _, h2⟩ , ⟨ _, _, h4 ⟩ ⟩; linarith [h2 0, h4 0]

abbrev Real.IsPos (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

abbrev Real.IsNeg (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

theorem Real.isPos_def (x:Real) :
    IsPos x ↔ ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

theorem Real.isNeg_def (x:Real) :
    IsNeg x ↔ ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl
abbrev Sequence.tail (a : ℕ → ℚ) (N:ℕ)   := fun n ↦ if n < N then a N else a n
theorem Sequence.IsCauchy.tail {a : ℕ → ℚ} (ha : (a:Sequence).IsCauchy ) : ∀ N, ((Sequence.tail a N):Sequence).IsCauchy := by
  intro N ε hε 
  specialize ha ε hε 
  obtain ⟨M, hM, ha⟩:= ha 
  simp at hM; lift M to ℕ using hM
  use M; simp;
  intro n hn m hm
  simp at hn hm
  lift n to ℕ using by grind
  lift m to ℕ using by grind
  simp[hn,hm,Rat.Close]
  by_cases hnN : n < N <;>
  by_cases hmN : m < N <;>
  simp[Sequence.tail,hnN,hmN]
  . grind
  . norm_cast at hn
    have : M ≤ N := by grind
    specialize ha N
    simp[this] at ha
    specialize ha m
    simp[hm,Rat.Close] at ha
    assumption
  . 
    have : M ≤ N := by grind
    specialize ha n
    simp[hn] at ha
    specialize ha N
    simp[this,Rat.Close] at ha
    assumption
  . specialize ha n 
    simp[hn] at ha
    specialize ha m
    simp[hm,Rat.Close ] at ha
    assumption

theorem Real.tail_eq {a: ℕ → ℚ} (ha : (a:Sequence).IsCauchy) : ∀ N, LIM a = LIM (Sequence.tail a N ) := by
  intro N
  rw[LIM_eq_LIM ha (by apply Sequence.IsCauchy.tail ha)]
  intro ε hε 
  use N
  intro n hn
  simp at hn
  lift n to ℕ using by grind
  norm_cast at hn
  have hn' : ¬ n < N := by grind
  simp[hn,Rat.Close,Sequence.tail,hn']
  grind

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.trichotomous (x:Real) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  by_cases hz : x = 0 <;> simp[hz]
  -- assume x != 0
  obtain ⟨a,ha,hbon,rfl⟩ := boundedAwayZero_of_nonzero hz
  obtain ⟨b, hb, hbon⟩ := hbon 
  have habon := ha (b/2) (by positivity)
  obtain ⟨N,hN,habon⟩ := habon 
  simp at hN
  lift N to ℕ using hN
  have haN := hbon N
  simp at haN
  have habonN := habon N
  simp at habonN
  obtain (haNn | haNp ):= le_abs'.mp haN
  map_tacs [right; left]
  all_goals
    use Sequence.tail a N
    have ht := Sequence.IsCauchy.tail ha N
    have he := tail_eq ha N
    refine ⟨?_, ht,he⟩ 
    use (b/2)
    simp [hb,Sequence.tail]
    intro n
    by_cases hn: n < N <;> simp[hn]
    try linarith
    have haNnb := habonN n
    simp at hn
    simp[hn,Rat.Close] at haNnb
    obtain ⟨haNnbu, haNnbl⟩ := abs_le.mp haNnb 
    linarith



/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_pos (x:Real) : ¬(x = 0 ∧ x.IsPos) := by
  rintro ⟨hz, ⟨a,hbon,ha,rfl⟩⟩ 
  have := BoundedAwayZero.boundedAwayPos hbon
  have := lim_of_boundedAwayZero this ha
  contradiction
  
  

theorem Real.nonzero_of_pos {x:Real} (hx: x.IsPos) : x ≠ 0 := by
  have := not_zero_pos x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_neg (x:Real) : ¬(x = 0 ∧ x.IsNeg) := by
  rintro ⟨hz, ⟨a,hbon,ha,rfl⟩⟩ 
  have := BoundedAwayZero.boundedAwayNeg hbon
  have := lim_of_boundedAwayZero this ha
  contradiction


theorem Real.nonzero_of_neg {x:Real} (hx: x.IsNeg) : x ≠ 0 := by
  have := not_zero_neg x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_pos_neg (x:Real) : ¬(x.IsPos ∧ x.IsNeg) := by
  rintro ⟨⟨a,⟨ua,hua,hbona⟩ ,ha,hal⟩ ,⟨b,⟨ub,hub,hbonb⟩ ,hb,rfl⟩ ⟩ 
  rw[LIM_eq_LIM hb ha] at hal
  specialize hal ua hua
  choose N hN using hal
  specialize hN N.toNat
  have : 0 ≤ N ∨ N ≤ 0 := by grind
  simp[this,Rat.Close] at hN
  set n := (max N 0).toNat
  specialize hbona n
  specialize hbonb n
  rw[abs_le] at hN
  grind

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
@[simp]
theorem Real.neg_iff_pos_of_neg (x:Real) : x.IsNeg ↔ (-x).IsPos := by
  constructor
  all_goals
    rintro⟨a,hbon,hac,hrfl⟩ 
    try rw[neg_eq_iff_eq_neg] at hrfl
    simp[hrfl]
    rw[neg_LIM _ hac]
    use -a
    refine ⟨?_, by apply IsCauchy.neg _ hac, rfl⟩ 
    peel hbon with b hb hbon n 
    simp;grind

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1-/
theorem Real.pos_add {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x+y).IsPos := by
  obtain ⟨ax,⟨ux,hux,hbonx⟩ ,haxc,rfl⟩:= hx 
  obtain ⟨ay,⟨uy,huy,hbony⟩ ,hayc,rfl⟩:= hy 
  rw[LIM_add haxc hayc]
  use (ax + ay); refine ⟨?_,by apply Sequence.IsCauchy.add haxc hayc ,rfl⟩ 
  use ux+uy
  have :ux + uy > 0 := by grind
  simp[this]
  intro n
  specialize hbonx n
  specialize hbony n
  grind

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_mul {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x*y).IsPos := by
  obtain ⟨ax,⟨ux,hux,hbonx⟩ ,haxc,rfl⟩:= hx 
  obtain ⟨ay,⟨uy,huy,hbony⟩ ,hayc,rfl⟩:= hy 
  rw[LIM_mul haxc hayc]
  use (ax * ay); refine ⟨?_,by apply Sequence.IsCauchy.mul haxc hayc ,rfl⟩ 
  have :ux * uy > 0 := by apply mul_pos hux huy
  use ux * uy
  simp[this]
  intro n
  specialize hbonx n
  specialize hbony n
  apply mul_le_mul hbonx hbony (by grind) (by grind)


theorem Real.pos_of_coe (q:ℚ) : (q:Real).IsPos ↔ q > 0 := by
  constructor
  . rintro ⟨a,⟨b,hb,hbon⟩, ha,hrfl ⟩ 
    rw[ratCast_def,
      LIM_eq_LIM (by apply Sequence.IsCauchy.const) ha,
    ] at hrfl
    specialize hrfl (b/2) (by positivity)
    choose N hN using hrfl
    specialize hN N.toNat
    simp at hN
    have : 0 ≤ N ∨ N ≤ 0 := by exact Int.le_total 0 N
    simp[this,Rat.Close] at hN
    set n := (max N 0).toNat
    rw[abs_le] at hN
    specialize hbon n
    linarith
  intro hq
  use fun x ↦ q
  refine ⟨?_, by apply Sequence.IsCauchy.const, by exact ratCast_def q⟩ 
  use q; simp[hq]
    

theorem Real.neg_of_coe (q:ℚ) : (q:Real).IsNeg ↔ q < 0 := by
  have := pos_of_coe (-q)
  simpa 


open Classical in
/-- Need to use classical logic here because isPos and isNeg are not decidable -/
noncomputable abbrev Real.abs (x:Real) : Real := if x.IsPos then x else (if x.IsNeg then -x else 0)

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_pos (x:Real) (hx: x.IsPos) : abs x = x := by
  simp [abs, hx]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_neg (x:Real) (hx: x.IsNeg) : abs x = -x := by
  have : ¬x.IsPos := by have := not_pos_neg x; simpa [hx] using this
  simp [abs, hx, this]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_zero : abs 0 = 0 := by
  have hpos: ¬(0:Real).IsPos := by have := not_zero_pos 0; simpa using this
  have hneg: ¬(0:Real).IsNeg := by have := not_zero_neg 0; simpa using this
  simp [abs, hpos, hneg]

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).IsNeg

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)

theorem Real.lt_iff (x y:Real) : x < y ↔ (x-y).IsNeg := by rfl
theorem Real.le_iff (x y:Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).IsPos := by
  have := lt_iff y x
  simp[this]

theorem Real.ge_iff (x y:Real) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  have := le_iff y x
  tauto

theorem Real.lt_of_coe (q q':ℚ): q < q' ↔ (q:Real) < (q':Real) := by
  rw[lt_iff,← sub_neg,← neg_of_coe]
  simp[ratCast_sub]


theorem Real.gt_of_coe (q q':ℚ): q > q' ↔ (q:Real) > (q':Real) := Real.lt_of_coe _ _

theorem Real.isPos_iff (x:Real) : x.IsPos ↔ x > 0 := by
  simp[gt_iff]
theorem Real.isNeg_iff (x:Real) : x.IsNeg ↔ x < 0 := by
  simp[lt_iff]

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.trichotomous' (x y:Real) : x > y ∨ x < y ∨ x = y := by
  set d := x - y
  obtain (hz|hpos|hneg):= trichotomous d 
  . right; right; simp[d] at hz; grind
  . left; rw[gt_iff]; simpa
  . right;left; rw[lt_iff];simp[d] at hneg; simpa


/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_lt (x y:Real) : ¬ (x > y ∧ x < y):= by
  rw[gt_iff, lt_iff]
  exact not_pos_neg (x - y)



/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_eq (x y:Real) : ¬ (x > y ∧ x = y):= by
  rw[gt_iff,← sub_eq_zero,and_comm]
  apply not_zero_pos


/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_lt_and_eq (x y:Real) : ¬ (x < y ∧ x = y):= by
  rw[lt_iff,← sub_eq_zero,and_comm]
  apply not_zero_neg

/-- Proposition 5.4.7(b) (order is anti-symmetric) / Exercise 5.4.2 -/
theorem Real.antisymm (x y:Real) : x < y ↔ (y - x).IsPos := by
  simp[lt_iff]

/-- Proposition 5.4.7(c) (order is transitive) / Exercise 5.4.2 -/
theorem Real.lt_trans {x y z:Real} (hxy: x < y) (hyz: y < z) : x < z := by
  simp[lt_iff] at *
  have : z - x = z - y + (y - x) := by abel
  rw[this]
  apply pos_add  hyz hxy


/-- Proposition 5.4.7(d) (addition preserves order) / Exercise 5.4.2 -/
theorem Real.add_lt_add_right {x y:Real} (z:Real) (hxy: x < y) : x + z < y + z := by
  simp[lt_iff] at *
  assumption'

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z:Real} (hxy: x < y) (hz: z.IsPos) : x * z < y * z := by
  rw [antisymm] at hxy ⊢; convert pos_mul hxy hz using 1; ring

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_le_mul_left {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : z * x ≤ z * y := by
  rw[le_iff] at *
  obtain (hlt|heq) := hxy
  left; rw[mul_comm, mul_comm z y]; apply mul_lt_mul_right hlt hz
  right; simp[heq]

theorem Real.mul_pos_neg {x y:Real} (hx: x.IsPos) (hy: y.IsNeg) : (x * y).IsNeg := by
  simp at *
  have := pos_mul hx hy
  simpa 

open Classical in
/--
  (Not from textbook) Real has the structure of a linear ordering. The order is not computable,
  and so classical logic is required to impose decidability.
-/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl := by
    intro a
    rw[le_iff];right;rfl
  le_trans := by
    intro a b c
    simp[le_iff] at *
    rintro (able | abeq) ( bcle | bceq)
    . left; apply lt_trans able bcle
    . left; grind
    . left; grind
    . right; grind
  lt_iff_le_not_ge := by
    intro a b
    simp[le_iff]
    constructor
    . 
      intro hlt
      split_ands
      . tauto
      . have := not_gt_and_lt a b
        tauto
      . have := not_gt_and_eq b a
        tauto
    rintro ⟨(hlt|heq), hgt, hne⟩ 
    tauto
    symm at heq; contradiction
  le_antisymm := by
    simp[le_iff]
    rintro a b (hlt|heq) (hgt|heq)
    . have := not_gt_and_lt a b; tauto
    . symm; assumption
    assumption'
  le_total := by
    intro a b
    simp[le_iff]
    have := trichotomous' a b
    tauto
  toDecidableLE := Classical.decRel _

/--
  (Not from textbook) Linear Orders come with a definition of absolute value |.|
  Show that it agrees with our earlier definition.
-/

noncomputable instance Real.instAddLeftMono : AddLeftMono Real where
  elim := by
    intro a b c
    simp
    intro le
    simp[le_iff] at *
    obtain (h | h ) := le
    . left; rw[add_comm,add_comm a c]; apply add_lt_add_right _ h
    . right; assumption'
theorem Real.abs_eq_abs (x:Real) : |x| = abs x := by
  by_cases h :x.IsPos
  simp[abs,h]
  have : 0 < x := by exact (isPos_iff x).mp h
  exact _root_.abs_of_pos this
  by_cases h' : x.IsNeg
  simp[abs,h,h']
  have : x < 0 := by exact (isNeg_iff x).mp h'
  exact _root_.abs_of_neg this
  have tri := trichotomous x
  simp[h,h'] at tri
  simp[abs,tri]

/-- Proposition 5.4.8 -/
theorem Real.inv_of_pos {x:Real} (hx: x.IsPos) : x⁻¹.IsPos := by
  observe hnon: x ≠ 0
  observe hident : x⁻¹ * x = 1
  have hinv_non: x⁻¹ ≠ 0 := by contrapose! hident; simp [hident]
  have hnonneg : ¬x⁻¹.IsNeg := by
    intro h
    observe : (x * x⁻¹).IsNeg
    have id : -(1:Real) = (-1:ℚ) := by simp
    simp only [neg_iff_pos_of_neg, id, pos_of_coe, self_mul_inv hnon] at this
    linarith
  have trich := trichotomous x⁻¹
  simpa [hinv_non, hnonneg] using trich

theorem Real.div_of_pos {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x/y).IsPos := by
  rw[div_eq_inv_mul]
  apply pos_mul
  apply inv_of_pos hy
  exact hx

theorem Real.inv_of_gt {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon: x ≠ 0
  observe hynon: y ≠ 0
  observe hxinv : x⁻¹.IsPos
  by_contra! this
  have : (1:Real) > 1 := calc
    1 = x * x⁻¹ := (self_mul_inv hxnon).symm
    _ > y * x⁻¹ := mul_lt_mul_right hxy hxinv
    _ ≥ y * y⁻¹ := mul_le_mul_left this hy
    _ = _ := self_mul_inv hynon
  simp at this

/-- (Not from textbook) Real has the structure of a strict ordered ring. -/
instance Real.instIsStrictOrderedRing : IsStrictOrderedRing Real where
  add_le_add_left := by
    intro a b hle c
    simp[le_iff] at *
    obtain (h | h ) := hle
    . left; assumption
    . right; assumption'

  add_le_add_right := by 
    intro a b hle c
    simp[hle]
  mul_lt_mul_of_pos_left := by
    intro a b c hab hc
    observe : c.IsPos
    have := mul_lt_mul_right hab this
    rwa[mul_comm,mul_comm c b]

  mul_lt_mul_of_pos_right := by
    intro a b c hab hc
    observe : c.IsPos
    exact mul_lt_mul_right hab this
  le_of_add_le_add_left := by
    intro a b c hab 
    rw[le_iff] at *
    simpa using hab
  zero_le_one := by
    rw[le_iff]; left
    rw[lt_iff]
    simp
    change IsPos (1:ℚ)
    exact (pos_of_coe 1).mpr rfl
/-- Proposition 5.4.9 (The non-negative reals are closed)-/
theorem Real.LIM_of_nonneg {a: ℕ → ℚ} (ha: ∀ n, a n ≥ 0) (hcauchy: (a:Sequence).IsCauchy) :
    LIM a ≥ 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hlim
  set x := LIM a
  rw [←isNeg_iff, isNeg_def] at hlim; choose b hb hb_cauchy hlim using hlim
  rw [boundedAwayNeg_def] at hb; choose c cpos hb using hb
  have claim1 : ∀ n, ¬ (c/2).Close (a n) (b n) := by
    intro n; specialize ha n; specialize hb n
    simp [Section_4_3.close_iff]
    calc
      _ < c := by linarith
      _ ≤ a n - b n := by linarith
      _ ≤ _ := le_abs_self _
  have claim2 : ¬(c/2).EventuallyClose (a:Sequence) (b:Sequence) := by
    contrapose! claim1; rw [Rat.eventuallyClose_iff] at claim1; peel claim1 with N claim1; grind [Section_4_3.close_iff]
  have claim3 : ¬Sequence.Equiv a b := by contrapose! claim2; rw [Sequence.equiv_def] at claim2; solve_by_elim [half_pos]
  simp_rw [x, LIM_eq_LIM hcauchy hb_cauchy] at hlim
  contradiction

/-- Corollary 5.4.10 -/
theorem Real.LIM_mono {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy)
  (hmono: ∀ n, a n ≤ b n) :
    LIM a ≤ LIM b := by
  -- This proof is written to follow the structure of the original text.
  have := LIM_of_nonneg (a := b - a) (by intro n; simp [hmono n]) (Sequence.IsCauchy.sub hb ha)
  rw [←Real.LIM_sub hb ha] at this; linarith

/-- Remark 5.4.11 --/

theorem Real.LIM_mono_fail :
    ∃ (a b:ℕ → ℚ), (a:Sequence).IsCauchy
    ∧ (b:Sequence).IsCauchy
    ∧ (∀ n, a n > b n)
    ∧ ¬LIM a > LIM b := by
  use (fun n ↦ 1 + 1/((n:ℚ) + 1))
  use (fun n ↦ 1 - 1/((n:ℚ) + 1))
  have hharc:= Sequence.IsCauchy.harmonic'
  have hconst := Sequence.IsCauchy.const 1
  have haddc := Sequence.IsCauchy.add hconst hharc
  have hsubc := Sequence.IsCauchy.sub hconst hharc
  refine⟨haddc,hsubc,?_,?_⟩ 
  .
    intro n;simp
    rw[← sub_neg];ring_nf;simp
    exact neg_lt_iff_pos_add'.mp rfl
  push_neg
  rw[le_iff_lt_or_eq];right
  calc 
    _ = LIM (fun n ↦ 1) + LIM (fun n ↦ 1 / (n + 1)):= by rw[LIM_add (by exact hconst) (by exact hharc)]; rfl
    _ = LIM (fun n ↦ 1) + 0 := by congr; exact LIM.harmonic
    _ = LIM (fun n ↦ 1) - LIM (fun n↦ 1/(n+1)) := by rw[LIM.harmonic];simp 
    _ = _ := by rw[LIM_sub (by exact hconst) (by exact hharc)]; rfl

/-- Proposition 5.4.12 (Bounding reals by rationals) -/
theorem Real.exists_rat_le_and_nat_ge {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x) ∧ ∃ N:ℕ, x < (N:Real) := by
  -- This proof is written to follow the structure of the original text.
  rw [isPos_def] at hx; choose a hbound hcauchy heq using hx
  rw [boundedAwayPos_def] at hbound; choose q hq hbound using hbound
  have := Sequence.isBounded_of_isCauchy hcauchy
  rw [Sequence.isBounded_def] at this; choose r hr this using this
  simp [Sequence.boundedBy_def] at this
  refine ⟨ ⟨ q, hq, ?_ ⟩, ?_ ⟩
  . convert LIM_mono (Sequence.IsCauchy.const _) hcauchy hbound
    exact Real.ratCast_def q
  choose N hN using exists_nat_gt r; use N
  calc
    x ≤ r := by
      rw [Real.ratCast_def r]
      convert LIM_mono hcauchy (Sequence.IsCauchy.const r) _
      intro n; specialize this n; simp at this
      exact (le_abs_self _).trans this
    _ < ((N:ℚ):Real) := by simp [hN]
    _ = N := rfl

/-- Corollary 5.4.13 (Archimedean property ) -/
theorem Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x := by
  -- This proof is written to follow the structure of the original text.
  obtain rfl | hx | hx := trichotomous x
  . use 1; simpa [isPos_iff] using hε
  . choose N hN using (exists_rat_le_and_nat_ge (div_of_pos hx hε)).2
    set M := N+1; refine ⟨ M, by positivity, ?_ ⟩
    replace hN : x/ε < M := hN.trans (by simp [M])
    simp
    convert mul_lt_mul_right hN hε
    rw [isPos_iff] at hε; field_simp
  use 1; simp_all [isPos_iff]; linarith

theorem Sequence.LIM_within_steady {a : ℕ → ℚ} {ε : ℚ} 
  (ha : (a:Sequence).IsCauchy)  {N:ℕ} (hsteady: ε.Steady ((a:Sequence).from N)) (hε : ε > 0):
    LIM a ≤ a N + ε ∧ a N - ε ≤ LIM a := by
  have haNc:= IsCauchy.const (a N)
  have hεc:= IsCauchy.const ε 
  have ha' := IsCauchy.tail ha N
  have heqaa' := Real.tail_eq ha N
  set a' := tail a N
  rw[heqaa']
  simp_rw[Real.ratCast_def]
  simp_rw[Real.LIM_add haNc hεc]
  simp_rw[Real.LIM_sub haNc hεc]
  split_ands
  map_tacs[apply Real.LIM_mono ha' (Sequence.IsCauchy.add haNc hεc); apply Real.LIM_mono (Sequence.IsCauchy.sub haNc hεc) ha']
  all_goals
    intro n
    simp[a',tail]
    by_cases hn : n < N <;> simp[hn]
    grind
    simp at hn
    specialize hsteady N (by simp) n (by simp[hn])
    simp[hn,Rat.Close] at hsteady
    rw[abs_le] at hsteady
    grind

theorem Sequence.LIM_all_close {a:ℕ → ℚ} {ε :ℚ}
  (ha : (a:Sequence).IsCauchy) (hε : ε > 0):
    ∃ N :ℕ , ∀ n ≥ N, LIM a ≤ a n + ε ∧ a n - ε ≤ LIM a := by
      have hsteady := ha (ε/2) (by positivity)
      choose N hN hsteady using hsteady
      simp at hN 
      lift N to ℕ using hN
      choose hupper hlower using LIM_within_steady ha hsteady (by positivity)
      simp at hlower hupper
      specialize hsteady N (by simp)
      use N
      intro n hn
      specialize hsteady n (by simp[hn])
      simp [Rat.Close,hn,abs_le] at hsteady
      choose hgu hgl using hsteady
      split_ands
      . 
        calc
          _ ≤ (a N :Real) + ε / 2:= hupper
          _ ≤ (ε /2) + (a n) + (ε/2) := by norm_cast;simpa
          _ = _ := by ring
      calc
        _ ≤ (a N : Real)+ε / 2 - ε  := by  gcongr; norm_cast
        _ = (a N :Real) - ε /2 := by ring
        _ ≤ _ := by linarith


/-- Proposition 5.4.14 / Exercise 5.4.5 -/
theorem Real.rat_between {x y:Real} (hxy: x < y) : ∃ q:ℚ, x < (q:Real) ∧ (q:Real) < y := by
  set diff := y - x
  have hdp : diff.IsPos := by simp[diff];exact (antisymm x y).mp hxy
  obtain ⟨ε,hε, hle⟩ := (exists_rat_le_and_nat_ge hdp).1
  obtain ⟨ax,hax,rfl⟩ := eq_lim x 
  have hes :=  hax (ε /2) (by positivity)
  choose N hN hsteady using hes
  simp at hN
  lift N to ℕ using hN
  obtain ⟨hupper, hlower⟩ := Sequence.LIM_within_steady hax hsteady (by positivity)
  rw[show ( (ε /2):ℚ  ) = ((ε:Real) / 2) by simp] at hupper hlower
  by_cases haxN: ax N > LIM ax
  . 
    use ax N
    simp[haxN]
    rw[show y = LIM ax + diff by simp[diff]]
    calc
      _ ≤ LIM ax + (ε / 2) := by grind
      _ < LIM ax + ε := by simp[hε]
      _ ≤ _ := by simp[hle]
  use (ax N + (3/4) * ε)
  split_ands
  . 
    calc 
      _ ≤ ((ax N):Real) + ε / 2 :=  by exact hupper
      _ < _ := by simp; rw[div_eq_mul_inv,mul_comm];gcongr;grind
      
  simp at haxN
  rw[show y = LIM ax + diff by simp[diff]]
  calc
    _ ≤ LIM ax + 3/4 * ε := by simp[haxN]
    _ < LIM ax + ε := by simp; apply mul_lt_of_lt_one_left; simp[hε]; grind
    _ ≤  _ := by simp[hle]

/-- Exercise 5.4.3 -/
theorem Real.floor_exist (x:Real) : ∃! n:ℤ, (n:Real) ≤ x ∧ x < (n:Real)+1 := by
  -- uniqueness 
  apply existsUnique_of_exists_of_unique
  pick_goal 2
  intro y1 y2 hy1 hy2
  obtain (h1 | h2| h3) := lt_trichotomy y1 y2
  . have : x < x := by
      calc
        _ < (y1:Real) + 1 := by exact hy1.2
        _ ≤ y2 := by norm_cast 
        _ ≤ _ := by exact hy2.1
    linarith
  . assumption
  . have : x < x := by
      calc
        _ < (y2:Real) + 1 := by exact hy2.2
        _ ≤ y1 := by norm_cast
        _ ≤ _ := by exact hy1.1
    linarith

  -- Existence 
  obtain ⟨a,ha,rfl⟩ := eq_lim x 
  have hes :=  ha (1 /2) (by positivity)
  choose N hN hsteady using hes
  simp at hN
  lift N to ℕ using hN
  obtain ⟨hupper, hlower⟩ := Sequence.LIM_within_steady ha hsteady (by positivity)

  have : (((1/2):ℚ ):Real) = (1:Real)/ 2 := by simp
  rw[this] at hupper hlower
  set x := a N
  set c := ⌈x⌉
  by_cases hc : c ≤ LIM a
  . use c
    refine⟨hc,?_⟩ 
    calc
      _ ≤ (x:Real) + (1 / 2) := hupper
      _ ≤ (c:Real) + (1/2) := by simp; exact Int.le_ceil x
      _ < _ := by simp;linarith
  by_cases hc' : c - 1 ≤ LIM a
  . use c - 1
    refine⟨by simp[hc'], ?_⟩ 
    simp at hc ⊢ 
    exact hc
  set d := c - 2;
  have hd : d < x - 1 := by
    simp[d,c]
    norm_cast
    calc
      _ < x + 1 - 2 := by gcongr; exact Int.ceil_lt_add_one x
      _ = _ := by linarith
  use d
  split_ands
  . rw[le_iff_lt_or_eq]; left
    rw[lt_of_coe] at hd
    simp at hd
    have : (x:Real) - 1 < (x:Real) - 1 / 2 := by
      simp;linarith
    grind
  simp at hc'
  simp[d]
  grind

/-- Exercise 5.4.4 -/
theorem Real.exist_inv_nat_le {x:Real} (hx: x.IsPos) : ∃ N:ℤ, N>0 ∧ (N:Real)⁻¹ < x := by
  set x' := x⁻¹ 
  choose N' hN' huni using floor_exist x'
  set N := N'+1
  use N
  split_ands
  . simp[N]
    have : 0 < x' := by simp[x'];exact (isPos_iff x).mp hx
    have : (0:Real) < N' + 1 := by grind
    norm_cast at this
  apply inv_lt_of_inv_lt₀
  exact (isPos_iff x).mp hx
  simp[N]
  simp[x'] at hN'
  grind

/-- Exercise 5.4.6 -/
theorem Real.dist_lt_iff (ε x y:Real) : |x-y| < ε ↔ y-ε < x ∧ x < y+ε := by
  rw[abs_lt];grind

/-- Exercise 5.4.6 -/
theorem Real.dist_le_iff (ε x y:Real) : |x-y| ≤ ε ↔ y-ε ≤ x ∧ x ≤ y+ε := by
rw[abs_le];grind

/-- Exercise 5.4.7 -/
theorem Real.le_add_eps_iff (x y:Real) : (∀ ε > 0, x ≤ y+ε) ↔ x ≤ y := by
constructor
. intro h
  contrapose! h
  set d := x - y;
  have : d/2 > 0 := by simp[d];exact h
  use d/2;simp[this]
  calc
    _ < y + d := by simp;simpa[d]
    _ = _ := by simp[d]
intro h ε hε 
calc
  _ ≤ x + ε := by simp; grind
  _ ≤ _ := by grind

/-- Exercise 5.4.7 -/
theorem Real.dist_le_eps_iff (x y:Real) : (∀ ε > 0, |x-y| ≤ ε) ↔ x = y := by
constructor
. intro h
  set d := |x - y|
  have : d = 0 := by 
    by_contra!
    have : d > 0 := by simpa[d]
    specialize h (d/2) (by positivity)
    linarith
  simpa[d,sub_eq_zero] using this
intro h ε hε 
simp[h];grind

/-- Exercise 5.4.8 -/
lemma Real.le_of_coe (q q' : ℚ) : q ≤ q' ↔ (q:Real) ≤ q':= by
  simp[le_iff_lt_or_eq]
theorem Real.LIM_of_le {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≤ x) :
    LIM a ≤ x := by
    by_contra! hcon
    choose q hupper hlower using rat_between hcon
    have : LIM a ≤ q := by
      rw[ratCast_def]
      apply LIM_mono hcauchy
      apply Sequence.IsCauchy.const
      intro n;
      have hn := h n
      rw[le_of_coe]
      grind
    linarith

lemma Sequence.IsCauchy.neg {a:ℕ → ℚ} (ha : (a:Sequence).IsCauchy) : ((-a: ℕ → ℚ ):Sequence).IsCauchy := by
  peel ha with ε hε N hN n hn m hm ha
  simp_all
  lift N to ℕ using hN
  lift n to ℕ using by grind
  lift m to ℕ using by grind
  simp at hn hm
  simp[Rat.Close] at ha ⊢ 
  rw[abs_le] at ha ⊢
  grind

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_ge {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≥ x) :
    LIM a ≥ x := by
    set a' := -a
    set x' := -x
    have ha' : (a':Sequence).IsCauchy := by
      simp[a']
      apply Sequence.IsCauchy.neg hcauchy
    have h' : ∀n, a' n ≤ x' := by
      peel h with n h
      simp[a',x',h]
    have := LIM_of_le ha' h'
    simp[a',x'] at this
    rw[← neg_LIM _ hcauchy] at this
    grind

theorem Real.max_eq (x y:Real) : max x y = if x ≥ y then x else y := max_def' x y

theorem Real.min_eq (x y:Real) : min x y = if x ≤ y then x else y := rfl

/-- Exercise 5.4.9 -/
theorem Real.neg_max (x y:Real) : max x y = - min (-x) (-y) := by
  simp[max_eq,min_eq]
  obtain (h1 | h2| h3) := trichotomous' x y
  . 
    observe : y ≤ x
    simp[this]
  . 
    observe : ¬ y ≤ x
    simp[this]
  simp[h3]

/-- Exercise 5.4.9 -/
theorem Real.neg_min (x y:Real) : min x y = - max (-x) (-y) := by
  simp[max_eq,min_eq]
  obtain (h1 | h2| h3) := trichotomous' y x
  . 
    observe : x ≤ y
    simp[this]
  . 
    observe : ¬ x ≤ y
    simp[this]
  simp[h3]

/-- Exercise 5.4.9 -/
theorem Real.max_comm (x y:Real) : max x y = max y x := by
  simp[max_eq]
  obtain (h1 | h2| h3) := trichotomous' x y
  . 
    observe : y ≤ x
    simp[this]
    intro h;grind
  . 
    observe : ¬ y ≤ x
    simp[this]
    intro h;grind
  simp[h3]


/-- Exercise 5.4.9 -/
theorem Real.max_self (x:Real) : max x x = x := by
  simp

/-- Exercise 5.4.9 -/
theorem Real.max_add (x y z:Real) : max (x + z) (y + z) = max x y + z := by
  simp[max_eq]
  obtain (h1 | h2| h3) := trichotomous' x y
  . 
    observe : y ≤ x
    simp[this]
  . 
    observe : ¬ y ≤ x
    simp[this]
  simp[h3]

/-- Exercise 5.4.9 -/
theorem Real.max_mul (x y :Real) {z:Real} (hz: z.IsPos) : max (x * z) (y * z) = max x y * z := by
  simp[max_eq]
  obtain (h1 | h2| h3) := trichotomous' x y
  . 
    observe h : y ≤ x
    observe hz : z > 0
    have hxyz : y * z ≤ x * z := by
      rwa[mul_le_mul_right hz]
    simp[hxyz,h]
  . 
    observe : ¬ y ≤ x
    observe hz : z > 0
    have hxyz : ¬ y * z ≤ x * z := by
      rwa[mul_le_mul_right hz]
    simp[hxyz,this]
  simp[h3]
/- Additional exercise: What happens if z is negative? -/

/-- Exercise 5.4.9 -/
theorem Real.min_comm (x y:Real) : min x y = min y x := by
  simp[min_eq]
  obtain (h1 | h2| h3) := trichotomous' y x
  . 
    observe : x ≤ y
    simp[this]
    intro h
    grind
  . 
    observe : ¬ x ≤ y
    simp[this]
    intro h
    grind
  simp[h3]

/-- Exercise 5.4.9 -/
theorem Real.min_self (x:Real) : min x x = x := by
  simp


/-- Exercise 5.4.9 -/
theorem Real.min_add (x y z:Real) : min (x + z) (y + z) = min x y + z := by
  simp[min_eq]
  obtain (h1 | h2| h3) := trichotomous' x y
  . 
    observe : ¬ x ≤ y
    simp[this]
  . 
    observe : x ≤ y
    simp[this]
  simp[h3]

/-- Exercise 5.4.9 -/
theorem Real.min_mul (x y :Real) {z:Real} (hz: z.IsPos) : min (x * z) (y * z) = min x y * z := by
  simp[min_eq]
  obtain (h1 | h2| h3) := trichotomous' x y
  . 
    observe h : ¬ x ≤ y
    observe hz : z > 0
    have hxyz : ¬ x * z ≤ y * z := by
      rwa[mul_le_mul_right hz]
    simp[hxyz,h]
  . 
    observe : x ≤ y
    observe hz : z > 0
    have hxyz :  x * z ≤ y * z := by
      rwa[mul_le_mul_right hz]
    simp[hxyz,this]
  simp[h3]

/-- Exercise 5.4.9 -/
theorem Real.inv_max {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (max x y)⁻¹ = min x⁻¹ y⁻¹ := by
  simp[min_eq,max_eq]
  obtain (h1 | h2| h3) := trichotomous' x y
  . 
    observe : y ≤ x
    have hinv : x⁻¹ ≤ y⁻¹ := by
      rwa[inv_le_inv₀ (by exact (isPos_iff x).mp hx) (by exact (isPos_iff y).mp hy)]
    simp[this,hinv]
  . 
    observe : ¬ y ≤ x
    have hinv : ¬ x⁻¹ ≤ y⁻¹ := by
      rwa[inv_le_inv₀ (by exact (isPos_iff x).mp hx) (by exact (isPos_iff y).mp hy)]
    simp[this,hinv]
  simp[h3]


/-- Exercise 5.4.9 -/
theorem Real.inv_min {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (min x y)⁻¹ = max x⁻¹ y⁻¹ := by
  simp[min_eq,max_eq]
  obtain (h1 | h2| h3) := trichotomous' x y
  . 
    observe : ¬ x ≤ y
    have hinv : ¬ y⁻¹ ≤ x⁻¹ := by
      rwa[inv_le_inv₀ (by exact (isPos_iff y).mp hy) (by exact (isPos_iff x).mp hx)]
    simp[this,hinv]
  . 
    observe : x ≤ y
    have hinv :  y⁻¹ ≤ x⁻¹ := by
      rwa[inv_le_inv₀ (by exact (isPos_iff y).mp hy) (by exact (isPos_iff x).mp hx )]
    simp[this,hinv]
  simp[h3]

/-- Not from textbook: the rationals map as an ordered ring homomorphism into the reals. -/
abbrev Real.ratCast_ordered_hom : ℚ →+*o Real where
  toRingHom := ratCast_hom
  monotone' := by
    simp[Monotone]


end Chapter5
