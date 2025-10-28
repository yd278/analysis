import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.4: Images and inverse images

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Images and inverse images of (Mathlib) functions, within the framework of Section 3.1 set
  theory. (The Section 3.3 functions are now deprecated and will not be used further.)
- Connection with Mathlib's image `f '' S` and preimage `f ⁻¹' S` notions.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.4.1.  Interestingly, the definition does not require S to be a subset of X. -/
abbrev SetTheory.Set.image {X Y:Set} (f:X → Y) (S: Set) : Set :=
  X.replace (P := fun x y ↦ f x = y ∧ x.val ∈ S) (by simp_all)

/-- Definition 3.4.1 -/
theorem SetTheory.Set.mem_image {X Y:Set} (f:X → Y) (S: Set) (y:Object) :
    y ∈ image f S ↔ ∃ x:X, x.val ∈ S ∧ f x = y := by
  grind [replacement_axiom]

/-- Alternate definition of image using axiom of specification -/
theorem SetTheory.Set.image_eq_specify {X Y:Set} (f:X → Y) (S: Set) :
    image f S = Y.specify (fun y ↦ ∃ x:X, x.val ∈ S ∧ f x = y) := by
      ext y'
      unfold image
      rw[replacement_axiom]
      rw[specification_axiom'']
      constructor
      . intro ⟨x, ⟨hfx, hx⟩ ⟩ 
        set y : Y := f x with hfy
        have hy' : y' ∈ Y := by
          rw[← hfx]
          exact y.property
        use hy'
        use x
        split_ands
        . exact hx
        rw[← hfy]
        obtain ⟨y, hy⟩ := y
        simp at hfx ⊢ 
        assumption'
      intro ⟨hy',⟨x,⟨hxS,hfx⟩ ⟩ ⟩ 
      use x
      split_ands
      . rw[hfx]
      exact hxS

/--
  Connection with Mathlib's notion of image.  Note the need to utilize the `Subtype.val` coercion
  to make everything type consistent.
-/
theorem SetTheory.Set.image_eq_image {X Y:Set} (f:X → Y) (S: Set):
    (image f S: _root_.Set Object) = Subtype.val '' (f '' {x | x.val ∈ S}) := by
  ext; simp; grind

theorem SetTheory.Set.image_in_codomain {X Y:Set} (f:X → Y) (S: Set) :
    image f S ⊆ Y := by intro _ h; rw [mem_image] at h; grind

/-- Example 3.4.2 -/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2*n:ℕ)

theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1,2,3} = {2,4,6} := by
  ext; simp only [mem_image, mem_triple, f_3_4_2]
  constructor
  · rintro ⟨_, (_ | _ | _), rfl⟩ <;> simp_all
  rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals simp_all

/-- Example 3.4.3 is written using Mathlib's notion of image. -/
example : (fun n:ℤ ↦ n^2) '' {-1,0,1,2} = {0,1,4} := by aesop

theorem SetTheory.Set.mem_image_of_eval {X Y:Set} (f:X → Y) (S: Set) (x:X) :
    x.val ∈ S → (f x).val ∈ image f S := by
      simp
      intro hxS
      use x
      have hxX := x.property
      split_ands
      . use hxX
      exact hxS

theorem SetTheory.Set.mem_image_of_eval_counter :
    ∃ (X Y:Set) (f:X → Y) (S: Set) (x:X), ¬((f x).val ∈ image f S → x.val ∈ S) := by
      use Nat
      use Nat
      use fun x ↦ ((_root_.Nat.pred x):Nat) 
      use {1}
      use 0
      push_neg
      split_ands
      . 
        simp
        use (1:Nat)
        use (1:Nat).property
        simp
      aesop 

/--
  Definition 3.4.4 (inverse images).
  Again, it is not required that U be a subset of Y.
-/
abbrev SetTheory.Set.preimage {X Y:Set} (f:X → Y) (U: Set) : Set := X.specify (P := fun x ↦ (f x).val ∈ U)

@[simp]
theorem SetTheory.Set.mem_preimage {X Y:Set} (f:X → Y) (U: Set) (x:X) :
    x.val ∈ preimage f U ↔ (f x).val ∈ U := by rw [specification_axiom']

/--
  A version of mem_preimage that does not require x to be of type X.
-/
theorem SetTheory.Set.mem_preimage' {X Y:Set} (f:X → Y) (U: Set) (x:Object) :
    x ∈ preimage f U ↔ ∃ x': X, x'.val = x ∧ (f x').val ∈ U := by
  constructor
  . intro h; by_cases hx: x ∈ X
    . use ⟨ x, hx ⟩; have := mem_preimage f U ⟨ _, hx ⟩; simp_all
    . grind [specification_axiom]
  . rintro ⟨ x', rfl, hfx' ⟩; rwa [mem_preimage]

/-- Connection with Mathlib's notion of preimage. -/
theorem SetTheory.Set.preimage_eq {X Y:Set} (f:X → Y) (U: Set) :
    ((preimage f U): _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) := by
  ext; simp

theorem SetTheory.Set.preimage_in_domain {X Y:Set} (f:X → Y) (U: Set) :
    (preimage f U) ⊆ X := by intro _ _; aesop

/-- Example 3.4.6 -/
theorem SetTheory.Set.preimage_f_3_4_2 : preimage f_3_4_2 {2,4,6} = {1,2,3} := by
  ext; simp only [mem_preimage', mem_triple, f_3_4_2]; constructor
  · rintro ⟨x, rfl, (_ | _ | _)⟩ <;> simp_all <;> omega
  rintro (rfl | rfl | rfl); map_tacs [use 1; use 2; use 3]
  all_goals simp

theorem SetTheory.Set.image_preimage_f_3_4_2 :
    image f_3_4_2 (preimage f_3_4_2 {1,2,3}) ≠ {1,2,3} := by
      set pig := preimage f_3_4_2 {1,2,3} with hpig
      have evpig : pig = {1} := by
        rw[hpig]
        ext x
        simp only [mem_preimage',mem_singleton,mem_triple, f_3_4_2]
        constructor
        . 
          rintro ⟨x, rfl, (_|_|_) ⟩ 
          <;> simp_all
          omega
        rintro rfl
        use 1
        simp
      rw[evpig]
      set ig := image f_3_4_2 {1} with hig
      have evig : ig = {2} := by
        ext x
        rw[hig,mem_image]
        simp only [f_3_4_2, mem_singleton]
        constructor
        . rintro ⟨x', h1, h2⟩ 
          simp at h1
          simp[h1]at h2
          symm
          exact h2
        intro hx
        use 1
        constructor
        . rfl
        rw[hx]
        simp
      rw[evig]
      simp[SetTheory.Set.ext_iff]
      use 1
      simp

/-- Example 3.4.7 (using the Mathlib notion of preimage) -/
example : (fun n:ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by
  ext; refine ⟨ ?_, by aesop ⟩; rintro (_ | _ | h)
  on_goal 3 => have : 2 ^ 2 = (4:ℤ) := (by norm_num); rw [←h, sq_eq_sq_iff_eq_or_eq_neg] at this
  all_goals aesop

example : (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) ≠ {-1,0,1,2} := by
  set f:= fun n: ℤ ↦ n^2 with hf
  set ig := f '' {-1,0,1,2} with hig
  have evig : ig = {0,1,4} := by aesop
  have evpig : f ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by
    ext; refine ⟨ ?_, by aesop ⟩; rintro (_ | _ | h)
    on_goal 3 => have : 2 ^ 2 = (4:ℤ) := (by norm_num); rw [←h, sq_eq_sq_iff_eq_or_eq_neg] at this
    all_goals aesop
  aesop

instance SetTheory.Set.inst_pow : Pow Set Set where
  pow := pow

@[coe]
def SetTheory.Set.coe_of_fun {X Y:Set} (f: X → Y) : Object := function_to_object X Y f

/-- This coercion has to be a `CoeOut` rather than a
`Coe` because the input type `X → Y` contains
parameters not present in the output type `Output` -/
instance SetTheory.Set.inst_coe_of_fun {X Y:Set} : CoeOut (X → Y) Object where
  coe := coe_of_fun

@[simp]
theorem SetTheory.Set.coe_of_fun_inj {X Y:Set} (f g:X → Y) : (f:Object) = (g:Object) ↔ f = g := by
  simp [coe_of_fun]

/-- Axiom 3.11 (Power set axiom) --/
@[simp]
theorem SetTheory.Set.powerset_axiom {X Y:Set} (F:Object) :
    F ∈ (X ^ Y) ↔ ∃ f: Y → X, f = F := SetTheory.powerset_axiom X Y F

/-- Example 3.4.9 -/
abbrev f_3_4_9_a : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 0, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_b : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 0, by simp ⟩ else ⟨ 1, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_c : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 1, by simp ⟩ else ⟨ 0, by simp ⟩

abbrev f_3_4_9_d : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 1, by simp ⟩

theorem SetTheory.Set.example_3_4_9 (F:Object) :
    F ∈ ({0,1}:Set) ^ ({4,7}:Set) ↔ F = f_3_4_9_a
    ∨ F = f_3_4_9_b ∨ F = f_3_4_9_c ∨ F = f_3_4_9_d := by
  rw [powerset_axiom]
  refine ⟨?_, by aesop ⟩
  rintro ⟨f, rfl⟩
  have h1 := (f ⟨4, by simp⟩).property
  have h2 := (f ⟨7, by simp⟩).property
  simp [coe_of_fun_inj] at *
  obtain _ | _ := h1 <;> obtain _ | _ := h2
  map_tacs [left; (right;left); (right;right;left); (right;right;right)]
  all_goals ext ⟨_, hx⟩; simp at hx; grind

abbrev indicator {X : Set} (f : X → ({0,1}: Set)) : (X → Prop) := fun x ↦ f x = (1:Object)
open Classical in
noncomputable abbrev selector (X Y : Set) : X → ({0,1} : Set) := fun x ↦  if x.val ∈ Y then ⟨ 1, by simp⟩  else ⟨0, by simp⟩ 
/-- Exercise 3.4.6 (i). One needs to provide a suitable definition of the power set here. -/
def SetTheory.Set.powerset (X:Set) : Set :=
  (({0,1} ^ X): Set).replace (P := fun F s ↦ 
      ∃ f : (X → ({0,1}:Set)), (f:Object) = F ∧ 
        ∃ S : Set, (S:Object) = s ∧ S = specify X (indicator f)
  ) (by 
    simp
  )

open Classical in
/-- Exercise 3.4.6 (i) -/
@[simp]
theorem SetTheory.Set.mem_powerset {X:Set} (x:Object) :
    x ∈ powerset X ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
      constructor
      . simp only [powerset]
        intro hx 
        simp at hx
        obtain ⟨f, hf⟩ := hx 
        set Y :=  X.specify (indicator f)  with hy
        use Y
        have hyx := specify_subset (indicator f)
        rw[← hy]at hyx
        symm at hf
        tauto
      rintro ⟨Y,rfl, hyx⟩ 
      simp[powerset]
      use selector X Y
      ext y
      rw[specification_axiom'']
      constructor
      . intro ⟨hxy,hy⟩ 
        simp[indicator, selector] at hy
        contrapose! hy
        simp[hy]
      intro hy
      have hxy : y∈ X:= by aesop
      use hxy
      simp[indicator,selector]
      simp[hy]

/-- Lemma 3.4.10 -/
theorem SetTheory.Set.exists_powerset (X:Set) :
   ∃ (Z: Set), ∀ x, x ∈ Z ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  use powerset X; apply mem_powerset

/- As noted in errata, Exercise 3.4.6 (ii) is replaced by Exercise 3.5.11. -/

/-- Remark 3.4.11 -/
theorem SetTheory.Set.powerset_of_triple (a b c x:Object) :
    x ∈ powerset {a,b,c}
    ↔ x = (∅:Set)
    ∨ x = ({a}:Set)
    ∨ x = ({b}:Set)
    ∨ x = ({c}:Set)
    ∨ x = ({a,b}:Set)
    ∨ x = ({a,c}:Set)
    ∨ x = ({b,c}:Set)
    ∨ x = ({a,b,c}:Set) := by
  simp only [mem_powerset, subset_def, mem_triple]
  refine ⟨ ?_, by aesop ⟩
  rintro ⟨Y, rfl, hY⟩; by_cases a ∈ Y <;> by_cases b ∈ Y <;> by_cases c ∈ Y
  on_goal 8 => left
  on_goal 4 => right; left
  on_goal 6 => right; right; left
  on_goal 7 => right; right; right; left
  on_goal 2 => right; right; right; right; left
  on_goal 3 => right; right; right; right; right; left
  on_goal 5 => right; right; right; right; right; right; left
  on_goal 1 => right; right; right; right; right; right; right
  all_goals congr; ext; simp; grind

/-- Axiom 3.12 (Union) -/
theorem SetTheory.Set.union_axiom (A: Set) (x:Object) :
    x ∈ union A ↔ ∃ (S:Set), x ∈ S ∧ (S:Object) ∈ A := SetTheory.union_axiom A x

/-- Example 3.4.12 -/
theorem SetTheory.Set.example_3_4_12 :
    union { (({2,3}:Set):Object), (({3,4}:Set):Object), (({4,5}:Set):Object) } = {2,3,4,5} := by
      ext x
      simp[union_axiom]
      aesop

/-- Connection with Mathlib union -/
theorem SetTheory.Set.union_eq (A: Set) :
    (union A : _root_.Set Object) =
    ⋃₀ { S : _root_.Set Object | ∃ S':Set, S = S' ∧ (S':Object) ∈ A } := by
  ext; simp [union_axiom, Set.mem_sUnion]; aesop

/-- Indexed union -/
abbrev SetTheory.Set.iUnion (I: Set) (A: I → Set) : Set :=
  union (I.replace (P := fun α S ↦ S = A α) (by grind))

theorem SetTheory.Set.mem_iUnion {I:Set} (A: I → Set) (x:Object) :
    x ∈ iUnion I A ↔ ∃ α:I, x ∈ A α := by
  rw [union_axiom]; constructor
  . simp_all [replacement_axiom]; grind
  grind [replacement_axiom]

open Classical in
noncomputable abbrev SetTheory.Set.index_example : ({1,2,3}:Set) → Set :=
  fun i ↦ if i.val = 1 then {2,3} else if i.val = 2 then {3,4} else {4,5}

theorem SetTheory.Set.iUnion_example : iUnion {1,2,3} index_example = {2,3,4,5} := by
  apply ext; intros; simp [mem_iUnion, index_example, Insert.insert]
  refine ⟨ by aesop, ?_ ⟩; rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals aesop

/-- Connection with Mathlib indexed union -/
theorem SetTheory.Set.iUnion_eq (I: Set) (A: I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α: _root_.Set Object) := by
  ext; simp [mem_iUnion]

theorem SetTheory.Set.iUnion_of_empty (A: (∅:Set) → Set) : iUnion (∅:Set) A = ∅ := by
  ext x
  simp[mem_iUnion]

/-- Indexed intersection -/
noncomputable abbrev SetTheory.Set.nonempty_choose {I:Set} (hI: I ≠ ∅) : I :=
  ⟨(nonempty_def hI).choose, (nonempty_def hI).choose_spec⟩

abbrev SetTheory.Set.iInter' (I:Set) (β:I) (A: I → Set) : Set :=
  (A β).specify (P := fun x ↦ ∀ α:I, x.val ∈ A α)

noncomputable abbrev SetTheory.Set.iInter (I: Set) (hI: I ≠ ∅) (A: I → Set) : Set :=
  iInter' I (nonempty_choose hI) A

theorem SetTheory.Set.mem_iInter {I:Set} (hI: I ≠ ∅) (A: I → Set) (x:Object) :
    x ∈ iInter I hI A ↔ ∀ α:I, x ∈ A α := by
      simp [iInter]
      set β := nonempty_choose hI with hβ 
      intro a 
      specialize a β.val β.property
      congr

/-- Exercise 3.4.1 -/
theorem SetTheory.Set.preimage_eq_image_of_inv {X Y V:Set} (f:X → Y) (f_inv: Y → X)
  (hf: Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f)  :
    image f_inv V = preimage f V := by
      ext v
      obtain ⟨hf1, hf2⟩ := hf 
      rw[mem_image,mem_preimage']
      constructor
      . 
        intro ⟨x, ⟨hxv, hfx⟩ ⟩ 
        use (f_inv x)
        grind
      rintro ⟨x,rfl,hfx⟩ 
      use (f x)
      grind

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f S)` and `S`. -/
theorem SetTheory.Set.preimage_of_image {X Y:Set} (f:X → Y) (S: Set) (hS: S ⊆ X) : S ⊆ preimage f ( image f S) := by
  rw[subset_def]
  intro x hxs
  simp
  use by aesop
  use x
  use by aesop

/- Exercise 3.4.2.  State and prove an assertion connecting `image f (preimage f U)` and `U`.
Interestingly, it is not needed for U to be a subset of Y. -/
theorem SetTheory.Set.image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : image f (preimage f U) ⊆ U := by
  rw[subset_def]
  intro u
  simp
  intro  x hx hfx
  simp[hx,hfx]
/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f (preimage f U))` and `preimage f U`.
Interestingly, it is not needed for U to be a subset of Y.-/
theorem SetTheory.Set.preimage_of_image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : preimage f (image f (preimage f U)) = preimage f U  := by
  ext x
  simp
  constructor
  . 
    rintro ⟨hx,a,ha,feq,ha',hfa⟩ 
    use hx
    rw[← feq]
    exact hfa
  rintro ⟨hx,hfx⟩  
  use hx
  use x ,hx

/--
  Exercise 3.4.3.
-/
theorem SetTheory.Set.image_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∩ B) ⊆ (image f A) ∩ (image f B) := by
      simp only [subset_def]
      intro x hint
      rw[mem_inter]
      simp at hint
      obtain ⟨a,⟨haX,hfa⟩ ,haA, haB⟩ := hint 
      split_ands 
      all_goals
        simp 
        use a
        refine ⟨?_, by assumption⟩
        use haX


      


theorem SetTheory.Set.image_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    (image f A) \ (image f B) ⊆ image f (A \ B) := by
      rw[subset_def]
      intro x hdiff
      rw[mem_sdiff] at hdiff
      obtain ⟨hxA, hxB⟩ := hdiff
      simp[image] at *
      obtain ⟨a,⟨haX,haf⟩ ,haA⟩ := hxA 
      specialize hxB a haX haf
      use a
      refine ⟨by (use haX), haA,hxB ⟩  

theorem SetTheory.Set.image_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∪ B) = (image f A) ∪ (image f B) := by
      ext x
      constructor
      .
        intro hunion
        simp at hunion
        obtain ⟨a, ⟨haX, rfl⟩, haunion ⟩:= hunion 
        simp
        obtain h | h := haunion
        map_tacs [left;right]
        all_goals 
          use a
          split_ands
          try use haX
          assumption 
      simp
      rintro (⟨a,⟨haX,rfl⟩ ,haa⟩  | ⟨a,⟨haX,rfl⟩ ,haa⟩)
      all_goals
      use a
      tauto

def SetTheory.Set.image_of_inter' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A ∩ B) = (image f A) ∩ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse
  push_neg
  set f : Nat → Nat := fun x ↦ ((_root_.Nat.pred x):Nat) with hf
  use Nat, Nat, f, ({0} : Set) , ({1} : Set)
  have : ({0} : Set ) ∩ ({1} : Set) = ∅ := by aesop
  rw[this]
  have : image f ∅ = ∅ := by aesop 
  rw[this]
  symm
  simp
  rw[eq_empty_iff_forall_notMem]
  push_neg
  use 0
  rw[mem_inter]
  split_ands 
  all_goals
    simp only [image]
    rw[replacement_axiom]
  map_tacs [use 0; use 1] 
  all_goals
    simp[f]

def SetTheory.Set.image_of_diff' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A \ B) = (image f A) \ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse
  push_neg
  set f : Nat → Nat := fun x ↦ 0 with hf
  have f0 : ∀ n , f n = 0 := by simp[f]
  use Nat, Nat, f, ({0,1} : Set) , ({1} : Set)
  have: ({0,1} : Set) \ ({1}:Set) = {0} := by aesop
  rw[this]
  have : ∀ S, (∃ (s: Nat), s.val ∈ S) → image f S = {0} := by
    intro S  ⟨⟨s,hsn⟩ , hss⟩ 
    ext x
    rw[mem_image]
    constructor
    . 
      rintro ⟨y,hys,hfy⟩ 
      simp[f0] at hfy
      simp[← hfy]
    simp
    intro hx
    simp only [f, hx]
    use s
    split_ands
    . simp at hss
      assumption
    use hsn; rfl
  have if0 : image f {0} = {0} := by
    exact this {0} (by use 0; simp)
  have if1 : image f {1} = {0} := by 
    exact this {1} (by use 1; simp)
  have if01 : image f {0,1} = {0} := by 
    exact this {0,1} (by use 0; simp)
  simp[if0,if1,if01]
  have : ({0}:Set )\ ({0}:Set) = ∅ := by
    aesop
  rw[this]
  by_contra hcon
  rw[eq_empty_iff_forall_notMem] at hcon
  specialize hcon 0
  simp at hcon

/-- Exercise 3.4.4 -/
theorem SetTheory.Set.preimage_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∩ B) = (preimage f A) ∩ (preimage f B) := by
      ext x
      rw[mem_inter]
      simp
      constructor
      . 
        rintro ⟨hx,hfxA,hfxB⟩ 
        split_ands <;> use hx 
      rintro ⟨⟨hxA,fxA⟩, ⟨hxB,fxB⟩  ⟩ 
      use hxA 

theorem SetTheory.Set.preimage_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∪ B) = (preimage f A) ∪ (preimage f B) := by
      ext x
      rw[mem_union]
      simp
      constructor
      . 
        rintro ⟨hx, (hxA|hxB)⟩ 
        map_tacs[left;right]
        all_goals 
          use hx
      rintro (⟨hx,fxa⟩  | ⟨hx, fxb⟩ ) 
      <;> use hx
      <;> tauto


theorem SetTheory.Set.preimage_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A \ B) = (preimage f A) \ (preimage f B)  := by
      ext x
      rw[mem_sdiff]
      simp
      constructor
      .
        rintro ⟨hx,fxa,fxnb⟩ 
        tauto
      rintro ⟨⟨hx, hxa⟩,hxx ⟩ 
      specialize hxx hx
      tauto

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.image_preimage_of_surj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ Y → image f (preimage f S) = S) ↔ Function.Surjective f := by
      simp[Function.Surjective]
      constructor
      -- equal -> Surjective
      . 
        contrapose!
        rintro ⟨y,hy,fay⟩ 
        use {y}
        constructor
        . rw[subset_def]
          intro x
          rw[mem_singleton]
          intro hx
          rw[hx]
          exact hy
        have :  preimage f {y} = ∅ := by
          rw[eq_empty_iff_forall_notMem]
          intro x
          by_contra hx'
          rw[mem_preimage'] at hx'
          simp at hx'
          obtain ⟨hx, hfx⟩ := hx'
          specialize fay x hx
          simp [← hfx] at fay
        rw[this]
        have : image f ∅ = ∅ := by
          ext x
          simp
        rw[this]
        symm
        by_contra con
        rw[eq_empty_iff_forall_notMem] at con
        specialize con y
        simp at con
-- Surjective -> equal
      intro suj S hSY
      set T := preimage f S with hT
      have ssuj : ∀ s ∈ S, ∃ t , f t = s ∧ t.val ∈ T := by
        intro s hS
        specialize suj s (by aesop) 
        obtain ⟨a, ha, haf⟩ := suj
        use ⟨a, ha⟩ 
        aesop
      ext s
      specialize ssuj s
      constructor
      . have tr := image_of_preimage f S
        rw[subset_def] at tr
        specialize tr s
        exact tr
      intro hs
      specialize ssuj hs
      simp
      obtain ⟨t, hft, htt⟩ := ssuj
      use t
      split_ands
      . use t.property
      exact htt

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.preimage_image_of_inj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ X → preimage f (image f S) = S) ↔ Function.Injective f := by
      simp[Function.Injective]
      constructor
      . 
      -- equal -> Inj
        contrapose!
        rintro ⟨x1,hx1,x2,hx2,fxx,xx⟩ 
        use {x1} 
        use by
          simp[subset_def]
          exact hx1
        have hT: image f {x1} = { (f ⟨x1, hx1⟩).val} := by
          ext t
          simp
          constructor
          . rintro ⟨hx1',hfx⟩ 
            rw[← hfx]
          rintro rfl
          use hx1
        rw[hT]
        have hx2p : x2 ∈ preimage f { (f ⟨x1, hx1⟩).val} := by
          simp
          use hx2
          rw[fxx]
        by_contra con
        have : x2 ∈ ({x1}: Set) := by
          rw[con] at hx2p
          exact hx2p
        simp at this
        symm at this
        contradiction
      intro inj S hS
      have base := preimage_of_image f S hS
      have target : preimage f (image f S) ⊆ S := by
        rw[subset_def]
        intro x
        rw[mem_preimage']
        rintro ⟨x,rfl,hfx⟩ 
        simp at hfx
        obtain ⟨x',⟨hx'X,hff⟩ , hx'S⟩ := hfx 
        specialize inj x.val x.property x' hx'X
        symm at hff
        rw[coe_inj] at hff
        simp[hff] at inj
        simp[inj,hx'S]
      set T := preimage f (image f S)
      exact subset_antisymm T S target base

/-- Helper lemma for Exercise 3.4.7. -/
@[simp]
lemma SetTheory.Set.mem_powerset' {S S' : Set} : (S': Object) ∈ S.powerset ↔ S' ⊆ S := by
  simp [mem_powerset]

/-- Another helper lemma for Exercise 3.4.7. -/
-- a function maps a subset of S into a set
-- the union of all these sets is exactly 
-- the union of all these sets = =
lemma SetTheory.Set.mem_union_powerset_replace_iff {S : Set} {P : S.powerset → Object → Prop} {hP : _} {x : Object} :
    x ∈ union (S.powerset.replace (P := P) hP) ↔
    ∃ (S' : S.powerset) (U : Set), P S' U ∧ x ∈ U := by
  grind [union_axiom, replacement_axiom]

/-- Exercise 3.4.7 -/
theorem SetTheory.Set.partial_functions {X Y:Set} :
    ∃ Z:Set, ∀ F:Object, F ∈ Z ↔ ∃ X' Y':Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f: X' → Y', F = f := by
      set PX := X.powerset with hPX
      set PY := Y.powerset with hPY
      -- X' ∈ PX and Y' ∈ PY
      -- all possible f : X' → Y' is a element of  Y' ^ X'
      -- Z is the union of all Y' ^ X'
      -- union it twice?
      -- Ok ,first of all, build a function which takes a fixed X'₀ 
      -- and generates the Union of all Y' ^ X'₀ 
      -- which is union PY .replace 
      set mapY : Set → Set := fun X₀ ↦ 
        union ( PY.replace (P:= fun y' u ↦ 
          ∃ Y' : Set , (Y':Object) = y' ∧ set_to_object (Y' ^ X₀) = u  
        ) ( by 
              simp_all
        ) ) with hmapY
       -- next ,for all X' in PX, and union them up
      set PFs : Set := union (
        PX.replace ( P := fun x' u ↦ 
          ∃ X' : Set, (X' : Object) = x' ∧ u = mapY X'
        ) 
          (by simp_all)
      )
      use PFs
      intro F
      constructor
      . 
        rw[mem_union_powerset_replace_iff]
        rintro ⟨ ⟨x',hx'⟩ , Uni,⟨X',hX',hUni⟩ ,hFUni⟩
        apply coe_eq at hUni 
        unfold mapY at hUni
        rw[hUni] at hFUni 
        rw[mem_union_powerset_replace_iff] at hFUni
        obtain ⟨ ⟨y' ,hy'⟩ , U ,⟨Y',hY',hXYU⟩ ,hFU⟩  :=hFUni
        apply coe_eq at hXYU
        use X', Y'
        simp at hX' hY'
        rw[← hX', mem_powerset'] at hx'
        rw[← hY', mem_powerset'] at hy'
        use hx' , hy'
        rw[← hXYU,powerset_axiom] at hFU
        obtain ⟨f,hFU⟩ := hFU
        use f
        exact hFU.symm
      rintro ⟨X',Y',hXX',hYY',f,hF⟩   
      rw[mem_union_powerset_replace_iff]
      set x' : PX := ⟨ (X' : Object), by rwa[← mem_powerset'] at hXX'⟩  with hXx'
      use x'
      set Uni := mapY X' with hUni
      use Uni
      split_ands
      . 
        use X'
      unfold Uni mapY
      rw[mem_union_powerset_replace_iff]
      set y' : PY := ⟨ (Y' : Object), by rwa[← mem_powerset'] at hYY'⟩  with hYy'
      use y'
      set U := Y' ^ X' with hXYU
      use U
      split_ands
      . 
        use Y'
      rw[hXYU,powerset_axiom]
      use f
      exact hF.symm

/--
  Exercise 3.4.8.  The point of this exercise is to prove it without using the
  pairwise union operation `∪`.
-/
theorem SetTheory.Set.union_pair_exists (X Y:Set) : ∃ Z:Set, ∀ x, x ∈ Z ↔ (x ∈ X ∨ x ∈ Y) := by
  set T := union {(X : Object), (Y: Object)} with hT
  use T
  intro x
  rw[hT]
  rw[union_axiom]
  constructor
  . 
    rintro ⟨S,hx,hs⟩ 
    rw[mem_pair]at hs
    obtain hsa | hsa := hs
    <;> apply coe_eq at hsa
    <;> rw[← hsa]
    <;> tauto
  rintro (case| case)
  map_tacs[use X; use Y]
  all_goals
    simp
    assumption

/-- Exercise 3.4.9 -/
theorem SetTheory.Set.iInter'_insensitive {I:Set} (β β':I) (A: I → Set) :
    iInter' I β A = iInter' I β' A := by
      ext x
      simp[iInter']
      rintro h
      constructor
      <;> intro
      map_tacs[specialize h β'.val β'.property ;specialize h β.val β.property ]
      all_goals 
        tauto

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_iUnion {I J:Set} (A: (I ∪ J:Set) → Set) :
    iUnion I (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∪ iUnion J (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iUnion (I ∪ J) A := by
      ext x
      simp[mem_iUnion]
      constructor
      . 
        rintro (h|h)
        <;> obtain ⟨a, ha,hxa⟩ := h 
        <;> use a
        <;> use (by tauto)
      rintro ⟨a,⟨(hai|haj),hax⟩ ⟩ 
      map_tacs[left;right]
      all_goals
        use a
        use by assumption

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_of_nonempty {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) : I ∪ J ≠ ∅ := by
  simp[eq_empty_iff_forall_notMem] at hJ ⊢
  obtain ⟨x,hxj⟩  := hJ
  use x
  tauto

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.inter_iInter {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) (A: (I ∪ J:Set) → Set) :
    iInter I hI (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∩ iInter J hJ (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iInter (I ∪ J) (union_of_nonempty hI hJ) A := by
      ext x
      simp only [iInter, mem_inter]
      set bi := nonempty_choose hI
      obtain ⟨bi, hbi⟩ := bi 
      set bj := nonempty_choose hJ 
      obtain ⟨bj, hbj⟩ := bj
      set bij := nonempty_choose (union_of_nonempty hI hJ)
      obtain ⟨bij, hbij⟩ := bij
      have hbi' : bi ∈ I ∪ J := by aesop
      have hbj' : bj ∈ I ∪ J := by aesop
      have hinsI := iInter'_insensitive ⟨bij, hbij⟩ ⟨bi, hbi'⟩ A  
      have hinsJ := iInter'_insensitive ⟨bij, hbij⟩ ⟨bj, hbj'⟩ A  
      constructor
      . 
        simp[hinsI]
        rintro hxi hxI hxj hxJ
        split_ands
        . assumption
        intro a
        specialize hxI a
        specialize hxJ a
        rintro (hai| haj)
        map_tacs[specialize hxI hai; specialize hxJ haj]
        all_goals
          assumption
      simp
      intro xaij xAij
      split_ands
      <;> try tauto
      . 
        specialize xAij bj
        specialize xAij (by tauto)
        exact xAij
      intro a
      intro haj
      specialize xAij a (by tauto)
      exact xAij

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iUnion {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iUnion I A = iInter I hI (fun α ↦ X \ A α) := by
      ext x
      rw[mem_sdiff,mem_iInter]
      simp only [mem_iUnion]
      push_neg
      simp
      constructor
      . 
        rintro ⟨hx,hax⟩ a ha
        specialize hax a ha
        tauto
      intro hax
      split_ands
      . 
        have b := nonempty_choose hI
        obtain ⟨b,hb⟩ := b
        specialize hax b hb
        tauto
      intro a ha
      specialize hax a ha
      tauto


/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iInter {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iInter I hI A = iUnion I (fun α ↦ X \ A α) := by
      ext x
      rw[mem_sdiff,mem_iUnion]
      simp only [mem_iInter]
      push_neg
      constructor
      . 
        rintro ⟨hx, ⟨a,hxa⟩ ⟩ 
        use a
        simp
        tauto
      rintro ⟨i,hai⟩ 
      rw[mem_sdiff] at hai
      constructor
      . tauto
      use i
      tauto

end Chapter3
