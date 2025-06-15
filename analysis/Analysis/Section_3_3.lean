import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.3

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.   When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- A notion of function, adapted to the set theory of Section 3.1
-/

namespace Chapter3

export SetTheory (Set Object nat nat_equiv)

variable [SetTheory]

/-- Definition 3.3.1. `Function X Y` is the structure of functions from `X` to `Y`. -/
@[ext]
structure Function (X Y: Set) where
  P : X → Y → Prop
  unique : ∀ x: X, ∃! y: Y, P x y

#check Function.mk

/-- Converting a Chapter 3 function to a Mathlib function. The Chapter 3 definition of a function was nonconstructive, so we have to use the axiom of choice here.  -/
noncomputable instance Function.inst_coefn (X Y: Set)  : CoeFun (Function X Y) (fun _ ↦ X → Y) where
  coe := fun f x ↦ Classical.choose (f.unique x)

noncomputable abbrev Function.to_fn {X Y: Set} (f: Function X Y) (x:X) : Y := f x

theorem Function.to_fn_eval {X Y: Set} (f: Function X Y) (x:X) : f.to_fn x = f x := rfl

/-- Converting a Mathlib function to a Chapter 3 function -/
abbrev Function.mk_fn {X Y: Set} (f: X → Y) : Function X Y :=
  Function.mk (fun x y ↦ y = f x) (by
    intro x
    apply ExistsUnique.intro (f x)
    . rfl
    intro y h
    assumption)


/-- Definition 3.3.1 -/
theorem Function.eval {X Y: Set} (f: Function X Y) (x: X) (y: Y) : y = f x ↔ f.P x y := by
  constructor
  . intro h
    subst h
    exact (Classical.choose_spec (f.unique x)).1
  intro h
  apply (Classical.choose_spec (f.unique x)).2
  assumption

@[simp]
theorem Function.eval_of {X Y: Set} (f: X → Y) (x:X) : (Function.mk_fn f) x = f x := by
  symm; rw [eval]


/-- Example 3.3.2.  Due to the fact that `nat` and ℕ -/
abbrev P_3_3_2a : nat → nat → Prop := fun x y ↦ (y:ℕ) = (x:ℕ)+1

theorem SetTheory.Set.P_3_3_2a_existsUnique (x: nat) : ∃! y: nat, P_3_3_2a x y := by
  apply ExistsUnique.intro ((x+1:ℕ):nat)
  . simp [P_3_3_2a]
  intro y h
  simp only [P_3_3_2a, Equiv.symm_apply_eq] at h
  assumption

abbrev SetTheory.Set.f_3_3_2a : Function nat nat := Function.mk P_3_3_2a P_3_3_2a_existsUnique

theorem SetTheory.Set.f_3_3_2a_eval (x y: nat) : y = f_3_3_2a x ↔ (y:ℕ) = (x+1:ℕ) := Function.eval _ _ _


theorem SetTheory.Set.f_3_3_2a_eval' (n: ℕ) : f_3_3_2a (n:nat) = (n+1:ℕ) := by
  symm
  simp only [f_3_3_2a_eval, nat_equiv_coe_of_coe]

theorem SetTheory.Set.f_3_3_2a_eval'' : f_3_3_2a (nat_equiv 4) = nat_equiv 5 :=  f_3_3_2a_eval' 4

theorem SetTheory.Set.f_3_3_2a_eval''' (n:ℕ) : f_3_3_2a (nat_equiv (2*n+3)) = nat_equiv (2*n+4) := by
  convert f_3_3_2a_eval' _

abbrev SetTheory.Set.P_3_3_2b : nat → nat → Prop := fun x y ↦ (y+1:ℕ) = (x:ℕ)

theorem SetTheory.Set.not_P_3_3_2b_existsUnique : ¬ ∀ x, ∃! y: nat, P_3_3_2b x y := by
  by_contra h
  replace h := ExistsUnique.exists (h (0:nat))
  obtain ⟨ n, hn ⟩ := h
  have : ((0:nat):ℕ) = 0 := by simp [OfNat.ofNat]
  simp [P_3_3_2b, this] at hn

abbrev SetTheory.Set.P_3_3_2c : (nat \ {(0:Object)}: Set) → nat → Prop := fun x y ↦ ((y+1:ℕ):Object) = x

theorem SetTheory.Set.P_3_3_2c_existsUnique (x: (nat \ {(0:Object)}: Set)) : ∃! y: nat, P_3_3_2c x y := by
-- Some technical unpacking here due to the subtle distinctions between the `Object` type, sets converted to subtypes of `Object`, and subsets of those sets.
  obtain ⟨ x, hx ⟩ := x
  simp at hx
  obtain ⟨ hx1, hx2⟩ := hx
  set n := ((⟨ x, hx1 ⟩:nat):ℕ)
  have : x = (n:nat) := by simp [n]
  simp [P_3_3_2c, this, SetTheory.Object.ofnat_eq'] at hx2 ⊢
  replace hx2 : n = (n-1) + 1 := by omega
  apply ExistsUnique.intro ((n-1:ℕ):nat)
  . simp [←hx2]
  intro y hy
  set m := (y:ℕ)
  simp [←hy, m]

abbrev SetTheory.Set.f_3_3_2c : Function (nat \ {(0:Object)}: Set) nat := Function.mk P_3_3_2c P_3_3_2c_existsUnique

theorem SetTheory.Set.f_3_3_2c_eval (x: (nat \ {(0:Object)}: Set)) (y: nat) : y = f_3_3_2c x ↔ ((y+1:ℕ):Object) = x := Function.eval _ _ _

/-- Create a version of anon-zero `n` inside `nat \ {0}` for any natural number n. -/
abbrev SetTheory.Set.coe_nonzero (n:ℕ) (h: n ≠ 0): (nat \ {(0:Object)}: Set) := ⟨ ((n:ℕ):Object), by simp [SetTheory.Object.ofnat_eq',h]; rw [←SetTheory.Object.ofnat_eq]; exact Subtype.property _ ⟩

theorem SetTheory.Set.f_3_3_2c_eval' (n: ℕ) : f_3_3_2c (coe_nonzero (n+1) (by positivity)) = n := by
  symm; rw [f_3_3_2c_eval]; simp

theorem SetTheory.Set.f_3_3_2c_eval'' : f_3_3_2c (coe_nonzero 4 (by positivity)) = 3 := by convert f_3_3_2c_eval' 3

theorem SetTheory.Set.f_3_3_2c_eval''' (n:ℕ) : f_3_3_2c (coe_nonzero (2*n+3) (by positivity)) = (2*n+2:ℕ) := by convert f_3_3_2c_eval' (2*n+2)




end Chapter3
