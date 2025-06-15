import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.4

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.   When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Images and inverse images of (Mathlib) functions, within the framework of Section 3.1 set theory.  (The Section 3.2 functions are now deprecated and will not be used further.)
- Connection with Mathlib's image `f '' S` and preimage `f ⁻¹' S` notions.
-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.4.1.  Interestingly, the definition does not require S to be a subset of X. -/
abbrev SetTheory.Set.image {X Y:Set} (f:X → Y) (S: Set) : Set := X.replace (P := fun x y ↦ y = f x ∧ x.val ∈ S) (by
  intro x y y' ⟨ hy, hy' ⟩
  simp at hy hy'
  rw [hy.1, hy'.1])

/-- Definition 3.4.1 -/
theorem SetTheory.Set.mem_image {X Y:Set} (f:X → Y) (S: Set) (y:Object) : y ∈ image f S ↔ ∃ x:X, x.val ∈ S ∧ f x = y := by
  rw [SetTheory.Set.replacement_axiom]
  apply exists_congr; intro x
  tauto

/-- Alternate definition of image using axiom of specification -/
theorem SetTheory.Set.image_eq_specify {X Y:Set} (f:X → Y) (S: Set) : image f S = Y.specify (fun y ↦ ∃ x:X, x.val ∈ S ∧ f x = y) := by sorry

/-- Connection with Mathlib's notion of image.  Note the need to utilize the `Subtype.val` coercion to make everything type consistent. -/
theorem SetTheory.Set.image_eq_image {X Y:Set} (f:X → Y) (S: Set): (image f S: _root_.Set Object) = Subtype.val '' (f '' {x | x.val ∈ S}) := by sorry


/-- Example 3.4.2 -/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2*n:ℕ)

theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1,2,3} = {2,4,6} := by sorry

/-- Example 3.4.3 is written using Mathlib's notion of image -/
example : (fun n:ℤ ↦ n^2) '' {-1,0,1,2} = {0,1,4} := by sorry

theorem SetTheory.Set.mem_image_of_eval {X Y:Set} (f:X → Y) (S: Set) (x:X) : x.val ∈ S → (f x).val ∈ image f S := by sorry

theorem SetTheory.Set.mem_image_of_eval_counter : ∃ (X Y:Set) (f:X → Y) (S: Set) (x:X), ¬ ((f x).val ∈ image f S → x.val ∈ S) := by sorry

/-- Definition 3.4.4 (inverse images).  Again, it is not required that U be a subset of Y. -/
abbrev SetTheory.Set.preimage {X Y:Set} (f:X → Y) (U: Set) : Set := X.specify (P := fun x ↦ (f x).val ∈ U)

theorem SetTheory.Set.mem_preimage {X Y:Set} (f:X → Y) (U: Set) (x:X) : x.val ∈ preimage f U ↔ (f x).val ∈ U := by
  rw [specification_axiom']

/-- Connection with Mathlib's notion of preimage. -/
theorem SetTheory.Set.preimage_eq {X Y:Set} (f:X → Y) (U: Set) : ((preimage f U): _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) := by sorry

/-- Example 3.4.5 -/
theorem SetTheory.Set.preimage_f_3_4_2 : preimage f_3_4_2 {2,4,6} = {1,2,3} := by sorry

theorem SetTheory.Set.image_preimage_f_3_4_2 : image f_3_4_2 (preimage f_3_4_2 {1,2,3}) ≠ {1,2,3} := by sorry

/-- Example 3.4.6 (using the Mathlib notinon of preimage) -/
example : (fun n:ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by sorry

example : (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) ≠ {-1,0,1,2} := by sorry


end Chapter3
