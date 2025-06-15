import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.4

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.   When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Images and inverse images of (Mathlib) functions, within the framework of Section 3.1 set theory.  (The Section 3.2 functions are now deprecated and will not be used further.)

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
theorem SetTheory.Set.image_eq_image {X Y:Set} (f:X → Y) (S: Set) (y: Object) : y ∈ image f S ↔ y ∈ Subtype.val '' (f '' {x | x.val ∈ S}) := by sorry


/-- Example 3.4.2 -/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2*n:ℕ)

theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1,2,3} = {2,4,6} := by sorry






end Chapter3
