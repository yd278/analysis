import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.2: Russell's paradox

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

This section is mostly optional, though it does make explicit the axiom of foundation which is
used in a minor role in an exercise in Section 3.5.

Main constructions and results of this section:

- Russell's paradox (ruling out the axiom of universal specification).
- The axiom of regularity (foundation) - an axiom designed to avoid Russell's paradox.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/-- Axiom 3.8 (Universal specification) -/
abbrev axiom_of_universal_specification : Prop :=
  ∀ P : Object → Prop, ∃ A : Set, ∀ x : Object, x ∈ A ↔ P x

theorem Russells_paradox : ¬ axiom_of_universal_specification := by
  -- This proof is written to follow the structure of the original text.
  intro h
  set P : Object → Prop := fun x ↦ ∃ X:Set, x = X ∧ x ∉ X
  choose Ω hΩ using h P
  by_cases h: (Ω:Object) ∈ Ω
  . have : P (Ω:Object) := (hΩ _).mp h
    obtain ⟨ Ω', ⟨ hΩ1, hΩ2⟩ ⟩ := this
    simp at hΩ1
    rw [←hΩ1] at hΩ2
    contradiction
  have : P (Ω:Object) := by use Ω
  rw [←hΩ] at this
  contradiction

/-- Axiom 3.9 (Regularity) -/
theorem SetTheory.Set.axiom_of_regularity {A:Set} (h: A ≠ ∅) :
    ∃ x:A, ∀ S:Set, x.val = S → Disjoint S A := by
  choose x h h' using regularity_axiom A (nonempty_def h)
  use ⟨x, h⟩
  intro S hS; specialize h' S hS
  rw [disjoint_iff, eq_empty_iff_forall_notMem]
  contrapose! h'; simp at h'
  aesop

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the empty set.
-/
theorem SetTheory.Set.emptyset_exists (h: axiom_of_universal_specification):
    ∃ (X:Set), ∀ x, x ∉ X := by
     let P (x : Object ) := False 
     have set := h P
     choose A hA using set
     use A
     intro x
     specialize hA x
     by_contra h
     have px := hA.mp h
     unfold P at px
     contradiction

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the singleton set.
-/
theorem SetTheory.Set.singleton_exists (h: axiom_of_universal_specification) (x:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x := by
      let P (y:Object) := y = x 
      have set := h P
      choose A hA using set
      use A


/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the pair set.
-/
theorem SetTheory.Set.pair_exists (h: axiom_of_universal_specification) (x₁ x₂:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
      let P (y:Object) := y = x₁ ∨ y = x₂ 
      have set := h P
      choose A hA using set
      use A


/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the union operation.
-/
theorem SetTheory.Set.union_exists (h: axiom_of_universal_specification) (A B:Set):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
      let P (y:Object) := y ∈ A ∨ y ∈ B
      have set := h P
      choose A hA using set
      use A

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the specify operation.
-/
theorem SetTheory.Set.specify_exists (h: axiom_of_universal_specification) (A:Set) (P: A → Prop):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨ z, h ⟩ := by
      let Q (y:Object) := ∃ h : y ∈ A, P ⟨ y, h ⟩
      have set := h Q
      choose A hA using set
      use A


/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the replace operation.
-/
theorem SetTheory.Set.replace_exists (h: axiom_of_universal_specification) (A:Set)
  (P: A → Object → Prop) (hP: ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z:Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
      let Q (y:Object) := ∃ a :A , P a y 
      have set := h Q
      choose A hA using set
      use A

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_self (A:Set) : (A:Object) ∉ A := by
  have : ∃ x, x ∈ ({(A:Object)} : Set ):= by
    use (A:Object)
    rw[mem_singleton]
  have reg := regularity_axiom (singleton (A:Object) ) this
  choose x x_sing x_set  using reg
  specialize x_set  A 
  rw[singleton_axiom x (A:Object)] at x_sing
  have res := x_set x_sing
  push_neg at res
  specialize res (A:Object)
  rw[singleton_axiom] at res
  simp at res
  exact res

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_mem (A B:Set) : (A:Object) ∉ B ∨ (B:Object) ∉ A := by
  by_contra! h
  have ⟨h1, h2⟩ := h
  have non_empty : ∃ x, x ∈ ({ (A:Object), (B:Object)}:Set) := by
    use (A:Object)
    rw[mem_pair]
    tauto
  have reg := regularity_axiom ({ (A:Object), (B:Object)}:Set) non_empty
  choose x x_pair x_set using reg
  change x ∈  ({ (A:Object), (B:Object)}:Set) at x_pair
  rw[mem_pair] at x_pair
  obtain case_A | case_B := x_pair
  . 
    specialize x_set A
    replace x_set := x_set case_A
    push_neg at x_set
    specialize x_set B
    have:  mem (B:Object) {(A:Object), (B:Object)} := by
      change (B:Object) ∈ ({(A:Object), (B:Object)}: Set)  
      rw[mem_pair] 
      tauto
    replace x_set := x_set this
    change (B:Object) ∉ A at x_set
    contradiction
  . 
    specialize x_set B
    replace x_set := x_set case_B
    push_neg at x_set
    specialize x_set A
    have:  mem (A:Object) {(A:Object), (B:Object)} := by
      change (A:Object) ∈ ({(A:Object), (B:Object)}: Set)  
      rw[mem_pair] 
      tauto
    replace x_set := x_set this
    change (A:Object) ∉ B at x_set
    contradiction

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔
  ∃ (U:Set), ∀ x, x ∈ U := by
    unfold axiom_of_universal_specification 
    constructor
    . 
      intro a
      let P (x : Object) := True
      have set := a P
      choose u pu using set
      use u
      intro x
      specialize pu x
      replace pu := pu.mpr
      unfold P at pu
      tauto
    intro a
    choose U hu using a
    intro P
    let P' (x : U ) := P x.val
    use specify U P' 
    intro x
    rw[specification_axiom'']
    constructor
    . intro ⟨a, b⟩ 
      unfold P' at b
      simp at b
      exact b
    intro px
    use (hu x)

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U:Set), ∀ (x:Object), x ∈ U := by
  by_contra h
  rw[← univ_iff] at h
  have nh := Russells_paradox
  contradiction


end Chapter3
