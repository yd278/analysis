import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_4

/-!
# Analysis I, Section 3.5

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.   When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Ordered pairs and n-tuples
- Cartesian products and n-fold products
- Finite choice
--/

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/-- Definition 3.5.1 (Ordered pair) -/
@[ext]
structure OrderedPair where
  fst: Object
  snd: Object

#check OrderedPair.ext

/-- Definition 3.5.1 (Ordered pair) -/
theorem OrderedPair.eq (x y x' y':Object) : (⟨ x, y ⟩:OrderedPair) = (⟨ x', y' ⟩:OrderedPair) ↔ x = x' ∧ y = y' := by aesop

/-- Exercise 3.5.1 -/
abbrev OrderedPair.toObject : OrderedPair ↪ Object where
  toFun p := ({ (({p.fst}:Set):Object), (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by sorry

instance OrderedPair.inst_coeObject : Coe OrderedPair Object where
  coe := OrderedPair.toObject

/-- A technical operation, turning a object `x` and a set `Y` to a set `{x} × Y`, needed to define the full Cartesian product-/
abbrev SetTheory.Set.slice (x:Object) (Y:Set) : Set := Y.replace (P := fun y z ↦ z = (⟨x, y⟩:OrderedPair)) (by
  intro y z z' ⟨ hz, hz'⟩
  simp at hz hz'
  rw [hz, hz'])

theorem SetTheory.Set.mem_slice (x z:Object) (Y:Set) : z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y:Y, z = (⟨x, y⟩:OrderedPair) :=  replacement_axiom _ _

/-- Definition 3.5.2 (Cartesian product) -/
abbrev SetTheory.Set.cartesian (X Y:Set) : Set := union (X.replace (P := fun x z ↦ z = slice x Y) (by
  intro x z z' ⟨ hz, hz' ⟩
  simp at hz hz'
  rw [hz, hz']))

/-- This instance enables the ×ˢ notation for Cartesian product. -/
instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

theorem SetTheory.Set.mem_cartesian (z:Object) (X Y:Set) : z ∈ X ×ˢ Y ↔ ∃ x:X, ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := by
  simp only [SProd.sprod, union_axiom]
  constructor
  . intro h
    obtain ⟨ S, hz, hS ⟩ := h
    rw [replacement_axiom] at hS
    obtain ⟨ x, hx ⟩ := hS
    simp at hx
    rw [hx] at hz
    rw [mem_slice] at hz
    obtain ⟨ y, rfl ⟩ := hz
    use x, y
  intro h
  obtain ⟨ x, y, rfl ⟩ := h
  use slice x Y
  constructor
  . rw [mem_slice]
    use y
  rw [replacement_axiom]
  use x

abbrev SetTheory.Set.curry {X Y Z:Set} (f: X ×ˢ Y → Z) : X → Y → Z := fun x y ↦ f ⟨ (⟨ x, y ⟩:OrderedPair), by rw [mem_cartesian]; use x, y ⟩

noncomputable abbrev SetTheory.Set.fst {X Y:Set} (z:X ×ˢ Y) : X := (show ∃ x:X, ∃ y:Y, z.val = (⟨ x, y ⟩:OrderedPair) by exact (mem_cartesian _ _ _).mp z.property).choose

noncomputable abbrev SetTheory.Set.snd {X Y:Set} (z:X ×ˢ Y) : Y := (show ∃ y:Y, ∃ x:X, z.val = (⟨ x, y ⟩:OrderedPair) by rw [exists_comm]; exact (mem_cartesian _ _ _).mp z.property).choose

theorem SetTheory.Set.pair_eq_fst_snd {X Y:Set} (z:X ×ˢ Y) : z.val = (⟨ fst z, snd z ⟩:OrderedPair) := by
  obtain ⟨ y, hy ⟩ := ((mem_cartesian _ _ _).mp z.property).choose_spec
  obtain ⟨ x, hx ⟩ := (exists_comm.mp ((mem_cartesian _ _ _).mp z.property)).choose_spec
  change z.val = (⟨ fst z, y ⟩:OrderedPair) at hy
  change z.val = (⟨ x, snd z ⟩:OrderedPair) at hx
  rw [hx] at hy ⊢
  simp only [EmbeddingLike.apply_eq_iff_eq, OrderedPair.eq] at hy ⊢
  simp [hy.1]

noncomputable abbrev SetTheory.Set.uncurry {X Y Z:Set} (f: X → Y → Z) : X ×ˢ Y → Z := fun z ↦ f (fst z) (snd z)

theorem SetTheory.Set.curry_uncurry {X Y Z:Set} (f: X → Y → Z) : curry (uncurry f) = f := by sorry

theorem SetTheory.Set.uncurry_curry {X Y Z:Set} (f: X ×ˢ Y → Z) : uncurry (curry f) = f := by sorry



end Chapter3
