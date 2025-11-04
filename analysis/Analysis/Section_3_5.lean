import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_4

/-!
# Analysis I, Section 3.5: Cartesian products

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordered pairs and n-tuples.
- Cartesian products and n-fold products.
- Finite choice.
- Connections with Mathlib counterparts such as `Set.pi` and `Set.prod`.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

open SetTheory.Set

/-- Definition 3.5.1 (Ordered pair).  One could also have used `Object × Object` to
define `OrderedPair` here. -/
@[ext]
structure OrderedPair where
  fst: Object
  snd: Object

#check OrderedPair.ext

/-- Definition 3.5.1 (Ordered pair) -/
@[simp]
theorem OrderedPair.eq (x y x' y' : Object) :
    (⟨ x, y ⟩ : OrderedPair) = (⟨ x', y' ⟩ : OrderedPair) ↔ x = x' ∧ y = y' := by aesop

/-- Helper lemma for Exercise 3.5.1 -/
lemma SetTheory.Set.pair_eq_singleton_iff {a b c: Object} : {a, b} = ({c}: Set) ↔
    a = c ∧ b = c := by
      constructor
      . 
        intro h
        simp[SetTheory.Set.ext_iff] at h
        have hac := h a
        have hbc := h b
        tauto 
      intro ⟨hac, hbc⟩ 
      ext x
      rw[hac,hbc]
      simp

lemma SetTheory.Set.singleton_eq_singleton_iff {a b:Object} : {a} = ({b} : Set) ↔ a = b := by
  constructor
  . 
    intro h
    rw[SetTheory.Set.ext_iff] at h
    specialize h a
    simp at h
    exact h
  intro h
  rw[h]

lemma SetTheory.Set.singleton_eq_pair_iff {a b c:Object} :{c} = ({a,b}:Set) ↔ a = c ∧ b = c := by
  rw[← pair_eq_singleton_iff]
  constructor <;> intro h <;> symm <;> exact h

lemma SetTheory.Set.pair_eq_pair_iff {a b c d:Object} :  
    ({a,b}:Set) = {c,d} ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
      constructor
      .
        intro h
        exact pair_eq_pair h
      rintro (⟨h1, h2⟩|⟨h1,h2⟩ ) 
      <;> rw[h1,h2]
      ext x
      simp
      tauto

/-- Exercise 3.5.1, first part -/
def OrderedPair.toObject : OrderedPair ↪ Object where
  toFun p := ({ (({p.fst}:Set):Object), (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by
    simp[Function.Injective]
    intro p1 p2
    intro h12
    simp[SetTheory.Set.ext_iff] at h12
    have ffst := h12 (({p1.fst}:Set):Object)
    simp at ffst
    have fsnd := h12 (SetTheory.set_to_object {p1.fst, p1.snd})
    simp at fsnd
    obtain (hfstA| hfstB) := ffst <;>
    obtain (hsndA | hsndB) := fsnd <;>
    ext 
    all_goals
      simp_all [singleton_eq_singleton_iff, pair_eq_singleton_iff, singleton_eq_pair_iff,pair_eq_pair_iff]
    obtain (h1|h2) := hsndB
    tauto
    have ⟨h21,h22⟩ := h2
    simp_all

instance OrderedPair.inst_coeObject : Coe OrderedPair Object where
  coe := toObject

/--
  A technical operation, turning a object `x` and a set `Y` to a set `{x} × Y`, needed to define
  the full Cartesian product
-/
abbrev SetTheory.Set.slice (x:Object) (Y:Set) : Set :=
  Y.replace (P := fun y z ↦ z = (⟨x, y⟩:OrderedPair)) (by grind)

@[simp]
theorem SetTheory.Set.mem_slice (x z:Object) (Y:Set) :
    z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := replacement_axiom _ _

/-- Definition 3.5.4 (Cartesian product) -/
abbrev SetTheory.Set.cartesian (X Y:Set) : Set :=
  union (X.replace (P := fun x z ↦ z = slice x Y) (by grind))

/-- This instance enables the ×ˢ notation for Cartesian product. -/
instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

example (X Y:Set) : X ×ˢ Y = SetTheory.Set.cartesian X Y := rfl

@[simp]
theorem SetTheory.Set.mem_cartesian (z:Object) (X Y:Set) :
    z ∈ X ×ˢ Y ↔ ∃ x:X, ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := by
  simp only [SProd.sprod, union_axiom]; constructor
  . intro ⟨ S, hz, hS ⟩; rw [replacement_axiom] at hS; obtain ⟨ x, hx ⟩ := hS
    use x; simp_all
  rintro ⟨ x, y, rfl ⟩; use slice x Y; refine ⟨ by simp, ?_ ⟩
  rw [replacement_axiom]; use x

noncomputable abbrev SetTheory.Set.fst {X Y:Set} (z:X ×ˢ Y) : X :=
  ((mem_cartesian _ _ _).mp z.property).choose

noncomputable abbrev SetTheory.Set.snd {X Y:Set} (z:X ×ˢ Y) : Y :=
  (exists_comm.mp ((mem_cartesian _ _ _).mp z.property)).choose

theorem SetTheory.Set.pair_eq_fst_snd {X Y:Set} (z:X ×ˢ Y) :
    z.val = (⟨ fst z, snd z ⟩:OrderedPair) := by
  have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y, hy: z.val = (⟨ fst z, y ⟩:OrderedPair)⟩ := this.choose_spec
  obtain ⟨ x, hx: z.val = (⟨ x, snd z ⟩:OrderedPair)⟩ := (exists_comm.mp this).choose_spec
  simp_all [EmbeddingLike.apply_eq_iff_eq]

/-- This equips an `OrderedPair` with proofs that `x ∈ X` and `y ∈ Y`. -/
def SetTheory.Set.mk_cartesian {X Y:Set} (x:X) (y:Y) : X ×ˢ Y :=
  ⟨(⟨ x, y ⟩:OrderedPair), by simp⟩

@[simp]
theorem SetTheory.Set.fst_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    fst (mk_cartesian x y) = x := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y', hy: z.val = (⟨ fst z, y' ⟩:OrderedPair) ⟩ := this.choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hy.1]

@[simp]
theorem SetTheory.Set.snd_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    snd (mk_cartesian x y) = y := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ x', hx: z.val = (⟨ x', snd z ⟩:OrderedPair) ⟩ := (exists_comm.mp this).choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hx.2]

@[simp]
theorem SetTheory.Set.mk_cartesian_fst_snd_eq {X Y: Set} (z: X ×ˢ Y) :
    (mk_cartesian (fst z) (snd z)) = z := by
  rw [mk_cartesian, Subtype.mk.injEq, pair_eq_fst_snd]

/--
  Connections with the Mathlib set product, which consists of Lean pairs like `(x, y)`
  equipped with a proof that `x` is in the left set, and `y` is in the right set.
  Lean pairs like `(x, y)` are similar to our `OrderedPair`, but more general.
-/
noncomputable abbrev SetTheory.Set.prod_equiv_prod (X Y:Set) :
    ((X ×ˢ Y):_root_.Set Object) ≃ (X:_root_.Set Object) ×ˢ (Y:_root_.Set Object) where
  toFun z := ⟨(fst z, snd z), by simp⟩
  invFun z := mk_cartesian ⟨z.val.1, z.prop.1⟩ ⟨z.val.2, z.prop.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- Example 3.5.5 -/
example : ({1, 2}: Set) ×ˢ ({3, 4, 5}: Set) = ({
  ((mk_cartesian (1: Nat) (3: Nat)): Object),
  ((mk_cartesian (1: Nat) (4: Nat)): Object),
  ((mk_cartesian (1: Nat) (5: Nat)): Object),
  ((mk_cartesian (2: Nat) (3: Nat)): Object),
  ((mk_cartesian (2: Nat) (4: Nat)): Object),
  ((mk_cartesian (2: Nat) (5: Nat)): Object)
}: Set) := by ext; aesop

/-- Example 3.5.5 / Exercise 3.6.5. There is a bijection between `X ×ˢ Y` and `Y ×ˢ X`. -/
noncomputable abbrev SetTheory.Set.prod_commutator (X Y:Set) : X ×ˢ Y ≃ Y ×ˢ X where
  toFun := fun z ↦ 
  ⟨(⟨ snd z, fst z⟩:OrderedPair) , by simp ⟩  
  invFun := fun z ↦ 
  ⟨(⟨ snd z, fst z⟩:OrderedPair) , by simp ⟩  
  left_inv z := by
    rw[← mk_cartesian_fst_snd_eq z,mk_cartesian ]
    simp
  right_inv z := by
    rw[← mk_cartesian_fst_snd_eq z,mk_cartesian ]
    simp

/-- Example 3.5.5. A function of two variables can be thought of as a function of a pair. -/
noncomputable abbrev SetTheory.Set.curry_equiv {X Y Z:Set} : (X → Y → Z) ≃ (X ×ˢ Y → Z) where
  toFun f z := f (fst z) (snd z)
  invFun f x y := f ⟨ (⟨ x, y ⟩:OrderedPair), by simp ⟩
  left_inv _ := by simp
  right_inv _ := by simp [←pair_eq_fst_snd]

/-- Definition 3.5.6.  The indexing set `I` plays the role of `{ i : 1 ≤ i ≤ n }` in the text.
    See Exercise 3.5.10 below for some connections betweeen this concept and the preceding notion
    of Cartesian product and ordered pair.  -/
-- tuple is essentially a function
-- x is I → X indeed, hence ,given i, choose a element xᵢ  in Xᵢ 
-- so the tuple itself is an objectified function which 
-- takes x, wrapped it, change the return type from subType Xᵢ to subType (Bigunion of Xᵢ's)
-- it can also be seen as a series T, Tᵢ is `tuple x i`


abbrev SetTheory.Set.tuple {I:Set} {X: I → Set} (x: ∀ i, X i) : Object :=
  ((fun i ↦ ⟨ x i, by rw [mem_iUnion]; use i; exact (x i).property ⟩):I → iUnion I X)


/-- Definition 3.5.6 -/
-- before specification, it's all possible functions mapping i to all possible elements in bigUnion Xᵢ 
-- after that ,i can only map to elements in Xᵢ but still as a subtype of the bigunion

abbrev SetTheory.Set.iProd {I: Set} (X: I → Set) : Set :=
  ((iUnion I X)^I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)

/-- Definition 3.5.6 -/
theorem SetTheory.Set.mem_iProd {I: Set} {X: I → Set} (t:Object) :
    t ∈ iProd X ↔ ∃ x: ∀ i, X i, t = tuple x := by
  simp only [iProd, specification_axiom'']; constructor
  . intro ⟨ ht, x, h ⟩; use x
  intro ⟨ x, hx ⟩
  have h : t ∈ (I.iUnion X)^I := by simp [hx]
  use h, x

theorem SetTheory.Set.tuple_mem_iProd {I: Set} {X: I → Set} (x: ∀ i, X i) :
    tuple x ∈ iProd X := by rw [mem_iProd]; use x

@[simp]
theorem SetTheory.Set.tuple_inj {I:Set} {X: I → Set} (x y: ∀ i, X i) :
    tuple x = tuple y ↔ x = y := by
      constructor
      . 
        simp
        intro hf
        ext i
        have hp:=congrArg (fun f => f i) hf 
        simp at hp
        exact hp
      intro h
      rw[h]

/-- Example 3.5.8. There is a bijection between `(X ×ˢ Y) ×ˢ Z` and `X ×ˢ (Y ×ˢ Z)`. -/
noncomputable abbrev SetTheory.Set.prod_associator (X Y Z:Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun p := mk_cartesian (fst (fst p)) (mk_cartesian (snd (fst p)) (snd p))
  invFun p := mk_cartesian (mk_cartesian (fst p) (fst (snd p))) (snd (snd p))
  left_inv _ := by simp
  right_inv _ := by simp

/--
  Example 3.5.10. I suspect most of the equivalences will require classical reasoning and only be
  defined non-computably, but would be happy to learn of counterexamples.
-/
noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i:Object) (X:Set) :
    iProd (fun _:({i}:Set) ↦ X) ≃ X where
  toFun tup := (((mem_iProd _).mp tup.property).choose) ⟨i, by simp⟩ 
  invFun x :=  ⟨tuple (fun _ ↦ x),by rw[mem_iProd] ;use (fun _ ↦ x)⟩ 
  left_inv tup := by
    have spec :=(((mem_iProd _).mp tup.property).choose_spec) 
    ext
    rw[spec,tuple_inj]
    simp
    funext i'
    have : i' = ⟨i, by simp⟩ := by
      have := i'.property
      simp at this
      ext
      simp
      exact this
    rw[this]
  right_inv x := by
    simp
    generalize_proofs ex hi
    have spec := ex.choose_spec
    rw[tuple_inj] at spec
    simp [← spec]

abbrev SetTheory.Set.empty_tuple  {X: (∅:Set)  → Set}  : iProd X := 
  let fx : (i : (∅ : Set)) → (X i) := by
      intro ⟨i, hi⟩ 
      simp at hi
  ⟨ tuple fx, by simp; use fx⟩ 
lemma SetTheory.Set.unique_empty_tuple {X: (∅:Set)  → Set}  { f  : iProd X } : f = empty_tuple := by
  obtain ⟨f, hf⟩ := f 
  obtain ⟨h1, rfl⟩ := (mem_iProd _).mp hf 
  rw[empty_tuple]
  congr
  funext x
  obtain ⟨x, hx⟩ := x
  simp at hx

/-- Example 3.5.10 -/
abbrev SetTheory.Set.empty_iProd_equiv (X: (∅:Set) → Set) : iProd X ≃ Unit where
  toFun := (fun tup ↦ PUnit.unit)
  invFun := fun u ↦ empty_tuple  
  left_inv tup := by
    simp
    exact unique_empty_tuple.symm
  right_inv x := by
    simp

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_of_const_equiv (I:Set) (X: Set) :
    iProd (fun i:I ↦ X) ≃ (I → X) where
  toFun prod := 
      ((mem_iProd _).mp (prod.property)).choose
  invFun x := ⟨tuple fun i:I ↦ (x i), tuple_mem_iProd fun i:I ↦ (x i) ⟩ 
  left_inv prod := by
    have spec := ((mem_iProd _).mp prod.property).choose_spec
    ext
    simp[← spec]
  right_inv x := by
    simp
    generalize_proofs hxi hxi2 ht
    have spec := ht.choose_spec
    funext i
    ext 
    have t := congrArg (fun f => f i) spec
    simp at t
    simp[t]
open Classical in
noncomputable def SetTheory.Set.cartesian_to_tuple_fx {X: ({0,1}:Set) → Set}
  (pair : (X ⟨0, by simp⟩ ×ˢ X ⟨1, by simp⟩)) : (i: ({0,1}:Set)) → X i := 
    fun ⟨i, hi⟩ =>
      if h : i = 0
        then ⟨fst pair, by simp[h, (fst pair).property]⟩ 
        else ⟨snd pair, by simp[h]at hi; simp[hi, (snd pair).property]⟩  

lemma SetTheory.Set.cartesian_to_tuple_fx_eq {X: ({0,1}:Set) → Set}
  {x : ∀ i, X i} : 
  cartesian_to_tuple_fx (mk_cartesian (x ⟨0, by simp⟩) (x ⟨1, by simp⟩)) = x := by
    unfold cartesian_to_tuple_fx
    funext i
    by_cases hi : i = ⟨0, by simp⟩ 
    . 
      aesop
    have hi' : i = ⟨ 1, by simp⟩ := by
      aesop
    aesop
/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod (X: ({0,1}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) where
  toFun prod := 
     mk_cartesian (((mem_iProd _).mp prod.property).choose ⟨0, by simp⟩ ) (((mem_iProd _).mp prod.property).choose ⟨1, by simp⟩ )
  invFun pair :=     
    ⟨ tuple (cartesian_to_tuple_fx pair) ,  tuple_mem_iProd (cartesian_to_tuple_fx pair)⟩
  left_inv prod := by
    have ⟨pv, hp⟩ := prod 
    rw[mem_iProd] at hp
    have spec := hp.choose_spec
    simp
    conv_rhs => rw[spec]
    rw[tuple_inj]
    exact cartesian_to_tuple_fx_eq 
  right_inv pair := by
    set fx := cartesian_to_tuple_fx pair with hfx
    set tup := tuple fx with htup
    set prod :iProd X := ⟨tup, tuple_mem_iProd fx ⟩ with hprod
    have spec := ((mem_iProd _).mp prod.property).choose_spec
    change  mk_cartesian (((mem_iProd _).mp prod.property).choose ⟨0, by simp⟩ ) (((mem_iProd _).mp prod.property).choose ⟨1, by simp⟩ ) = pair
    simp[hprod] at spec
    conv_lhs at spec => rw[htup]
    rw[tuple_inj] at spec
    rw[← spec]
    simp[fx,cartesian_to_tuple_fx]
open Classical in
noncomputable def SetTheory.Set.cartesian_to_triple_fx {X: ({0,1,2}:Set) → Set}
  (pair : (X ⟨0, by simp⟩ ×ˢ X ⟨1, by simp⟩ ×ˢ X ⟨2, by simp⟩ )) : (i: ({0,1,2}:Set)) → X i := 
    fun ⟨i, hi⟩ =>
      if h : i = 0
        then ⟨fst pair, by simp[h, (fst pair).property]⟩ 
        else if h' : i = 1 
          then ⟨fst (snd pair), by simp [h' , (fst (snd pair)).property]⟩ 
          else ⟨snd (snd pair), by simp[h,h']at hi; simp[hi, (snd (snd pair)).property]⟩  

lemma SetTheory.Set.cartesian_to_triple_fx_eq {X: ({0,1,2}:Set) → Set}
  {x : ∀ i, X i} : 
  cartesian_to_triple_fx (mk_cartesian (x ⟨0, by simp⟩) (mk_cartesian (x ⟨1, by simp⟩) (x ⟨2, by simp⟩))) = x := by
    unfold cartesian_to_triple_fx
    funext i
    by_cases hi : i = ⟨0, by simp⟩ 
    . 
      aesop
    by_cases hi' : i = ⟨1, by simp⟩ 
    .
      aesop
    have hi'' : i = ⟨2 , by simp⟩ := by
      aesop
    aesop


/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X: ({0,1,2}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) ×ˢ (X ⟨ 2, by simp ⟩) where
  toFun prod := 
     mk_cartesian (((mem_iProd _).mp prod.property).choose ⟨0, by simp⟩ ) (
      mk_cartesian 
      (((mem_iProd _).mp prod.property).choose ⟨1, by simp⟩ )
      (((mem_iProd _).mp prod.property).choose ⟨2, by simp⟩ )
    )
  invFun pair := 
     ⟨ tuple (cartesian_to_triple_fx pair) ,  tuple_mem_iProd (cartesian_to_triple_fx pair)⟩
  left_inv prod := by
    have ⟨pv, hp⟩ := prod 
    rw[mem_iProd] at hp
    have spec := hp.choose_spec
    simp
    conv_rhs => rw[spec]
    rw[tuple_inj]
    exact cartesian_to_triple_fx_eq 
  right_inv pair := by
    set fx := cartesian_to_triple_fx pair with hfx
    set tup := tuple fx with htup
    set prod :iProd X := ⟨tup, tuple_mem_iProd fx ⟩ with hprod
    have spec := ((mem_iProd _).mp prod.property).choose_spec
    change mk_cartesian (((mem_iProd _).mp prod.property).choose ⟨0, by simp⟩ ) (
      mk_cartesian 
      (((mem_iProd _).mp prod.property).choose ⟨1, by simp⟩ )
      (((mem_iProd _).mp prod.property).choose ⟨2, by simp⟩ )
    ) = pair
    simp[hprod] at spec
    conv_lhs at spec => rw[htup]
    rw[tuple_inj] at spec
    rw[← spec]
    simp[fx,cartesian_to_triple_fx]

/-- Connections with Mathlib's `Set.pi` -/
noncomputable abbrev SetTheory.Set.iProd_equiv_pi (I:Set) (X: I → Set) :
    iProd X ≃ Set.pi .univ (fun i:I ↦ ((X i):_root_.Set Object)) where
  toFun t := ⟨fun i ↦ ((mem_iProd _).mp t.property).choose i, by simp⟩
  invFun x :=
    ⟨tuple fun i ↦ ⟨x.val i, by have := x.property i; simpa⟩, by apply tuple_mem_iProd⟩
  left_inv t := by ext; rw [((mem_iProd _).mp t.property).choose_spec, tuple_inj]
  right_inv x := by
    ext; dsimp
    generalize_proofs _ h
    rw [←(tuple_inj _ _).mp h.choose_spec]


/-
remark: there are also additional relations between these equivalences, but this begins to drift
into the field of higher order category theory, which we will not pursue here.
-/

/--
  Here we set up some an analogue of Mathlib `Fin n` types within the Chapter 3 Set Theory,
  with rudimentary API.
-/
abbrev SetTheory.Set.Fin (n:ℕ) : Set := nat.specify (fun m ↦ (m:ℕ) < n)

theorem SetTheory.Set.mem_Fin (n:ℕ) (x:Object) : x ∈ Fin n ↔ ∃ m, m < n ∧ x = m := by
  rw [specification_axiom'']; constructor
  . intro ⟨ h1, h2 ⟩; use ↑(⟨ x, h1 ⟩:nat); simp [h2]
  intro ⟨ m, hm, h ⟩
  use (by rw [h, ←Object.ofnat_eq]; exact (m:nat).property)
  grind [Object.ofnat_eq''']

abbrev SetTheory.Set.Fin_mk (n m:ℕ) (h: m < n): Fin n := ⟨ m, by rw [mem_Fin]; use m ⟩

theorem SetTheory.Set.mem_Fin' {n:ℕ} (x:Fin n) : ∃ m, ∃ h : m < n, x = Fin_mk n m h := by
  choose m hm this using (mem_Fin _ _).mp x.property; use m, hm
  simp [Fin_mk, ←Subtype.val_inj, this]

@[coe]
noncomputable abbrev SetTheory.Set.Fin.toNat {n:ℕ} (i: Fin n) : ℕ := (mem_Fin' i).choose

noncomputable instance SetTheory.Set.Fin.inst_coeNat {n:ℕ} : CoeOut (Fin n) ℕ where
  coe := toNat

theorem SetTheory.Set.Fin.toNat_spec {n:ℕ} (i: Fin n) :
    ∃ h : i < n, i = Fin_mk n i h := (mem_Fin' i).choose_spec

theorem SetTheory.Set.Fin.toNat_lt {n:ℕ} (i: Fin n) : i < n := (toNat_spec i).choose

@[simp]
theorem SetTheory.Set.Fin.coe_toNat {n:ℕ} (i: Fin n) : ((i:ℕ):Object) = (i:Object) := by
  set j := (i:ℕ); obtain ⟨ h, h':i = Fin_mk n j h ⟩ := toNat_spec i; rw [h']

@[simp low]
lemma SetTheory.Set.Fin.coe_inj {n:ℕ} {i j: Fin n} : i = j ↔ (i:ℕ) = (j:ℕ) := by
  constructor
  · simp_all
  obtain ⟨_, hi⟩ := toNat_spec i
  obtain ⟨_, hj⟩ := toNat_spec j
  grind

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff {n:ℕ} (i: Fin n) {j:ℕ} : (i:Object) = (j:Object) ↔ i = j := by
  constructor
  · intro h
    rw [Subtype.coe_eq_iff] at h
    obtain ⟨_, rfl⟩ := h
    simp [←Object.natCast_inj]
  aesop

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff' {n m:ℕ} (i: Fin n) (hi : ↑i ∈ Fin m) : ((⟨i, hi⟩ : Fin m):ℕ) = (i:ℕ) := by
  obtain ⟨val, property⟩ := i
  simp only [toNat, Subtype.mk.injEq, exists_prop]
  generalize_proofs h1 h2
  suffices : (h1.choose: Object) = h2.choose
  · aesop
  have := h1.choose_spec
  have := h2.choose_spec
  grind

@[simp]
theorem SetTheory.Set.Fin.toNat_mk {n:ℕ} (m:ℕ) (h: m < n) : (Fin_mk n m h : ℕ) = m := by
  have := coe_toNat (Fin_mk n m h)
  rwa [Object.natCast_inj] at this

abbrev SetTheory.Set.Fin_embed (n N:ℕ) (h: n ≤ N) (i: Fin n) : Fin N := ⟨ i.val, by
  have := i.property; rw [mem_Fin] at *; grind
⟩

/-- Connections with Mathlib's `Fin n` -/
noncomputable abbrev SetTheory.Set.Fin.Fin_equiv_Fin (n:ℕ) : Fin n ≃ _root_.Fin n where
  toFun m := _root_.Fin.mk m (toNat_lt m)
  invFun m := Fin_mk n m.val m.isLt
  left_inv m := (toNat_spec m).2.symm
  right_inv m := by simp

/-- Lemma 3.5.11 (finite choice) -/
theorem SetTheory.Set.finite_choice {n:ℕ} {X: Fin n → Set} (h: ∀ i, X i ≠ ∅) : iProd X ≠ ∅ := by
  -- This proof broadly follows the one in the text
  -- (although it is more convenient to induct from 0 rather than 1)
  induction' n with n hn
  . have : Fin 0 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      grind [specification_axiom'']
    have empty (i:Fin 0) : X i := False.elim (by rw [this] at i; exact not_mem_empty i i.property)
    apply nonempty_of_inhabited (x := tuple empty); rw [mem_iProd]; use empty
  set X' : Fin n → Set := fun i ↦ X (Fin_embed n (n+1) (by linarith) i)
  have hX' (i: Fin n) : X' i ≠ ∅ := h _
  choose x'_obj hx' using nonempty_def (hn hX')
  rw [mem_iProd] at hx'; obtain ⟨ x', rfl ⟩ := hx'
  set last : Fin (n+1) := Fin_mk (n+1) n (by linarith)
  choose a ha using nonempty_def (h last)
  have x : ∀ i, X i := fun i =>
    if h : i = n then
      have : i = last := by ext; simpa [←Fin.coe_toNat, last]
      ⟨a, by grind⟩
    else
      have : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Fin.toNat_lt i)) h
      let i' := Fin_mk n i this
      have : X i = X' i' := by simp [X', i', Fin_embed]
      ⟨x' i', by grind⟩
  exact nonempty_of_inhabited (tuple_mem_iProd x)

/-- Exercise 3.5.1, second part (requires axiom of regularity) -/
abbrev OrderedPair.toObject' : OrderedPair ↪ Object where
  toFun p := ({ p.fst, (({p.fst, p.snd}:Set):Object) }:Set)
  inj' p1 p2 := by
    intro h12
    simp[SetTheory.Set.ext_iff] at h12
    have ffst := h12 p1.fst
    simp at ffst
    have fsnd := h12 ( ({p1.fst, p1.snd} : Set) :Object)
    simp at fsnd
    obtain (feq|fother) := ffst
    <;> obtain (sother|seq) := fsnd
    . 
      rw[feq] at sother
      have con := not_mem_self ({p2.fst,p1.snd})
      rw[sother] at con
      simp at con
    . 
      ext
      . exact feq
      rw[feq]at seq
      have cases := pair_eq_pair seq
      simp at cases
      obtain (case1 | ⟨case2_1 , case2_2⟩  ) := cases
      . tauto
      rw[case2_2]
      exact case2_1
    .
      have con := not_mem_mem  {p2.fst,p2.snd} {p1.fst, p1.snd}
      obtain (case1 | case2 ) := con
      .
        simp[← fother] at case1
      simp[← sother] at case2
    .
      have cases := pair_eq_pair seq
      simp at cases
      obtain (⟨case1,case12⟩|⟨case1,case22⟩) := cases  
      all_goals
        rw[case1] at fother
        have con := not_mem_self ({p2.fst,p2.snd})
        simp [←fother] at con

/-- An alternate definition of a tuple, used in Exercise 3.5.2 -/
structure SetTheory.Set.Tuple (n:ℕ) where
  X: Set
  x: Fin n → X
  surj: Function.Surjective x

/--
  Custom extensionality lemma for Exercise 3.5.2.
  Placing `@[ext]` on the structure would generate a lemma requiring proof of `t.x = t'.x`,
  but these functions have different types when `t.X ≠ t'.X`. This lemma handles that part.
-/
@[ext]
lemma SetTheory.Set.Tuple.ext {n:ℕ} {t t':Tuple n}
    (hX : t.X = t'.X)
    (hx : ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object)) :
    t = t' := by
  have ⟨_, _, _⟩ := t; have ⟨_, _, _⟩ := t'; subst hX; congr; ext; grind

/-- Exercise 3.5.2 -/
theorem SetTheory.Set.Tuple.eq {n:ℕ} (t t':Tuple n) :
    t = t' ↔ ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object) := by
      constructor
      . 
        intro eq m
        rw[eq]
      intro eq
      ext u
      .
        constructor
        <;> intro memt
        map_tacs[have surj := t.surj; have surj := t'.surj]
        all_goals
          unfold Function.Surjective at surj
          specialize surj ⟨u, memt⟩ 
          obtain ⟨a, ha⟩ := surj 
          specialize eq a
          rw[ha] at eq
          simp at eq
        map_tacs[have prop := (t'.x a).property; have prop := (t.x a).property]
        . simp[eq]; exact prop
        simp[← eq]; exact prop  
      exact eq u
noncomputable abbrev SetTheory.Set.iProd_equiv_tuples (n:ℕ) (X: Fin n → Set) :
    iProd X ≃ { t:Tuple n // ∀ i, (t.x i:Object) ∈ X i } where
  toFun prod := by
    set fx := ( (mem_iProd _).mp prod.property ).choose with hfx
    set codom :Set := (iUnion (Fin n) X).specify (fun a ↦ ∃ m, a.val = fx m)  with hcod
    set f : Fin n → codom := fun i ↦ ⟨
      fx i, 
      by 
        rw[hcod,specification_axiom'']
        have h : (fx i).val ∈ (Fin n).iUnion X := by
          rw[mem_iUnion]
          use i
          exact (fx i).property
        use h,i
    ⟩ 
    exact ⟨⟨codom, f, by 
      unfold Function.Surjective 
      intro b
      simp_all [fx, codom, f]
      obtain ⟨val, property⟩ := prod
      obtain ⟨val_1, property_1⟩ := b
      simp_all only [Subtype.mk.injEq, codom, fx]
      simp_all [codom, fx]
      obtain ⟨left, right⟩ := property_1
      obtain ⟨w, h⟩ := right
      obtain ⟨w_1, h⟩ := h
      obtain ⟨w_1, h⟩ := w_1
      subst h
      apply Exists.intro
      · apply Exists.intro
        · rfl
        · simp_all only [exists_const]
    ⟩ 
,by 
      grind only [cases eager Subtype]
    ⟩ 
  invFun tup := by
    obtain ⟨tup, htup⟩ := tup 
    have f : ∀ i, X i := fun i ↦ ⟨ tup.x i, htup i⟩  
    exact ⟨tuple f, tuple_mem_iProd f⟩ 
  left_inv prod := by
    simp only [Subtype.coe_eta]
    have hfx := ( (mem_iProd _).mp prod.property ).choose_spec 
    ext
    conv_rhs => rw[hfx]

  right_inv tup := by
    obtain ⟨tup , htup⟩ := tup 
    set f : ∀ i, X i := fun i ↦ ⟨ tup.x i, htup i⟩ with hf
    set prod: iProd X := ⟨tuple f, tuple_mem_iProd f⟩ with hprod
    set fx := ( (mem_iProd _).mp prod.property ).choose with hfx
    have spec := ( (mem_iProd _).mp prod.property ).choose_spec
    rw[hprod] at spec
    rw[tuple_inj] at spec
    
    simp only [Lean.Elab.WF.paramLet, Subtype.mk.injEq]
    ext t
    . 
      simp only [Subtype.exists, specification_axiom'', exists_prop]
      constructor
      .
        intro ht
        obtain ⟨ht, ⟨a,⟨ha, hfin⟩ ,h⟩ ⟩ := ht 
        rw[h]
        rw[← spec]
        simp[f]
        have xp := (tup.x (⟨a, by simp; use ha ⟩) ).property
        exact xp
      intro ht
      have surj := tup.surj
      unfold Function.Surjective at surj
      specialize surj ⟨t,ht⟩ 
      obtain ⟨a, hxi⟩ := surj 
      split_ands
      .
        specialize htup a
        simp[hxi] at htup
        rw[mem_iUnion]
        use a
      use a.val
      have ap := a.property
      simp at ap
      use ap
      simp[← spec,f,hxi]
    . 
      simp[← spec,f]

/--
  Exercise 3.5.3. The spirit here is to avoid direct rewrites (which make all of these claims
  trivial), and instead use `OrderedPair.eq` or `SetTheory.Set.tuple_inj`
-/
theorem OrderedPair.refl (p: OrderedPair) : p = p := by 
  rw[OrderedPair.eq]
  split_ands <;> rfl
  

theorem OrderedPair.symm (p q: OrderedPair) : p = q ↔ q = p := by
  constructor
  <;> intro h
  <;> rw[OrderedPair.eq] at *
  <;> obtain ⟨h1, h2⟩ := h  
  <;> tauto

theorem OrderedPair.trans {p q r: OrderedPair} (hpq: p=q) (hqr: q=r) : p=r := by
  rw[OrderedPair.eq] at *
  obtain ⟨fpq,spq⟩ := hpq
  obtain ⟨fqr,sqr⟩ := hqr
  rw[fqr]at fpq
  rw[sqr]at spq
  tauto

theorem SetTheory.Set.tuple_refl {I:Set} {X: I → Set} (a: ∀ i, X i) :
    tuple a = tuple a := by 
    rw[tuple_inj]


theorem SetTheory.Set.tuple_symm {I:Set} {X: I → Set} (a b: ∀ i, X i) :
    tuple a = tuple b ↔ tuple b = tuple a := by
      constructor
      <;> intro h
      <;> rw[tuple_inj] at *
      <;> exact h.symm

theorem SetTheory.Set.tuple_trans {I:Set} {X: I → Set} {a b c: ∀ i, X i}
  (hab: tuple a = tuple b) (hbc : tuple b = tuple c) :
    tuple a = tuple c := by
      rw[tuple_inj] at *
      rw[hbc]at hab
      exact hab

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_union (A B C:Set) : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
  ext p
  constructor
  . 
    intro hp
    rw[mem_cartesian] at hp
    rw[mem_union,mem_cartesian,mem_cartesian]
    obtain ⟨x,⟨y,huy⟩ ,hxy⟩ := hp 
    rw[mem_union] at huy
    obtain (case|case) := huy
    map_tacs[left;right]
    all_goals
      use x
      use ⟨y,case⟩ 
  intro hp
  rw[mem_union,mem_cartesian,mem_cartesian] at hp
  rw[mem_cartesian]
  obtain (⟨x,⟨y,hy⟩ ,p⟩| ⟨x,⟨y,hy⟩ ,p⟩) := hp 
  all_goals
    have huy : y ∈ B ∪ C  := by simp[hy]
    use x, ⟨y,huy⟩ 

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_inter (A B C:Set) : A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by
  ext v
  rw[mem_cartesian,mem_inter,mem_cartesian,mem_cartesian]
  constructor
  . 
    rintro ⟨x,⟨y,hiy⟩ ,hv⟩  
    rw[mem_inter] at hiy
    obtain ⟨hby,hcy⟩ := hiy 
    split_ands
    map_tacs[ set y' : B := ⟨y,hby⟩ with hy; set y' : C := ⟨y, hcy⟩with hy]
    all_goals
      use x,y'
  intro ⟨⟨xb,⟨yb,hyb⟩ ,hb⟩ ,⟨xc,⟨yc,hyc⟩ ,hc⟩ ⟩ 
  rw[hb] at hc
  simp at hc
  obtain ⟨hbb, hcc⟩:= hc 
  have hyi : yb ∈ B ∩ C :=  by
    aesop
  use xb, ⟨yb,hyi⟩ 

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_diff (A B C:Set) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  ext v
  rw [mem_cartesian, mem_sdiff,mem_cartesian,mem_cartesian,not_exists]
  constructor
  . 
    rintro ⟨x,⟨y,hy⟩ ,h⟩ 
    rw[mem_sdiff] at hy
    obtain ⟨hyb, hyc⟩ := hy 
    split_ands
    . use x,⟨y,hyb⟩ 
    aesop
  rintro ⟨⟨x,y,hxy⟩ ,h2⟩ 
  specialize h2 x
  push_neg at h2
  aesop

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.union_prod (A B C:Set) : (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) := by
  ext v
  simp
  constructor
  .
    rintro ⟨x,(hx|hx),y,hyc,hv⟩ 
    map_tacs[left;right]
    all_goals
      use x
      simp[hx]
      use y

  rintro (⟨x,hx,y,hy,hv⟩ |⟨x,hx,y,hy,hv⟩) <;> use x <;> split_ands
  <;> try simp[hx]
  all_goals
    use y

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.inter_prod (A B C:Set) : (A ∩ B) ×ˢ C = (A ×ˢ C) ∩ (B ×ˢ C) := by
  ext v
  simp
  constructor
  . 
    rintro ⟨x,⟨hax,hbx⟩,y,hyc,hv ⟩ 
    split_ands
    all_goals
      use x
      tauto
  rintro ⟨⟨xa,ha,ya,hyac,hva⟩ ,⟨xb,hb,yb,hybc,hvb⟩ ⟩ 
  rw[hva] at hvb
  simp at hvb
  obtain ⟨hx,hy⟩:= hvb 
  use xa
  split_ands
  . exact ha
  . rw[hx]; exact hb
  . use ya
/-- Exercise 3.5.4 -/
theorem SetTheory.Set.diff_prod (A B C:Set) : (A \ B) ×ˢ C = (A ×ˢ C) \ (B ×ˢ C) := by
  ext v
  simp
  constructor
  . 
    rintro ⟨a,⟨⟨haa,hab⟩ ,⟨c,hc,hv⟩ ⟩ ⟩ 
    split_ands
    . 
      use a
      simp[haa]
      use c
    intro b hb c' hc'
    rw[hv]
    simp
    intro hab'
    rw[hab'] at hab
    contradiction
  rintro ⟨⟨a,ha,c,hc,hv⟩ , hb⟩ 
  use a
  by_cases hab : a ∈ B
  . specialize hb a hab c hc
    contradiction
  simp [ha,hab]
  use c

/-- Exercise 3.5.5 -/
theorem SetTheory.Set.inter_of_prod (A B C D:Set) :
    (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
      ext v
      simp
      constructor
      . 
        rintro ⟨⟨a,ha,b,hb,hab⟩ ,⟨c,hc,d,hd,hcd⟩ ⟩ 
        simp[hab]at hcd
        obtain ⟨hac,hbd⟩ := hcd
        rw[hac]at ha
        rw[hbd] at hb
        use c
        simp[ha,hc]
        use d
        simp[hb,hd]
        simp[hab,hac,hbd]
      rintro ⟨x,⟨hxa,hxc⟩ ,y,⟨hyb,hyd⟩,hv ⟩ 
      split_ands
      <;> tauto



/- Exercise 3.5.5 -/
def SetTheory.Set.union_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  simp
  use {0},{1},{2},{3}
  rw[SetTheory.Set.ext_iff]
  push_neg
  use ((⟨0,3⟩ : OrderedPair) : Object)
  right
  aesop

/- Exercise 3.5.5 -/
def SetTheory.Set.diff_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  simp
  use {1,2} ,{3,4},{1},{3}
  rw[SetTheory.Set.ext_iff]
  push_neg
  use ((⟨2,3⟩:OrderedPair) : Object) 
  left
  simp

/--
  Exercise 3.5.6.
-/
theorem SetTheory.Set.prod_subset_prod {A B C D:Set}
  (hA: A ≠ ∅) (hB: B ≠ ∅) (hC: C ≠ ∅) (hD: D ≠ ∅) :
    A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D := by
      rw[subset_def,subset_def,subset_def]
      constructor 
      .
        intro h
        apply nonempty_def at hA
        obtain ⟨a,ha⟩ := hA 
        apply nonempty_def at hB
        obtain ⟨b,hb⟩ := hB 
        split_ands
        <;> intro x hx
        . 
          specialize h (⟨x, b⟩ :OrderedPair)
          simp at h
          specialize h hx hb
          exact h.1
        specialize h (⟨a, x⟩ : OrderedPair)
        simp at h
        specialize h ha hx
        exact h.2
      rintro ⟨h1, h2⟩ 
      intro x hx
      rw[mem_cartesian] at hx ⊢
      obtain ⟨⟨a,ha⟩ ,⟨b,hb⟩ ,hx ⟩:= hx 
      simp at hx
      apply h1 at ha
      apply h2 at hb
      use ⟨a,ha⟩, ⟨b, hb⟩  

def SetTheory.Set.prod_subset_prod' :
  Decidable (∀ (A B C D:Set), A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use  {1} ,∅ ,∅  ,∅  
  left
  split_ands
  . 
    rw[subset_def]
    intro x
    rw[mem_cartesian]
    rintro ⟨fst,⟨snd,hsnd⟩ ,hx⟩ 
    simp at hsnd
  .
    intro cont
    rw[subset_def] at cont
    specialize cont 1
    simp at cont


/-- Exercise 3.5.7 -/
theorem SetTheory.Set.direct_sum {X Y Z:Set} (f: Z → X) (g: Z → Y) :
    ∃! h: Z → X ×ˢ Y, fst ∘ h = f ∧ snd ∘ h = g := by
      apply existsUnique_of_exists_of_unique
      . 
        use fun z ↦  ⟨ (⟨f z, g z⟩:OrderedPair) , by simp⟩ 
        split_ands
        all_goals
          ext z
          simp
      intro h1 h2
      rintro ⟨fh1, gh1⟩ ⟨fh2,gh2⟩ 
      ext z
      have eqfst : fst (h1 z) =  fst (h2 z) := by
        calc 
          fst (h1 z) = f z := by rw[← fh1, Function.comp_apply]
          f z = fst (h2 z) := by rw[← fh2, Function.comp_apply]
      have eqsnd : snd (h1 z) =  snd (h2 z) := by
        calc 
          snd (h1 z) = g z := by rw[← gh1, Function.comp_apply]
          g z = snd (h2 z) := by rw[← gh2, Function.comp_apply]
      have p1 := mk_cartesian_fst_snd_eq (h1 z)
      have p2 := mk_cartesian_fst_snd_eq (h2 z)
      rw[eqfst,eqsnd] at p1
      rw[p1]at p2
      congr


/-- Exercise 3.5.8 -/
@[simp]
theorem SetTheory.Set.iProd_empty_iff {n:ℕ} {X: Fin n → Set} :
    iProd X = ∅ ↔ ∃ i, X i = ∅ := by
      constructor <;> contrapose!
      . 
        intro hi
        let fx : (i : Fin n) → X i := fun i ↦ 
          ⟨ (nonempty_def (hi i)).choose, (nonempty_def (hi i)).choose_spec ⟩
        have htup := tuple_mem_iProd fx
        exact nonempty_of_inhabited htup
      intro hi
      replace hi := nonempty_def hi
      obtain ⟨tup, htup⟩ := hi 
      rw[mem_iProd] at htup
      obtain ⟨fx, hfx⟩:= htup 
      intro i
      have ⟨xi, hxi⟩  := fx i
      exact nonempty_of_inhabited hxi

/-- Exercise 3.5.9-/
theorem SetTheory.Set.iUnion_inter_iUnion {I J: Set} (A: I → Set) (B: J → Set) :
    (iUnion I A) ∩ (iUnion J B) = iUnion (I ×ˢ J) (fun p ↦ (A (fst p)) ∩ (B (snd p))) := by
      ext v
      simp[mem_iUnion]
      constructor
      .
        rintro ⟨⟨i,hi,hia⟩ ,⟨j,hj,hjb⟩ ⟩ 
        use (⟨i,j⟩:OrderedPair )
        simp
        use ⟨hi, hj⟩ 
        rw[fst_of_mk_cartesian ⟨i, hi⟩ ⟨j, hj⟩ ]
        rw[snd_of_mk_cartesian ⟨i, hi⟩ ⟨j, hj⟩ ]
        exact ⟨hia, hjb⟩ 
      rintro ⟨p,⟨a,hai,b,hbj,rfl⟩ ,⟨hvA,hvB⟩ ⟩ 
      rw[fst_of_mk_cartesian ⟨a, hai⟩ ⟨b, hbj⟩ ] at hvA
      rw[snd_of_mk_cartesian ⟨a, hai⟩ ⟨b, hbj⟩ ] at hvB
      split_ands
      . 
        use a, hai 
      use b, hbj

abbrev SetTheory.Set.graph {X Y:Set} (f: X → Y) : Set :=
  (X ×ˢ Y).specify (fun p ↦ (f (fst p) = snd p))

/-- Exercise 3.5.10 -/
theorem SetTheory.Set.graph_inj {X Y:Set} (f f': X → Y) :
    graph f = graph f' ↔ f = f' := by
      rw[SetTheory.Set.ext_iff]
      constructor
      .
        intro h
        ext x
        set y := f x with hy
        symm at hy
        set y' :=f' x with hy'
        set p : OrderedPair := ⟨x, y⟩ with hp
        set p' : OrderedPair  := ⟨x,y'⟩ 
        specialize h p
        rw[specification_axiom'',specification_axiom''] at h
        simp at h
        specialize h x x.property y y.property hp 
        have r := h.mp hy
        rw[← hy'] at r
        symm at r
        simp[r]
      intro hf p
      rw[specification_axiom'',specification_axiom'']
      constructor <;> rintro ⟨hp,hfe⟩ <;> use hp
      map_tacs[rw[← hf]; rw[hf]]
      assumption'

theorem SetTheory.Set.is_graph {X Y G:Set} (hG: G ⊆ X ×ˢ Y)
  (hvert: ∀ x:X, ∃! y:Y, ((⟨x,y⟩:OrderedPair):Object) ∈ G) :
    ∃! f: X → Y, G = graph f := by
      apply existsUnique_of_exists_of_unique
      . 
        -- revert the function
        set fx : X → Y := fun x ↦ (ExistsUnique.exists (hvert x)).choose
        use fx
        ext po
        constructor
        . 
          -- prepare the xy pair
          intro hp
          have hpu : po ∈ X ×ˢ Y := by
            rw[subset_def]at hG
            exact hG po hp
          set p: X ×ˢ Y := ⟨po,hpu⟩  
          have:  po =p.val := by rfl
          rw[this]
          simp
          have eq := mk_cartesian_fst_snd_eq p
          unfold mk_cartesian at eq
          symm at eq
          set x := fst p
          set y := snd p
          split_ands
          . 
            use x, x.property, y, y.property
            rw[eq]
          simp[fx]
          have unique := hvert x
          have spec := (ExistsUnique.exists (hvert x)).choose_spec
          rw[this,eq] at hp
          exact ExistsUnique.unique unique spec hp
        intro hp
        have hpu : po ∈ X ×ˢ Y := by
          exact specification_axiom hp
        simp[specification_axiom''] at hp
        obtain ⟨⟨x,hx,y,hy,hpo⟩ , hfx⟩ := hp 
        set p : X ×ˢ Y := ⟨po, hpu⟩ with hppo
        have hpx : fst p = x := by
          have temp := fst_of_mk_cartesian ⟨x, hx⟩ ⟨y, hy⟩ 
          unfold mk_cartesian at temp
          simp_all only
        have hpy : snd p = y := by
          have temp := snd_of_mk_cartesian ⟨x, hx⟩ ⟨y, hy⟩ 
          unfold mk_cartesian at temp
          simp_all only
        simp[fx] at hfx
        have unique := hvert (fst p)
        simp at unique
        rw[hpo]
        have spec := (ExistsUnique.exists unique).choose_spec
        rw[hfx] at spec
        rw[hpx,hpy] at spec
        exact spec
      intro f1 f2 gf1 gf2
      funext x
      set y1 := f1 x
      set y2 := f2 x
      specialize hvert x
      apply ExistsUnique.unique hvert
      . 
        rw[gf1]
        simp[specification_axiom'',y1]
      rw[gf2]
      simp[specification_axiom'',y2]



/--
  Exercise 3.5.11. This trivially follows from `SetTheory.Set.powerset_axiom`, but the
  exercise is to derive it from `SetTheory.Set.exists_powerset` instead.
-/


theorem SetTheory.Set.powerset_axiom' (X Y:Set) :
    ∃! S:Set, ∀(F:Object), F ∈ S ↔ ∃ f: Y → X, f = F := by
      have h_exist_powerset := SetTheory.Set.exists_powerset (Y ×ˢ X)
      obtain ⟨Z, hZ⟩ := h_exist_powerset 

      -- coe of subset and Z 

      set rv_subset : Z → Set := fun z ↦ 
        ((hZ z.val).mp z.property).choose

      have rv_Inv (z:Z) : z = set_to_object (rv_subset z) := by
        simp[rv_subset]
        exact  ((hZ z.val).mp z.property).choose_spec.1


      have subset_spec (z:Z) := ((hZ z.val).mp z.property).choose_spec.2

      -- mapping and function graph 
      set is_mapping : Z → Prop := fun z ↦ 
        ∀ y:Y, ∃! x:X, ((⟨y,x⟩: OrderedPair): Object) ∈ rv_subset z
      have mapping_is_graph (z : Z) : is_mapping z → ∃ f : Y → X, rv_subset z = graph f:= by
        unfold is_mapping
        intro hvert
        have hGSub := subset_spec z
        have hFun := is_graph hGSub hvert
        unfold rv_subset
        exact ExistsUnique.exists hFun
      have graph_in_Z : ∀ f: Y → X, ((graph f):Object) ∈ Z := by
        intro f
        replace hZ := (hZ (graph f)).mpr
        apply hZ
        use (graph f)
        simp
        apply specification_axiom
      have rvInv' : ∀ f : Y → X, rv_subset ⟨(graph f), graph_in_Z f⟩ = graph f := by 
        intro f
        rw[← coe_eq_iff]
        symm
        have inv := rv_Inv (⟨graph f, graph_in_Z f⟩ )
        rw[← inv]

      have graph_is_mapping : ∀ f: Y → X , is_mapping ⟨graph f, graph_in_Z f⟩ := by
        intro f
        unfold is_mapping
        intro y
        apply existsUnique_of_exists_of_unique
        . 
          use (f y)
          rw[rvInv']
          simp
        intro x1 x2
        intro hr1 hr2
        simp[rvInv',specification_axiom''] at hr1 hr2
        rwa[hr1] at hr2

      set SMap := Z.specify is_mapping


      let obtain_function (s : SMap) : Y → X := 
         ((mapping_is_graph ⟨s.val,specification_axiom s.property⟩ ) ((specification_axiom' _ _).mp s.property )).choose
      let obtain_function_spec (s:SMap) :=
         ((mapping_is_graph ⟨s.val,specification_axiom s.property⟩ ) ((specification_axiom' _ _).mp s.property )).choose_spec
      

      let rep_prop: SMap → Object → Prop := fun s f ↦ f = obtain_function s
      set S := SMap.replace (P := rep_prop) (
        by
        intro s f1 f2 ⟨pf1,pf2⟩ 
        simp[rep_prop] at pf1 pf2
        rw[← pf1]at pf2
        exact pf2.symm
      )

      -- finally start to prove unique exists
      apply existsUnique_of_exists_of_unique 
      .
        use S
        intro F
        rw[replacement_axiom]
        unfold rep_prop
        constructor
        .
          intro hF
          obtain ⟨z,hprop⟩  := hF
          symm at hprop
          use (obtain_function z)
        rintro ⟨f,hf⟩ 
        set smap : SMap := ⟨graph f, 
          by
            rw[specification_axiom'']
            use (graph_in_Z f)
            apply graph_is_mapping
        ⟩ 
        use smap
        have spec := obtain_function_spec smap
        unfold obtain_function
        simp[← hf,← graph_inj, ← spec]
        rw[← coe_eq_iff, ← rv_Inv]
      intro S1 S2 hS1 hS2
      ext F
      specialize hS1 F
      specialize hS2 F
      simp[hS1,hS2]
  
/-- Exercise 3.5.12, with errata from web site incorporated -/
lemma SetTheory.Set.nat_ind { P : nat → Prop } (pzero : P (nat_equiv 0))  (psucc : (∀ n, P (nat_equiv n) → P (nat_equiv (n+1)))) : ∀ n, P (nat_equiv n) := by
  intro n
  induction' n with k hk
  . 
    exact pzero
  apply psucc k hk

theorem SetTheory.Set.recursion (X: Set) (f: nat → X → X) (c:X) :
    ∃! a: nat → X, a 0 = c ∧ ∀ n, a (n + 1:ℕ) = f n (a n) := by
      let a : nat → X := fun n ↦ 
        Nat.rec c (fun n pr ↦ f n pr) n
      apply existsUnique_of_exists_of_unique
      .
        use a
        simp[a]
      . 
        intro a1 a2 ⟨az1, as1⟩ ⟨az2,as2⟩  
        set P : nat → Prop := fun n ↦ a1 n = a2 n with hp
        have aux : ∀ n, P (nat_equiv n) := by
          apply nat_ind
          . 
            unfold P
            have : nat_equiv 0 = 0 := by rfl
            simp[this,az1,az2]
          .
            intro n
            specialize as1 n
            specialize as2 n
            unfold P
            intro hi
            have : nat_equiv n = ↑n := by rfl
            simp[this] at hi
            rw[hi]at as1
            rw[← as1] at as2
            have : nat_equiv (n+1) = ↑(n+1) := by rfl
            rw[this]
            exact as2.symm
        ext n'
        unfold P at aux
        set n:= nat_equiv.symm n'
        specialize aux n
        have:  nat_equiv n = n' := by simp[n]
        rw[this] at aux
        simp[aux]

/-- Exercise 3.5.13 -/
theorem SetTheory.Set.nat_unique (nat':Set) (zero:nat') (succ:nat' → nat')
  (succ_ne: ∀ n:nat', succ n ≠ zero) (succ_of_ne: ∀ n m:nat', n ≠ m → succ n ≠ succ m)
  (ind: ∀ P: nat' → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n) :
    ∃! f : nat → nat', Function.Bijective f ∧ f 0 = zero
    ∧ ∀ (n:nat) (n':nat'), f n = n' ↔ f (n+1:ℕ) = succ n' := by
  have nat_coe_eq {m:nat} {n} : (m:ℕ) = n → m = n := by aesop
  have nat_coe_eq_zero {m:nat} : (m:ℕ) = 0 → m = 0 := nat_coe_eq
  obtain ⟨f, hf⟩ := recursion nat' (fun _ n ↦ succ n) zero
  apply existsUnique_of_exists_of_unique
  · use f
    constructor
    · constructor
      · intro x1 x2 heq
        induction' hx1: (x1:ℕ) with i ih generalizing x1 x2
        · 
          simp at hf
          obtain ⟨⟨hfz,hfi⟩ , hfunique⟩ := hf
          apply nat_coe_eq_zero at hx1
          simp[hx1,hfz] at heq
          rw[hx1]
          by_contra hnz
          set x2' :ℕ := (nat_equiv.symm x2)  with hxp
          have hx2nz : x2' ≠ 0 := by
            by_contra h
            rw[hxp] at h
            have := nat_coe_eq_zero h
            symm at this
            contradiction
          have hx2g1 : 1 ≤ x2' := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hx2nz)
          have : x2' - 1 + 1 = x2' := by
            simpa using Nat.sub_add_cancel hx2g1
          specialize hfi (x2'-1)
          rw[this] at hfi
          simp[x2'] at hfi
          rw[← heq] at hfi
          symm at hfi
          specialize succ_ne (f ↑(nat_equiv.symm x2 - 1))
          contradiction


        



        
      sorry
    sorry
  sorry


end Chapter3
