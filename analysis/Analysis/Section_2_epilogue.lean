import Mathlib.Tactic
import Analysis.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers

In this (technical) epilogue, we show that the "Chapter 2" natural numbers `Chapter2.Nat` are
isomorphic in various senses to the standard natural numbers `ℕ`.

After this epilogue, `Chapter2.Nat` will be deprecated, and we will instead use the standard
natural numbers `ℕ` throughout.  In particular, one should use the full Mathlib API for `ℕ` for
all subsequent chapters, in lieu of the `Chapter2.Nat` API.

Filling the sorries here requires both the Chapter2.Nat API and the Mathlib API for the standard
natural numbers `ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

In second half of this section we also give a fully axiomatic treatment of the natural numbers
via the Peano axioms. The treatment in the preceding three sections was only partially axiomatic,
because we used a specific construction `Chapter2.Nat` of the natural numbers that was an inductive
type, and used that inductive type to construct a recursor.  Here, we give some exercises to show
how one can accomplish the same tasks directly from the Peano axioms, without knowing the specific
implementation of the natural numbers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Converting a Chapter 2 natural number to a Mathlib natural number. -/
abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

/-- The conversion is a bijection. Here we use the existing capability (from Section 2.1) to map
the Mathlib natural numbers to the Chapter 2 natural numbers. -/
abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn; rfl
    simp [hn]
    rw [succ_eq_add_one]
  right_inv n := by
    induction' n with n hn; rfl
    simp [←succ_eq_add_one, hn]

/-- The conversion preserves addition. -/
abbrev Chapter2.Nat.map_add : ∀ (n m : Nat), (n + m).toNat = n.toNat + m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_add, _root_.Nat.zero_add]
  rw[succ_add, succ_toNat, succ_toNat, hn]
  abel


/-- The conversion preserves multiplication. -/
abbrev Chapter2.Nat.map_mul : ∀ (n m : Nat), (n * m).toNat = n.toNat * m.toNat := by
  intro n m
  induction' n with n hn
  . rw[show zero = 0 from rfl, zero_mul, zero_toNat]
    ring
  rw[succ_mul, succ_toNat, map_add, hn]
  ring

/-- The conversion preserves order. -/
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  constructor
  . contrapose
    push_neg
    intro ⟨⟨v, hv⟩, hne⟩
    have : v ≠ 0 := by
      by_contra h
      simp[h] at hv
      symm at hv
      contradiction
    have : 0 < v.toNat  := by
      rcases uniq_succ_eq v this with ⟨ m, hm, hmu ⟩
      rw[← hm, succ_toNat]
      simp
    rw[hv, map_add]
    simp
    assumption
  intro ⟨ v, hv ⟩
  rw[hv, map_add]
  simp

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := map_le_map_iff
/-- The conversion preserves exponentiation. -/
lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
    n.toNat ^ m.toNat = (n^m).toNat := by
      induction' m with m mh
      . simp
      rw[succ_toNat, pow_succ, map_mul, ← mh]
      ring

/-- The Peano axioms for an abstract type `Nat` -/
@[ext]
structure PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

namespace PeanoAxioms

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2_Nat : PeanoAxioms where
  Nat := Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- The Mathlib natural numbers obey the Peano axioms. -/
def Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)


/-- One can start the proof here with `unfold Function.Injective`, although it is not strictly necessary. -/
theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast  := by
    unfold Function.Injective
    intro a b p
    revert a
    induction' b with b hind
    . intro a p
      contrapose! p
      rcases Nat.exists_eq_succ_of_ne_zero p  with ⟨v, hv⟩
      rw[hv,natCast]
      apply P.succ_ne
    intro a' pa'
    have : a' ≠ 0 := by
      contrapose! pa'
      rw[pa',natCast, natCast]
      symm
      apply P.succ_ne
    rcases Nat.exists_eq_succ_of_ne_zero this  with ⟨v, hv⟩
    rw[hv, natCast, natCast] at pa'
    apply P.succ_cancel at pa'
    apply hind at pa'
    simp[hv,pa']

/-- One can start the proof here with `unfold Function.Surjective`, although it is not strictly necessary. -/
theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
    unfold Function.Surjective
    apply P.induction
    . use 0
    intro p ⟨a, ha⟩ 
    use (a + 1)
    rw[natCast, ha]

/-- The notion of an equivalence between two structures obeying the Peano axioms.
    The symbol `≃` is an alias for Mathlib's `Equiv` class; for instance `P.Nat ≃ Q.Nat` is
    an alias for `_root_.Equiv P.Nat Q.Nat`. -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

/-- This exercise will require application of Mathlib's API for the `Equiv` class.
    Some of this API can be invoked automatically via the `simp` tactic. -/
abbrev Equiv.symm {P Q: PeanoAxioms} (equiv : Equiv P Q) : Equiv Q P where
  equiv := equiv.equiv.symm
  equiv_zero := by
    have eq := equiv.equiv_zero.symm
    rw[eq]
    simp
    
  equiv_succ n := by 
    have eq := equiv.equiv_succ
    specialize eq (Equiv.equiv.symm n)
    simp at eq
    rw[← eq]
    simp

/-- This exercise will require application of Mathlib's API for the `Equiv` class.
    Some of this API can be invoked automatically via the `simp` tactic. -/
abbrev Equiv.trans {P Q R: PeanoAxioms} (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by 
    simp [equiv1.equiv_zero, equiv2.equiv_zero]
  equiv_succ n := by 
    simp
    have eq1 := equiv1.equiv_succ
    specialize eq1 n
    rw[eq1]
    have eq2 := equiv2.equiv_succ
    specialize eq2 (equiv n)
    rw[eq2]

/-- Useful Mathlib tools for inverting bijections include `Function.surjInv` and `Function.invFun`. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv := {
    toFun := P.natCast
    invFun := P.natCast.invFun 
    left_inv := by 
      unfold Function.LeftInverse 
      intro x
      exact Function.leftInverse_invFun P.natCast_injective x
    right_inv := by
      unfold Function.RightInverse 
      unfold Function.LeftInverse 
      intro x
      exact Function.rightInverse_invFun P.natCast_surjective x
  }
  equiv_zero := by 
    simp
    rfl
  equiv_succ n := by 
    simp
    rfl

/-- The task here is to establish that any two structures obeying the Peano axioms are equivalent. -/
noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q :=
     Equiv.trans (Equiv.symm (Equiv.fromNat P)) (Equiv.fromNat Q)
/-- There is only one equivalence between any two structures obeying the Peano axioms. -/
theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  obtain ⟨equiv1, equiv_zero1, equiv_succ1⟩ := equiv1
  obtain ⟨equiv2, equiv_zero2, equiv_succ2⟩ := equiv2
  congr
  ext n
  revert n
  apply P.induction
  . simp[equiv_zero1, equiv_zero2]
  intro n hind
  simp[equiv_succ1,equiv_succ2]
  rw[hind]



/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by

      -- definitions
      let e := Equiv.fromNat P
      let toP : ℕ → P.Nat := e.equiv.toFun
      let toNat : P.Nat → ℕ := e.equiv.invFun
      have l_inv : ∀ x : ℕ , toNat (toP x) = x := e.equiv.left_inv
      have r_inv : ∀ y : P.Nat, toP (toNat y) = y := e.equiv.right_inv

      -- recursive  function
      let a_aux : ℕ → P.Nat :=
        Nat.rec c (fun n' prev_result => f (toP n') prev_result)
      let a : P.Nat → P.Nat := fun p ↦ a_aux (toNat p)

      -- properties of the function 

      have a_z : a P.zero = c := by
        simp[a, show P.zero = toP 0 from rfl , l_inv 0, a_aux]
      have a_succ :∀ n, a (P.succ n) = f n (a n) := by
        intro n
        simp[a, 
          show toNat (P.succ n) = toNat n + 1 
            from (Equiv.symm e).equiv_succ n, 
          a_aux,
          r_inv
        ]
     
      -- body of the proof

      use a
      constructor
      . --exist
        split_ands
        . exact a_z
        . exact a_succ
      . --unique
        intro a' ha'
        funext n
        revert n
        apply P.induction
        . -- base case
          rw[ha'.1]
          exact a_z.symm
        . -- induction
          intro n hind
          rw[ha'.2, hind]
          exact (a_succ n).symm

end PeanoAxioms
