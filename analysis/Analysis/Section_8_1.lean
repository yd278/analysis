import Mathlib.Tactic

/-!
# Analysis I, Section 8.1

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. hen there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Custom notions for "equal cardinality", "countable", and "at most countable".  Note that Mathlib's
`Countable` typeclass corresponds to what we call "at most countable" in this text.

Note that as the Chapter 3 set theory has been deprecated, we will not re-use relevant constructions from that theory here, replacing them with Mathlib counterparts instead.

-/

namespace Chapter8

/-- The definition of equal cardinality. For simplicity we restrict attention to the Type 0 universe. -/
abbrev EqualCard (X Y : Type) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Equivalence with Mathlib's `Cardinal.mk` concept -/
theorem EqualCard.iff {X Y : Type} :
  EqualCard X Y ↔ Nonempty (X ≃ Y) := by
  simp [EqualCard]
  constructor
  . rintro ⟨ f, hf ⟩
    exact ⟨ Equiv.ofBijective f hf ⟩
  rintro ⟨ e ⟩
  exact ⟨ e.toFun, e.bijective ⟩

theorem EqualCard.iff' {X Y : Type} :
  EqualCard X Y ↔ Cardinal.mk X = Cardinal.mk Y := by
  simp [Cardinal.eq, iff]

instance EqualCard.instSetoid : Setoid Type where
  r := EqualCard
  iseqv := {
    refl X := by sorry
    symm {X} {Y} hXY := by sorry
    trans {X} {Y} {Z} hXY hYZ := by sorry
  }

theorem EqualCard.univ (X : Type) : EqualCard (Set.univ : Set X) X :=
  ⟨ Subtype.val, Subtype.val_injective, by intro _; aesop ⟩

abbrev CountablyInfinite (X : Type) : Prop := EqualCard X ℕ

abbrev AtMostCountable (X : Type) : Prop := CountablyInfinite X ∨ Finite X

/-- Equivalence with Mathlib's `Denumerable` concept (cf. Remark 8.1.2) -/
theorem CountablyInfinite.iff (X : Type) : CountablyInfinite X ↔ Nonempty (Denumerable X) := by
  simp [CountablyInfinite, EqualCard.iff]
  constructor
  . rintro ⟨ e ⟩
    exact ⟨ Denumerable.mk' e ⟩
  rintro ⟨ h ⟩
  exact ⟨ Denumerable.eqv X ⟩

/-- Equivalence with Mathlib's `Countable` typeclass -/
theorem CountablyInfinite.iff' (X : Type) : CountablyInfinite X ↔ Countable X ∧ Infinite X := by
  rw [iff, nonempty_denumerable_iff]

theorem AtMostCountable.iff (X : Type) : AtMostCountable X ↔ Countable X := by
  have h1 := CountablyInfinite.iff' X
  have h2 : ¬ Finite X ↔ Infinite X := not_finite_iff_infinite
  have h3 : Finite X → Countable X := by intro h; exact Finite.to_countable
  unfold AtMostCountable; tauto

theorem CountablyInfinite.iff_image_inj {A:Type} (X: Set A) : CountablyInfinite X ↔ ∃ f : ℕ ↪ A, X = f '' Set.univ := by
  constructor
  . rintro ⟨ g, hg ⟩
    obtain ⟨ f, hleft, hright ⟩ := Function.bijective_iff_has_inverse.mp hg
    refine ⟨ ⟨ Subtype.val ∘ f, ?_ ⟩, ?_ ⟩
    . intro x y hxy; simp [Subtype.val_inj] at hxy
      rw [←hright x, ←hright y, hxy]
    ext x; simp; constructor
    . intro hx; use g ⟨ x, hx ⟩; simp [hleft _]
    rintro ⟨ n, rfl ⟩; aesop
  rintro ⟨ f, hf ⟩
  have := Function.leftInverse_invFun (Function.Embedding.injective f)
  set g := Function.invFun f
  use g ∘ Subtype.val
  constructor
  . rintro ⟨ x, hx ⟩ ⟨ y, hy ⟩ h
    simp [hf] at h ⊢ hx hy
    obtain ⟨ n, rfl ⟩ := hx
    obtain ⟨ m, rfl ⟩ := hy
    simp [this n, this m] at h; aesop
  intro n; use ⟨ f n, by aesop ⟩
  simp [this n]

/-- Examples 8.1.3 -/
example : CountablyInfinite ℕ := by sorry

example : CountablyInfinite (Set.univ \ {0}: Set ℕ) := by sorry

example : CountablyInfinite ((fun n:ℕ ↦ 2*n) '' Set.univ) := by sorry


/-- Proposition 8.1.4 (Well ordering principle / Exercise 8.1.2 -/
theorem Nat.exists_unique_min {X : Set ℕ} (hX : X.Nonempty) :
  ∃! m ∈ X, ∀ n ∈ X, m ≤ n := by
  sorry

open Classical in
noncomputable abbrev Nat.min (X : Set ℕ) : ℕ := if hX : X.Nonempty then (exists_unique_min hX).exists.choose else 0

theorem Nat.min_spec {X : Set ℕ} (hX : X.Nonempty) :
  min X ∈ X ∧ ∀ n ∈ X, min X ≤ n := by
  simp [hX, min]
  exact (exists_unique_min hX).exists.choose_spec

theorem Nat.min_eq {X : Set ℕ} (hX : X.Nonempty) {a:ℕ} (ha : a ∈ X ∧ ∀ n ∈ X, a ≤ n) : min X = a :=
  (exists_unique_min hX).unique (min_spec hX) ha

@[simp]
theorem Nat.min_empty : min ∅ = 0 := by
  simp [Nat.min]

example : Nat.min ((fun n ↦ 2*n) '' (Set.Ici 1)) = 2 := by sorry

theorem Nat.min_eq_inf {X : Set ℕ} (hX : X.Nonempty) : min X = sInf X := by
  sorry

open Classical in
/-- Equivalence with Mathlib's `Nat.find` method -/
theorem Nat.min_eq_find {X : Set ℕ} (hX : X.Nonempty) : min X = Nat.find hX := by
  symm; rw [Nat.find_eq_iff]
  have := min_spec hX
  simp [this]
  intro n hn; contrapose! hn; exact this.2 n hn



end Chapter8
