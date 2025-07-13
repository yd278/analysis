import Mathlib.Tactic

/-!
# API for ExistsUnique

Here we review some of the API provided for `ExistsUnique` in Mathlib, and provide some additional tools.

-/


#check existsUnique_of_exists_of_unique
#check ExistsUnique.exists
#check ExistsUnique.unique
#check ExistsUnique.intro

noncomputable def ExistsUnique.choose {α: Sort*} {p: α → Prop} (h : ∃! x, p x) : α := h.exists.choose

theorem ExistsUnique.choose_spec {α: Sort*} {p: α → Prop} (h : ∃! x, p x) :
  p h.choose := h.exists.choose_spec

theorem ExistsUnique.choose_eq {α: Sort*} {p: α → Prop} (h : ∃! x, p x) {x : α} (hx : p x) :
  h.choose = x := h.unique h.choose_spec hx

theorem ExistsUnique.choose_iff {α: Sort*} {p: α → Prop} (h : ∃! x, p x) (x : α):
  p x ↔ x = h.choose :=
  ⟨ by intro hx; exact (h.choose_eq hx).symm, by rintro rfl; exact h.choose_spec ⟩
