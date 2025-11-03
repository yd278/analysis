import Mathlib/Combinatorics/SimpleGraph/Basic
import Mathlib/Data/Sym2
import Mathlib/Data/Finset/Basic

open Classical
open scoped BigOperators

/-- We'll fix the vertex type to be `Fin 16`. -/
abbrev V := Fin 16

/-- “Color-`col` monochromatic star of size `k`”: there is a center `x` and a set `S`
    of `k` distinct neighbors of `x` such that every edge `{x,y}` with `y ∈ S`
    is present in `G` and colored `col`.  (No restriction on edges inside `S`.) -/
def hasMonoStar (G : SimpleGraph V) (color : Sym2 V → Fin 2)
    (col : Fin 2) (k : ℕ) : Prop :=
  ∃ (x : V) (S : Finset V),
    S.card = k ∧
    x ∉ S ∧
    ∀ ⦃y : V⦄, y ∈ S → G.Adj x y ∧ color (Sym2.mk x y) = col

/-- “Color-`col` monochromatic triangle”: there exist `a b c` with all three edges
    present in `G` and colored `col`.  (Adjacency already forces distinctness.) -/
def hasMonoTriangle (G : SimpleGraph V) (color : Sym2 V → Fin 2)
    (col : Fin 2) : Prop :=
  ∃ a b c : V,
    G.Adj a b ∧ G.Adj b c ∧ G.Adj a c ∧
    color (Sym2.mk a b) = col ∧
    color (Sym2.mk b c) = col ∧
    color (Sym2.mk a c) = col

/-- **Statement (n = 5 case of Pikhurko’s counterexample).**
There exists a simple graph on `16` vertices with exactly `44` edges such that
for *every* 2‑coloring of unordered pairs, either color `0` contains a `K_{1,5}`
(a 5‑edge star) or color `1` contains a `K₃` (a triangle).

This only *states* the claim (as a `Prop`).  You can later prove it from the
explicit construction, or assume it as an axiom while you develop the rest. -/
def Pikhurko_n5_statement : Prop :=
  ∃ (G : SimpleGraph V),
    G.edgeSet.ncard = 44 ∧
    ∀ (color : Sym2 V → Fin 2),
      hasMonoStar G color 0 5 ∨ hasMonoTriangle G color 1
