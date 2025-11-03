import Mathlib

open Classical
open scoped BigOperators

/-- “Color-`col` monochromatic star of size `k`”: there is a center `x` and a set `S`
    of `k` distinct neighbors of `x` such that every edge `{x,y}` with `y ∈ S`
    is present in `G` and colored `col`.  (No restriction on edges inside `S`.) -/
def hasMonoStar {V:Type*} (G : SimpleGraph V) (color : Sym2 V → Fin 2)
    (col : Fin 2) (k : ℕ) : Prop :=
  ∃ (x : V) (S : Finset V),
    S.card = k ∧
    x ∉ S ∧
    ∀ ⦃y : V⦄, y ∈ S → G.Adj x y ∧ color (Sym2.mk x y) = col

/-- “Color-`col` monochromatic triangle”: there exist `a b c` with all three edges
    present in `G` and colored `col`.  (Adjacency already forces distinctness.) -/
def hasMonoTriangle {V:Type*} (G : SimpleGraph V) (color : Sym2 V → Fin 2)
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
  ∃ (V:Type*) (G : SimpleGraph V),
    G.edgeSet.ncard = 44 ∧
    ∀ (color : Sym2 V → Fin 2),
      hasMonoStar G color 0 5 ∨ hasMonoTriangle G color 1


namespace PikhurkoN5

/-- Vertex type with 2 + 5 + 3 + 5 + 1 = 16 vertices. -/
inductive V
| A1 (i : Fin 2)  -- the K₂ part of P_{2,5}
| B1 (j : Fin 5)  -- the independent part of P_{2,5}
| A2 (i : Fin 3)  -- the K₃ part of P_{3,5}
| B2 (j : Fin 5)  -- the independent part of P_{3,5}
| apex            -- the universal vertex
deriving DecidableEq, Repr

open V

/-- Adjacency relation for the Pikhurko n=5 counterexample.

* Inside `A1` and inside `A2`: cliques.
* Between `A1`–`B1` and `A2`–`B2`: complete bipartite.
* Inside `B1` and `B2`: no edges.
* No edges between the two blocks `{A1,B1}` and `{A2,B2}`.
* `apex` is connected to every non-`apex` vertex. -/
def GAdj : V → V → Prop
| apex, apex => False
| apex, _    => True
| _,    apex => True
| A1 i, A1 j => i ≠ j
| A2 i, A2 j => i ≠ j
| A1 _, B1 _ => True
| B1 _, A1 _ => True
| A2 _, B2 _ => True
| B2 _, A2 _ => True
| _,    _    => False

/-- The graph `G` on 16 vertices used for the n=5 counterexample. -/
def G : SimpleGraph V where
  Adj := GAdj
  symm := by
    intro u v h
    cases u <;> cases v <;> simpa [GAdj] using h
  loopless := by
    intro v
    cases v <;> simp [GAdj]

/-!
Convenience simp lemmas. These are optional but help when you start proving
properties about colorings later on.
-/
@[simp] lemma adj_apex_left {v : V} : G.Adj V.apex v ↔ v ≠ V.apex := by
  cases v <;> simp [G, GAdj]

@[simp] lemma adj_apex_right {v : V} : G.Adj v V.apex ↔ v ≠ V.apex := by
  cases v <;> simp [G, GAdj]

@[simp] lemma adj_A1A1 {i j} : G.Adj (A1 i) (A1 j) ↔ i ≠ j := by
  simp [G, GAdj]

@[simp] lemma adj_A2A2 {i j} : G.Adj (A2 i) (A2 j) ↔ i ≠ j := by
  simp [G, GAdj]

@[simp] lemma adj_A1B1 {i j} : G.Adj (A1 i) (B1 j) := by
  simp [G, GAdj]

@[simp] lemma adj_A2B2 {i j} : G.Adj (A2 i) (B2 j) := by
  simp [G, GAdj]

@[simp] lemma no_adj_B1B1 {j j'} : ¬ G.Adj (B1 j) (B1 j') := by
  simp [G, GAdj]

@[simp] lemma no_adj_B2B2 {j j'} : ¬ G.Adj (B2 j) (B2 j') := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_A1B2 {i j} : ¬ G.Adj (A1 i) (B2 j) := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_A2B1 {i j} : ¬ G.Adj (A2 i) (B1 j) := by
  simp [G, GAdj]

end PikhurkoN5
