import Mathlib

open Classical
open scoped BigOperators


-- 1. Define the main claim

/-- “Color-`col` monochromatic star of size `k`”: there is a center `x` and a set `S`
    of `k` distinct neighbors of `x` such that every edge `{x,y}` with `y ∈ S`
    is present in `G` and colored `col`.  (No restriction on edges inside `S`.) -/
def hasMonoStar {V:Type*} (G : SimpleGraph V) (color : Sym2 V → Fin 2)
    (col : Fin 2) (k : ℕ) : Prop :=
  ∃ (x : V) (S : Finset V),
    S.card = k ∧
    x ∉ S ∧
    ∀ ⦃y : V⦄, y ∈ S → G.Adj x y ∧ color (Sym2.mk (x, y)) = col

/-- “Color-`col` monochromatic triangle”: there exist `a b c` with all three edges
    present in `G` and colored `col`.  (Adjacency already forces distinctness.) -/
def hasMonoTriangle {V:Type*} (G : SimpleGraph V) (color : Sym2 V → Fin 2)
    (col : Fin 2) : Prop :=
  ∃ a b c : V,
    G.Adj a b ∧ G.Adj b c ∧ G.Adj a c ∧
    color (Sym2.mk (a, b)) = col ∧
    color (Sym2.mk (b, c)) = col ∧
    color (Sym2.mk (a, c)) = col

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


-- 2. Construct the graph

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
    cases u <;> cases v <;> grind [GAdj]
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

@[simp] lemma adj_B1A1 {i j} : G.Adj (B1 i) (A1 j) := by
  simp [G, GAdj]

@[simp] lemma adj_A2B2 {i j} : G.Adj (A2 i) (B2 j) := by
  simp [G, GAdj]

@[simp] lemma adj_B2A2 {i j} : G.Adj (B2 j) (A2 i)  := by
  simp [G, GAdj]

@[simp] lemma no_adj_B1B1 {j j'} : ¬ G.Adj (B1 j) (B1 j') := by
  simp [G, GAdj]

@[simp] lemma no_adj_B2B2 {j j'} : ¬ G.Adj (B2 j) (B2 j') := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_A1B2 {i j} : ¬ G.Adj (A1 i) (B2 j) := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_A2B1 {i j} : ¬ G.Adj (A2 i) (B1 j) := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_B1A2 {i j} : ¬ G.Adj (B1 j) (A2 i)  := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_B1B2 {i j} : ¬ G.Adj (B1 j) (B2 i)  := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_A2A1 {i j} : ¬ G.Adj (A2 j) (A1 i)  := by
  simp [G, GAdj]

end PikhurkoN5


-- 3.  Count edges

namespace PikhurkoN5

open V

/- We’ll need `Fintype` on `V` for `univ`, sums, etc. -/
deriving instance Fintype for V

/-- An explicit equivalence showing `V` has 2+5+3+5+1 = 16 elements. -/
def VEquiv :
    V ≃ ((((Fin 2 ⊕ Fin 5) ⊕ Fin 3) ⊕ Fin 5) ⊕ Unit) where
  toFun
  | A1 i  => Sum.inl (Sum.inl (Sum.inl (Sum.inl i)))
  | B1 j  => Sum.inl (Sum.inl (Sum.inl (Sum.inr j)))
  | A2 i  => Sum.inl (Sum.inl (Sum.inr i))
  | B2 j  => Sum.inl (Sum.inr j)
  | apex  => Sum.inr ()
  invFun
  | Sum.inl (Sum.inl (Sum.inl (Sum.inl i))) => A1 i
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr j))) => B1 j
  | Sum.inl (Sum.inl (Sum.inr i))            => A2 i
  | Sum.inl (Sum.inr j)                      => B2 j
  | Sum.inr ()                               => apex
  left_inv v := by cases v <;> grind
  right_inv w := by cases w <;> grind

/-- `|V| = 16`. Useful for quick cardinality arithmetic. -/
lemma card_V : Fintype.card V = 16 := by
  -- Reduce to the nested-sum cardinality and compute arithmetically.
  simpa using
    (Fintype.card_congr VEquiv).trans <|
      by
        -- `simp` turns cardinals of sums into sums of cardinals; `norm_num` does the rest.
        simp [Fintype.card_sum, Fintype.card_fin]

/-! ## Degree computations

We compute the degree of each vertex *kind*. We’ll use your `[simp]` adjacency
lemmas from Approach A:
- `adj_apex_left`, `adj_A1A1`, `adj_A2A2`, `adj_A1B1`, `adj_A2B2`,
  and the corresponding “no edge” lemmas across blocks.
-/

/-- `deg(apex) = 15`. -/
lemma degree_apex : G.degree apex = 15 := by
  classical
  -- Neighbors of `apex` are exactly all vertices ≠ `apex`.
  have hN :
      G.neighborFinset apex = (Finset.univ.erase apex) := by
    ext v; constructor
    · intro hv
      have : G.Adj apex v := by simpa using hv
      have hvne : v ≠ apex := by simpa [adj_apex_left] using this
      simpa [Finset.mem_erase] using And.intro hvne (by simp : v ∈ (Finset.univ : Finset V))
    · intro hv
      have hvne : v ≠ apex := (Finset.mem_erase.mp hv).1
      have : G.Adj apex v := by simpa [adj_apex_left] using hvne
      simpa using this
  -- Count `univ.erase apex`.
  have : (G.neighborFinset apex).card = 15 := by
    -- `card (erase univ apex) = |V| - 1 = 16 - 1 = 15`
    have : (Finset.univ.erase apex).card = Fintype.card V - 1 := by
      have : apex ∈ (Finset.univ : Finset V) := by simp
      simp [Finset.card_erase_of_mem, this]
    simp [hN, card_V]
  -- `degree` is the cardinal of the neighbor finset.
  simp at this
  assumption

/-- `deg(A1 i) = 7` for each `i`. -/
lemma degree_A1 (i : Fin 2) : G.degree (A1 i) = 7 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 1 + 5 + 0 + 0 + 1 := by
      congr
      . calc
        _ = Finset.card {j | j ≠ i} := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
          grind
        _ = 1 := by
          fin_cases i <;> simp
          . convert Finset.card_singleton 1
          convert Finset.card_singleton 0
      . calc
        _ = Finset.card (Finset.univ : Finset (Fin 5)) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 5 := by simp [Fintype.card_fin]
      . calc
        _ = Finset.card (∅ : Finset (Fin 3)) := by
          congr; ext; simp [-iff_false]
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
          aesop
        _ = 0 := by simp
      . calc
        _ = Finset.card (∅: Finset (Fin 5)) := by
          congr; ext; simp [-iff_false]
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 0 := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 1 := by simp
    _ = _ := by norm_num

/-- `deg(B1 j) = 3` for each `j`. (Two `A1`s + apex.) -/
lemma degree_B1 (j : Fin 5) : G.degree (B1 j) = 3 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 2 + 0 + 0 + 0 + 1 := by
      congr
      . calc
          _ = Finset.card (Finset.univ : Finset (Fin 2)) := by
            congr; ext; simp
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 3)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 1 := by simp
    _ = _ := by norm_num



/-- `deg(A2 i) = 8` for each `i`. (Two inside `A2` + five in `B2` + apex.) -/
lemma degree_A2 (i : Fin 3) : G.degree (A2 i) = 8 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 0 + 0 + 2 + 5 + 1 := by
      congr
      . calc
          _ = Finset.card (∅ : Finset (Fin 2)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card {j | j ≠ i} := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
            grind
          _ = _ := by
            convert Finset.card_erase_of_mem (show i ∈ Finset.univ by simp)
            grind
      . calc
          _ = Finset.card (Finset.univ: Finset (Fin 5)) := by
            congr; ext; simp
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 1 := by simp
    _ = _ := by norm_num


/-- `deg(B2 j) = 4` for each `j`. (Three `A2`s + apex.) -/
lemma degree_B2 (j : Fin 5) : G.degree (B2 j) = 4 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 0 + 0 + 3 + 0 + 1 := by
      congr
      . calc
          _ = Finset.card (∅ : Finset (Fin 2)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      . calc
          _ = Finset.card (Finset.univ : Finset (Fin 3)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv, G, GAdj]
        _ = 1 := by simp
    _ = _ := by norm_num

/-!
### Edge count via the handshaking lemma
We now sum the degrees and divide by 2.
-/
theorem edge_count_44 : G.edgeSet.ncard = 44 := by
  classical
  -- Handshaking lemma on edge *set* cardinality.
  -- In current mathlib this comes as:
  --   `G.sum_degrees_eq_twice_card_edgeSet : (∑ v, G.degree v) = 2 * G.edgeSet.ncard`.
  have hand := G.sum_degrees_eq_twice_card_edges
  rw [←SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [←Equiv.sum_comp VEquiv.symm _] at hand
  simp_rw [Fintype.sum_sum_type] at hand
  simp [VEquiv, degree_A1, degree_B1, degree_A2, degree_B2, degree_apex, -Set.toFinset_card] at hand
  grind

end PikhurkoN5


-- 4. Show red neighbors of apex are ≥ 11 if no blue K_{1,5}

namespace PikhurkoN5
open V

/-! ### Small utilities -/

/- Pick a `k`-subset of a finset `s` when `k ≤ s.card`. -/
namespace Finset
variable {α : Type*}

lemma exists_subset_card_eq (s : Finset α) {k : ℕ} (hk : k ≤ s.card) :
  ∃ t ⊆ s, t.card = k := by
  exact Finset.le_card_iff_exists_subset_card.mp hk

end Finset

/-- In `Fin 2`, saying “equals `1`” is the same as “not equal to `0`”. -/
lemma fin2_eq_one_iff_ne_zero (a : Fin 2) : (a = 1) ↔ a ≠ 0 := by
  fin_cases a <;> simp

/-! ### Red neighbors of the apex are ≥ 11 if there is no blue star K_{1,5} -/

/-- The set of blue neighbors of `apex` in color class `0`. -/
noncomputable def blueNeighbors (color : Sym2 V → Fin 2) : Finset V :=
  (G.neighborFinset apex).filter (fun v => color (Sym2.mk (apex, v)) = 0)

/-- The set of red neighbors of `apex` in color class `1`. -/
noncomputable def redNeighbors (color : Sym2 V → Fin 2) : Finset V :=
  (G.neighborFinset apex).filter (fun v => color (Sym2.mk (apex, v)) = 1)

/-- If there is no blue `K_{1,5}`, then the apex has at most 4 blue neighbors. -/
lemma blueNeighbors_card_le_4
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
    (blueNeighbors color).card ≤ 4 := by
  classical
  -- Suppose ≥5 blue neighbors; extract a 5-subset and get a blue star.
  by_contra hle
  have hge : 5 ≤ (blueNeighbors color).card :=
    Nat.succ_le_of_lt (lt_of_not_ge hle)
  obtain ⟨S, hSsubset, hScard⟩ :=
    Finset.exists_subset_card_eq (blueNeighbors color) hge

  -- `apex ∉ S` since `apex` is not its own neighbor.
  have hapex_notin : apex ∉ S := by
    have : apex ∉ G.neighborFinset apex := by
      -- No loops ⇒ apex not adjacent to itself ⇒ not in neighbor set.
      simp [SimpleGraph.neighborFinset]
    exact fun hx => this <| (by
      have hx' : apex ∈ blueNeighbors color := hSsubset hx
      -- Blue neighbors are a subset of neighbors.
      have : blueNeighbors color ⊆ G.neighborFinset apex :=
        by
          intro v hv
          exact Finset.mem_of_mem_filter _ hv
      exact this hx')

  -- All edges from `apex` to `S` are present and blue, so we have a blue K_{1,5}.
  have hstar : hasMonoStar G color 0 5 := by
    refine ⟨apex, S, hScard, hapex_notin, ?_⟩
    intro y hy
    have hy' : y ∈ blueNeighbors color := hSsubset hy
    have hy_in : y ∈ G.neighborFinset apex ∧ color (Sym2.mk (apex, y)) = 0 := by
      simpa [blueNeighbors] using hy'
    exact ⟨by simpa using hy_in.1, hy_in.2⟩

  exact hNoBlueStar hstar

/-- If there is no blue `K_{1,5}`, then at least `11` neighbors of `apex` are red. -/
lemma red_from_apex_at_least_11
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
    (redNeighbors color).card ≥ 11 := by
  classical
  -- Split neighbors of apex into blue vs. non-blue; identify non-blue with red.
  have hsplit :
      (blueNeighbors color).card
      + ((G.neighborFinset apex).filter (fun v => ¬ (color (Sym2.mk (apex, v)) = 0))).card
      = (G.neighborFinset apex).card := by
    simpa [blueNeighbors] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := G.neighborFinset apex)
        (p := fun v => color (Sym2.mk (apex, v)) = 0))

  have hred_is_notblue :
      (G.neighborFinset apex).filter (fun v => ¬ (color (Sym2.mk (apex, v)) = 0))
      =
      redNeighbors color := by
    ext v; by_cases hv : v ∈ G.neighborFinset apex
    · -- On neighbors, “not blue” is “red”.
      simp [redNeighbors, hv, fin2_eq_one_iff_ne_zero]
    · simp [redNeighbors, hv]

  -- So blue + red = all neighbors = 15 (by `degree_apex`).
  have hsum : (blueNeighbors color).card + (redNeighbors color).card
              = (G.neighborFinset apex).card := by
    convert Finset.card_sdiff_add_card_eq_card _
    . simp [←hred_is_notblue, blueNeighbors]
      grind
    . infer_instance
    simp [redNeighbors]


  have hdeg : (G.neighborFinset apex).card = 15 := by
    simp [degree_apex]

  have hblue_le_4 := blueNeighbors_card_le_4 color hNoBlueStar

  -- Turn `blue + red = 15` into `red = 15 - blue`.
  have hred_eq : (redNeighbors color).card
      = 15 - (blueNeighbors color).card := by
    have hsum' : (redNeighbors color).card + (blueNeighbors color).card = 15 := by
      simpa [Nat.add_comm, hdeg] using hsum
    have := congrArg (fun t => t - (blueNeighbors color).card) hsum'
    -- `(red + blue) - blue = 15 - blue` ⇒ `red = 15 - blue`.
    simpa [Nat.add_sub_cancel] using this

  -- Finally: `blue ≤ 4` ⇒ `15 - blue ≥ 11`.
  have : 11 ≤ 15 - (blueNeighbors color).card :=
    by grind

  -- Combine with `red = 15 - blue`.
  simpa [hred_eq] using this

end PikhurkoN5
