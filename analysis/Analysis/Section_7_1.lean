import Mathlib.Tactic

/-!
# Analysis I, Section 7.1: Finite series

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Technical note: it is convenient in Lean to extend finite sequences (usually by zero) to be
functions on the entire integers.

Main constructions and results of this section:
-/

-- This makes available the convenient notation `∑ n ∈ A, f n` to denote summation of `f n` for
-- `n` ranging over a finite set `A`.
open BigOperators

/-!
- API for summation over finite sets (encoded using Mathlib's `Finset` type), using the
  `Finset.sum` method and the `∑ n ∈ A, f n` notation.
- Fubini's theorem for finite series

We do not attempt to replicate the full API for `Finset.sum` here, but in subsequent sections we
shall make liberal use of this API.

-/

-- This is a technical device to avoid Mathlib's insistence on decidable equality for finite sets.
open Classical

namespace Finset

-- We use `Finset.Icc` to describe finite intervals in the integers. `Finset.mem_Icc` is the
-- standard Mathlib tool for checking membership in such intervals.
#check mem_Icc

/-- Definition 7.1.1 -/
theorem sum_of_empty {n m:ℤ} (h: n < m) (a: ℤ → ℝ) : ∑ i ∈ Icc m n, a i = 0 := by
  rw [sum_eq_zero]; intro _; rw [mem_Icc]; grind

/--
  Definition 7.1.1. This is similar to Mathlib's `Finset.sum_Icc_succ_top` except that the
  latter involves summation over the natural numbers rather than integers.
-/
theorem sum_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) :
    ∑ i ∈ Icc m (n+1), a i = ∑ i ∈ Icc m n, a i + a (n+1) := by
  rw [add_comm _ (a (n+1))]
  convert sum_insert _
  . ext; simp; omega
  . infer_instance
  simp

-- actually, rw[mem_Icc] and simp it
example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-2), a i = 0 := by simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-1), a i = 0 := by simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m m, a i = a m := by simp

lemma Example_7_1_2 (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+1), a i = a m + a (m+1) := by
  have  : ∑ i ∈ Icc m m, a i = a m := by simp
  rw[add_comm _ (a (m + 1)), ← this]
  convert sum_insert _
  . ext; simp; omega
  . infer_instance
  simp
example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+1), a i = a m + a (m+1) := by
  exact Example_7_1_2 a m

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+2), a i = a m + a (m+1) + a (m+2) := by
  have := Example_7_1_2 a m
  rw[← this,add_comm _ (a (m+2))]
  convert sum_insert _
  . ext; simp; omega
  . infer_instance
  simp


/-- Remark 7.1.3 -/
example (a: ℤ → ℝ) (m n:ℤ) : ∑ i ∈ Icc m n, a i = ∑ j ∈ Icc m n, a j := rfl

/-- Lemma 7.1.4(a) / Exercise 7.1.1 -/
theorem concat_finite_series {m n p:ℤ} (hmn: m ≤ n+1) (hpn : n ≤ p) (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc (n+1) p, a i = ∑ i ∈ Icc m p, a i := by
    replace hmn : m - 1 ≤ n := by omega
    induction' n, hmn using Int.le_induction with k hk hind
    . simp
    specialize hind (by omega)
    rw[sum_of_nonempty hk a,← hind,add_assoc]
    congr;symm
    convert sum_insert _
    . ext;simp;omega
    . infer_instance
    simp

/-- Lemma 7.1.4(b) / Exercise 7.1.1 -/
theorem shift_finite_series {m n k:ℤ} (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i = ∑ i ∈ Icc (m+k) (n+k), a (i-k) := by
    by_cases hnm : n < m
    . observe hnm' : (n+k) < (m+k)
      rw[sum_of_empty hnm,sum_of_empty hnm']
    simp at hnm
    induction' n,hnm using Int.le_induction with n hn hind
    . simp
    rw[sum_of_nonempty (by omega),hind,add_comm _ (a (n+1)),show a (n+1) = a (n + 1 + k - k) by simp]
    symm
    convert sum_insert _
    . ext;simp;omega
    . infer_instance
    simp

/-- Lemma 7.1.4(c) / Exercise 7.1.1 -/
theorem finite_series_add {m n:ℤ} (a b: ℤ → ℝ) :
  ∑ i ∈ Icc m n, (a i + b i) = ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc m n, b i := by
    by_cases hnm : n < m
    . simp[sum_of_empty hnm]
    simp at hnm
    induction' n,hnm using Int.le_induction with n hn hind
    . simp
    have hnm' : n ≥ m-1 := by omega
    simp[sum_of_nonempty hnm', hind]
    ring

/-- Lemma 7.1.4(d) / Exercise 7.1.1 -/
theorem finite_series_const_mul {m n:ℤ}  (a: ℤ → ℝ) (c:ℝ) :
  ∑ i ∈ Icc m n, c * a i = c * ∑ i ∈ Icc m n, a i := by
    by_cases hnm : n < m
    . simp[sum_of_empty hnm]
    simp at hnm
    induction' n,hnm using Int.le_induction with n hn hind
    . simp
    have hnm' : n ≥ m-1 := by omega
    simp[sum_of_nonempty hnm', hind]
    ring

/-- Lemma 7.1.4(e) / Exercise 7.1.1 -/
theorem abs_finite_series_le {m n:ℤ}   (a: ℤ → ℝ)  :
  |∑ i ∈ Icc m n, a i| ≤ ∑ i ∈ Icc m n, |a i| := by
    by_cases hnm : n < m
    . simp[sum_of_empty hnm]
    simp at hnm
    induction' n,hnm using Int.le_induction with n hn hind
    . simp
    have hnm' : n ≥ m-1 := by omega
    simp_rw[sum_of_nonempty hnm']
    calc
      _ ≤ |∑ i ∈ Icc m n, a i| + |a (n+1)| := by apply abs_add_le
      _ ≤ _ := by gcongr

/-- Lemma 7.1.4(f) / Exercise 7.1.1 -/
theorem finite_series_of_le {m n:ℤ}  {a b: ℤ → ℝ} (h: ∀ i, m ≤ i → i ≤ n → a i ≤ b i) :
  ∑ i ∈ Icc m n, a i ≤ ∑ i ∈ Icc m n, b i := by
    by_cases hnm : n < m
    . simp[sum_of_empty hnm]
    simp at hnm
    induction' n,hnm using Int.le_induction with n hn hind
    . simp[h m]
    specialize hind (by
      peel h with i hm h
      intro hn
      exact h (by omega)
    )
    have hnm' : n ≥ m-1 := by omega
    simp_rw[sum_of_nonempty hnm']
    specialize h (n+1) (by linarith) (by simp)
    linarith

#check sum_congr
/--
  Proposition 7.1.8.
-/
theorem finite_series_of_rearrange {n:ℕ} {X':Type*} (X: Finset X') (hcard: X.card = n)
  (f: X' → ℝ) (g h: Icc (1:ℤ) n → X) (hg: Function.Bijective g) (hh: Function.Bijective h) :
    ∑ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0)
    = ∑ i ∈ Icc (1:ℤ) n, (if hi: i ∈ Icc (1:ℤ) n then f (h ⟨ i, hi ⟩) else 0) := by
  -- This proof is written to broadly follow the structure of the original text.
  revert X n; intro n
  induction' n with n hn
  . simp
  intro X hX g h hg hh
  -- A technical step: we extend g, h to the entire integers using a slightly artificial map π
  set π : ℤ → Icc (1:ℤ) (n+1) :=
    fun i ↦ if hi: i ∈ Icc (1:ℤ) (n+1) then ⟨ i, hi ⟩ else ⟨ 1, by simp ⟩
  have hπ (g : Icc (1:ℤ) (n+1) → X) :
      ∑ i ∈ Icc (1:ℤ) (n+1), (if hi:i ∈ Icc (1:ℤ) (n+1) then f (g ⟨ i, hi ⟩) else 0)
      = ∑ i ∈ Icc (1:ℤ) (n+1), f (g (π i)) := by
    apply sum_congr rfl _
    intro i hi; simp [hi, π, -mem_Icc]
  simp [-mem_Icc, hπ]
  rw [sum_of_nonempty (by linarith) _]
  set x := g (π (n+1))
  have ⟨⟨j, hj'⟩, hj⟩ := hh.surjective x
  simp at hj'; obtain ⟨ hj1, hj2 ⟩ := hj'
  set h' : ℤ → X := fun i ↦ if (i:ℤ) < j then h (π i) else h (π (i+1))
  have : ∑ i ∈ Icc (1:ℤ) (n + 1), f (h (π i)) = ∑ i ∈ Icc (1:ℤ) n, f (h' i) + f x := calc
    _ = ∑ i ∈ Icc (1:ℤ) j, f (h (π i)) + ∑ i ∈ Icc (j+1:ℤ) (n + 1), f (h (π i)) := by
      symm; apply concat_finite_series <;> linarith
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + f ( h (π j) )
        + ∑ i ∈ Icc (j+1:ℤ) (n + 1), f (h (π i)) := by
      congr; convert sum_of_nonempty _ _ <;> simp [hj1]
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + f x + ∑ i ∈ Icc (j:ℤ) n, f (h (π (i+1))) := by
      congr 1
      . simp [←hj, π,hj1, hj2]
      symm; convert shift_finite_series _; simp
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + ∑ i ∈ Icc (j:ℤ) n, f (h (π (i+1))) + f x := by abel
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h' i) + ∑ i ∈ Icc (j:ℤ) n, f (h' i) + f x := by
      congr 2
      all_goals apply sum_congr rfl _; intro i hi; simp [h'] at *
      . simp [show i < j by linarith]
      simp [show ¬ i < j by linarith]
    _ = _ := by congr; convert concat_finite_series _ _ _ <;> linarith
  rw [this]
  congr 1
  have g_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : g (π i) ≠ x := by
    simp at hi
    simp [x, hg.injective.eq_iff, π, hi.1, show i ≤ n+1 by linarith]
    linarith
  have h'_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : h' i ≠ x := by
    simp at hi
    have hi' : 0 ≤ i := by linarith
    have hi'' : i ≤ n+1 := by linarith
    by_cases hlt: i < j <;> by_contra! heq
    all_goals simp [h', hlt, ←hj, hh.injective.eq_iff, ←Subtype.val_inj,
                    π, hi.1, hi.2, hi',hi''] at heq
    . linarith
    contrapose! hlt; linarith
  set gtil : Icc (1:ℤ) n → X.erase x :=
    fun i ↦ ⟨ (g (π i)).val, by simp [mem_erase, Subtype.val_inj, g_ne_x] ⟩
  set htil : Icc (1:ℤ) n → X.erase x :=
    fun i ↦ ⟨ (h' i).val, by simp [mem_erase, Subtype.val_inj, h'_ne_x] ⟩
  set ftil : X.erase x → ℝ := fun y ↦ f y.val
  have hπinj {i j:ℤ} (hi: i ∈ Icc (1:ℤ) (n+1)) (hj: j ∈ Icc (1:ℤ) (n+1)) (heq: π i = π j): i= j := by 
    simpa[π, -mem_Icc, hi,hj] using heq
  -- gtil is basically g, so simply use hg 
  have why : Function.Bijective gtil := by
    have hmap {x} {hx}: (gtil ⟨x,hx⟩).val = (g ( π x)).val := by
      simp[gtil]
    constructor
    . rintro ⟨a,ha⟩ ⟨b,hb⟩ heq  
      have ha' : a ∈ Icc (1:ℤ) (n+1) := by 
        apply mem_of_subset ?_ ha
        apply Icc_subset_Icc_right
        simp
      have hb' : b ∈ Icc (1:ℤ) (n+1) := by 
        apply mem_of_subset ?_ hb
        apply Icc_subset_Icc_right
        simp
      simp_rw[← Subtype.val_inj,hmap,Subtype.val_inj] at heq
      simp[← Subtype.val_inj]
      apply hπinj ha' hb'
      apply hg.injective heq
    rintro ⟨x',hx'E⟩ 
    obtain ⟨⟨a,ha⟩,ha'⟩ := hg.surjective ⟨x',mem_of_mem_erase hx'E⟩ 
    suffices han : a ∈ Icc (1:ℤ) n from by
      use ⟨a,han⟩ 
      push_cast at ha
      simp[← Subtype.val_inj] at ha'
      simp[← Subtype.val_inj,hmap,← ha']
      simp[π, -mem_Icc,Subtype.val_inj]
      simp[ha]
    simp at ⊢ ha
    suffices han : a ≠ n+1 from by 
      refine ⟨ha.1,?_⟩ 
      rw[Int.le_iff_lt_add_one]
      apply lt_of_le_of_ne ha.2 han
    by_contra! han
    have hx'N := ne_of_mem_erase hx'E
    simp[← Subtype.val_inj] at ha'
    simp[x,π,← han,ha,← ha'] at hx'N
  -- 
  have why2 : Function.Bijective htil := by
    constructor
    . rintro ⟨a,ha⟩  ⟨b,hb⟩  heq
      have ha' : a ∈ Icc (1:ℤ) (n+1) := by 
        simp at ha ⊢
        omega
      have hb' : b ∈ Icc (1:ℤ) (n+1) := by 
        simp at hb ⊢
        omega
      have ha'1 : (a+1) ∈ Icc (1:ℤ) (n+1) := by
        simp at ha ⊢ 
        omega
      have hb'1 : (b+1) ∈ Icc (1:ℤ) (n+1) := by 
        simp at hb ⊢
        omega
      simp[htil,Subtype.val_inj] at heq
      apply Subtype.eq;simp
      simp[h'] at heq;split_ifs at heq with haj hbj
      . have := hh.injective heq
        simpa[π,-mem_Icc,ha',hb'] using this
      . have := hh.injective heq
        simp[π,-mem_Icc,ha',hb'1] at this
        omega
      . have := hh.injective heq
        simp[π,-mem_Icc,ha'1,hb'] at this
        omega
      . have := hh.injective heq
        simpa[π,-mem_Icc,ha'1,hb'1] using this
    rintro ⟨x',hx'⟩ 
    unfold htil h'
    simp[← Subtype.val_inj,-mem_Icc]
    obtain ⟨⟨a,ha⟩,ha'⟩ := hh.surjective ⟨x', mem_of_mem_erase hx'⟩ 
    push_cast at ha
    simp[← Subtype.val_inj] at ha'
    by_cases haj : a < j
    . use a; constructor; simp at ha ⊢; omega
      simp[haj,π,-mem_Icc,ha,← ha']
    use a-1
    suffices hanj : a ≠ j from by
      constructor
      . simp at ha ⊢
        omega
      push_neg at haj
      have : ¬  a - 1 < j := by
        simp[Int.le_sub_one_iff]
        apply lt_of_le_of_ne haj hanj.symm
      simp[this,π,-mem_Icc,ha,← ha']
    by_contra! han
    have hx'N := ne_of_mem_erase hx'
    rw[← Subtype.val_inj] at hj
    simp[← hj,← ha',han] at hx'N
  calc
    _ = ∑ i ∈ Icc (1:ℤ) n, if hi: i ∈ Icc (1:ℤ) n then ftil (gtil ⟨ i, hi ⟩ ) else 0 := by
      apply sum_congr rfl; grind
    _ = ∑ i ∈ Icc (1:ℤ) n, if hi: i ∈ Icc (1:ℤ) n then ftil (htil ⟨ i, hi ⟩ ) else 0 := by
      convert hn _ _ gtil htil why why2
      rw [Finset.card_erase_of_mem _, hX] <;> simp
    _ = _ := by apply sum_congr rfl; grind

/--
  This fact ensures that Definition 7.1.6 would be well-defined even if we did not appeal to the
  existing `Finset.sum` method.
-/
theorem exist_bijection {n:ℕ} {Y:Type*} (X: Finset Y) (hcard: X.card = n) :
    ∃ g: Icc (1:ℤ) n → X, Function.Bijective g := by
  have := Finset.equivOfCardEq (show (Icc (1:ℤ) n).card = X.card by simp [hcard])
  exact ⟨ this, this.bijective ⟩

/-- Definition 7.1.6 -/
theorem finite_series_eq {n:ℕ} {Y:Type*} (X: Finset Y) (f: Y → ℝ) (g: Icc (1:ℤ) n → X)
  (hg: Function.Bijective g) :
    ∑ i ∈ X, f i = ∑ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0) := by
  symm
  convert sum_bij (t:=X) (fun i hi ↦ g ⟨ i, hi ⟩ ) _ _ _ _
  . aesop
  . intro _ _ _ _ h; simpa [Subtype.val_inj, hg.injective.eq_iff] using h
  . intro b hb; have := hg.surjective ⟨ b, hb ⟩; grind
  intros; simp_all

/-- Proposition 7.1.11(a) / Exercise 7.1.2 -/
theorem finite_series_of_empty {X':Type*} (f: X' → ℝ) : ∑ i ∈ ∅, f i = 0 := by simp

/-- Proposition 7.1.11(b) / Exercise 7.1.2 -/
theorem finite_series_of_singleton {X':Type*} (f: X' → ℝ) (x₀:X') : ∑ i ∈ {x₀}, f i = f x₀ := by simp

/--
  A technical lemma relating a sum over a finset with a sum over a fintype. Combines well with
  tools such as `map_finite_series` below.
-/
theorem finite_series_of_fintype {X':Type*} (f: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, f x = ∑ x:X, f x.val := (sum_coe_sort X f).symm

/-- Proposition 7.1.11(c) / Exercise 7.1.2 -/
theorem map_finite_series {X Y:Type*} [Fintype X] [Fintype Y] (f: X → ℝ) {g:Y → X}
  (hg: Function.Bijective g) :
    ∑ x, f x = ∑ y, f (g y) := by
      set n := Fintype.card X with hn
      symm at hn
      choose hx hhx using exist_bijection Finset.univ hn
      have hyn : Fintype.card Y = Fintype.card X := Fintype.card_of_bijective hg
      rw[hn] at hyn
      rw[finite_series_eq Finset.univ f hx hhx]
      set f' := f ∘ g
      simp only [show ∀ y, f (g y) = f' y by exact fun y ↦ rfl]
      choose hy hhy using exist_bijection Finset.univ hyn
      rw[finite_series_eq Finset.univ f' hy hhy]
      unfold f' 
      set hxx :  Icc 1 (n:ℤ)  → Finset.univ (α := X) := fun i ↦ ⟨ g (hy i), by simp⟩ 
      have hhxx : Function.Bijective hxx := by
        constructor
        . intro i1 i2 heq
          simp[hxx] at heq
          replace heq := hg.injective heq
          rw[Subtype.coe_inj] at heq
          apply hhy.injective heq
        rintro ⟨x,hx⟩ 
        unfold hxx
        simp only [Subtype.eq_iff]
        choose hyav hhyav using hg.surjective x
        set hya : Finset.univ (α:=Y) := ⟨hyav, by simp⟩ 
        choose a ha using hhy.surjective hya
        use a;rw[ha]
        simpa[hya]
      exact finite_series_of_rearrange _ hn f hx hxx hhx hhxx


-- Proposition 7.1.11(d) is `rfl` in our formalism and is therefore omitted.

/-- Proposition 7.1.11(e) / Exercise 7.1.2 -/
theorem finite_series_of_disjoint_union {Z:Type*} {X Y: Finset Z} (hdisj: Disjoint X Y) (f: Z → ℝ) :
    ∑ z ∈ X ∪ Y, f z = ∑ z ∈ X, f z + ∑ z ∈ Y, f z := by
      set nx := #X with hnx
      set ny := #Y with hny
      choose gx hgx using exist_bijection X hnx.symm
      choose gy hgy using exist_bijection Y hny.symm
      have hiy (i:ℤ) (hi : i∈ Icc (1:ℤ) (ny + nx:ℕ)) (nhix : ¬ i ∈ Icc 1 (nx:ℤ)) : i - nx ∈ Icc (1:ℤ) ny := by
        simp at hi nhix ⊢
        omega
      set gz : {x // x ∈ Icc (1:ℤ) (ny + nx:ℕ) } → {x // x ∈ X ∪ Y} := fun ⟨i,hixy⟩  ↦ 
        if hix : i ∈ Icc 1 (nx:ℤ) then ⟨gx ⟨i,hix⟩, by simp ⟩ else ⟨gy ⟨i - nx, hiy i hixy hix⟩, by simp⟩ 
      have hcon (i) (j) : (gx i).val ≠ (gy j).val := by
        have gxx : (gx i).val ∈ X := by simp
        have gyy : (gy j).val ∈ Y := by simp
        by_contra! hcon
        rw[hcon] at gxx
        have hxy : (gy j).val ∈ X ∩ Y := by simpa
        have hxyn : (X ∩ Y).Nonempty := by use (gy j).val
        rw[← not_disjoint_iff_nonempty_inter] at hxyn
        contradiction
      have hgz : Function.Bijective gz := by
        constructor
        . intro i1 i2 heq
          simp[gz] at heq
          split_ifs at heq with hx1 hx2
          . simp[Subtype.coe_inj] at heq
            apply hgx.injective at heq
            simpa[Subtype.coe_inj] using heq
          . simp at heq
            contrapose! heq
            apply hcon
          . simp at heq
            contrapose! heq
            symm
            apply hcon
          . simp[Subtype.coe_inj] at heq
            apply hgy.injective at heq
            simpa[Subtype.coe_inj] using heq
        rintro ⟨z,hz⟩ 
        simp at hz
        obtain hix | hiy := hz 
        . obtain ⟨⟨a,hai⟩ ,ha⟩ :=   hgx.surjective ⟨z,hix⟩ 
          simp at hai
          use ⟨a, by simp;omega⟩
          simp[gz,hai]
          simpa[← Subtype.coe_inj] using ha
        obtain ⟨⟨a,hai⟩ ,ha⟩ :=   hgy.surjective ⟨z,hiy⟩ 
        simp at hai
        use ⟨a+nx,by simp;omega⟩ 
        have hc : ¬ a ≤ 0 := by omega
        simp[gz,hc]
        simpa[← Subtype.coe_inj] using ha
      rw[finite_series_eq X f gx hgx,
         finite_series_eq Y f gy hgy,
         finite_series_eq (X ∪ Y) f gz hgz
      ]
      push_cast
      set αx : ℤ → ℝ := fun i ↦ if hi : i ∈ Icc (1:ℤ) nx then  f (gx ⟨i,hi⟩) else 0 
      set αy : ℤ → ℝ := fun i ↦ if hi : i ∈ Icc (1:ℤ) ny then  f (gy ⟨i,hi⟩) else 0 
      rw[← concat_finite_series (m:=1) (n:=nx) (p:= ny + nx) (by simp) (by simp)]
      set αz : ℤ → ℝ := fun i ↦ if hi : i ∈ Icc (1:ℤ) (ny + nx) then  f (gz ⟨i,hi⟩) else 0 
      have hxz : (∑ i ∈ Icc (1:ℤ) nx, (αx i)) = ∑ i ∈ Icc (1:ℤ) nx, (αz i) := by
        apply sum_congr rfl
        intro x hx
        unfold αx αz
        have hx' : x ∈ Icc (1:ℤ) (ny + nx) := by
          apply Icc_subset_Icc_right ?_ hx
          linarith
        simp[-mem_Icc,hx,hx',gz]
      rw[hxz]
      congr 1
      rw[shift_finite_series (k:=nx) αy,add_comm (1:ℤ) nx]
      apply sum_congr rfl
      intro x hx
      simp at hx
      unfold αy αz
      have hx1 : 1 ≤ x := by omega
      have hxy : 1 ≤ x - nx := by omega
      have hxx : ¬ x ≤ nx := by omega
      simp[hx,hx1,hxy,gz,hxx]

/-- Proposition 7.1.11(f) / Exercise 7.1.2 -/
theorem finite_series_of_add {X':Type*} (f g: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, (f + g) x = ∑ x ∈ X, f x + ∑ x ∈ X, g x := by
      set nx := #X with hnx
      choose hx hhx using exist_bijection X hnx.symm
      rw[finite_series_eq X f hx hhx,
         finite_series_eq X g hx hhx,
         finite_series_eq X (f + g) hx hhx,
      ]
      rw[← finite_series_add]
      apply sum_congr rfl
      intro x hx
      simp[hx]

/-- Proposition 7.1.11(g) / Exercise 7.1.2 -/
theorem finite_series_of_const_mul {X':Type*} (f: X' → ℝ) (X: Finset X') (c:ℝ) :
    ∑ x ∈ X, c * f x = c * ∑ x ∈ X, f x := by
      set nx := #X with hnx
      choose hx hhx using exist_bijection X hnx.symm
      rw[finite_series_eq X f hx hhx]
      rw[← finite_series_const_mul]
      calc
       _ = ∑ x ∈ X, (c • f) x := by simp
       _ = _ := by
        rw[finite_series_eq X _ hx hhx]
        apply sum_congr rfl
        simp
        

/-- Proposition 7.1.11(h) / Exercise 7.1.2 -/
theorem finite_series_of_le' {X':Type*} (f g: X' → ℝ) (X: Finset X') (h: ∀ x ∈ X, f x ≤ g x) :
    ∑ x ∈ X, f x ≤ ∑ x ∈ X, g x := by
      set nx := #X with hnx
      choose hx hhx using exist_bijection X hnx.symm
      rw[finite_series_eq X f hx hhx,
         finite_series_eq X g hx hhx,
        ]
      apply finite_series_of_le
      intro i hi1 hix
      simp[hi1,hix]
      exact h (hx ⟨i,by simp;omega⟩) (by simp) 

/-- Proposition 7.1.11(i) / Exercise 7.1.2 -/
theorem abs_finite_series_le' {X':Type*} (f: X' → ℝ) (X: Finset X') :
    |∑ x ∈ X, f x| ≤ ∑ x ∈ X, |f x| := by 
      set nx := #X with hnx
      choose hx hhx using exist_bijection X hnx.symm
      set f' : X' → ℝ := fun x ↦ |f x|
      rw[finite_series_eq X f hx hhx,finite_series_eq X f' hx hhx]
      apply le_of_le_of_eq (abs_finite_series_le _)
      apply sum_congr rfl
      intro x hx
      split_ifs
      simp[f']

/-- Lemma 7.1.13 --/
theorem finite_series_of_finite_series {XX YY:Type*} (X: Finset XX) (Y: Finset YY)
  (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ z ∈ X.product Y, f z := by
  generalize h: X.card = n
  revert X; induction' n with n hn
  . simp
  intro X hX
  have hnon : X.Nonempty := by grind [card_ne_zero]
  choose x₀ hx₀ using hnon.exists_mem
  set X' := X.erase x₀
  have hcard : X'.card = n := by simp [X', card_erase_of_mem hx₀, hX]
  have hunion : X = X' ∪ {x₀} := by ext x; by_cases x = x₀ <;> grind
  have hdisj : Disjoint X' {x₀} := by simp [X']
  calc
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ x ∈ {x₀}, ∑ y ∈ Y, f (x, y) := by
      convert finite_series_of_disjoint_union hdisj _
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ y ∈ Y, f (x₀, y) := by
      rw [finite_series_of_singleton]
    _ = ∑ z ∈ X'.product Y, f z + ∑ y ∈ Y, f (x₀, y) := by rw [hn X' hcard]
    _ = ∑ z ∈ X'.product Y, f z + ∑ z ∈ .product {x₀} Y, f z := by
      congr 1
      rw [finite_series_of_fintype, finite_series_of_fintype f]
      set π : Finset.product {x₀} Y → Y :=
        fun z ↦ ⟨ z.val.2, by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; grind ⟩
      have hπ : Function.Bijective π := by
        constructor
        . intro ⟨ ⟨ x, y ⟩, hz ⟩ ⟨ ⟨ x', y' ⟩, hz' ⟩ hzz'; simp [π] at hz hz' hzz' ⊢; grind
        intro ⟨ y, hy ⟩; use ⟨ (x₀, y), by simp [hy] ⟩
      convert map_finite_series _ hπ with z
      obtain ⟨⟨x, y⟩, hz ⟩ := z
      simp at hz ⊢; grind
    _ = _ := by
      symm; convert finite_series_of_disjoint_union _ _
      . rw[hunion]
        calc
          _ = (X' ∪ {x₀}) ×ˢ Y := by rfl
          _ =  X' ×ˢ  Y ∪ {x₀} ×ˢ Y := by exact union_product
          _ = _ := by congr!
      suffices h:  Disjoint (X' ×ˢ  Y) ({x₀} ×ˢ Y) from by convert h
      rw[disjoint_product];tauto

/-- Corollary 7.1.14 (Fubini's theorem for finite series)-/
theorem finite_series_refl {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ z ∈ X.product Y, f z = ∑ z ∈ Y.product X, f (z.2, z.1) := by
  set h : Y.product X → X.product Y :=
    fun z ↦ ⟨ (z.val.2, z.val.1), by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; tauto ⟩
  have hh : Function.Bijective h := by
    constructor
    . intro ⟨ ⟨ _, _ ⟩, _ ⟩ ⟨ ⟨ _, _ ⟩, _ ⟩ _
      simp_all [h]
    intro ⟨ z, hz ⟩; simp at hz
    use ⟨ (z.2, z.1), by simp [hz] ⟩
  rw [finite_series_of_fintype]
  nth_rewrite 2 [finite_series_of_fintype]
  convert map_finite_series _ hh with z

theorem finite_series_comm {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ y ∈ Y, ∑ x ∈ X, f (x, y) := by
  rw [finite_series_of_finite_series, finite_series_refl,
      finite_series_of_finite_series _ _ (fun z ↦ f (z.2, z.1))]


-- Exercise 7.1.3 : develop as many analogues as you can of the above theory for finite products
-- instead of finite sums.
theorem prod_of_empty {n m:ℤ} (h: n < m) (a: ℤ → ℝ) : ∏ i ∈ Icc m n, a i = 1 := by
  rw [prod_eq_one]; intro _; rw [mem_Icc]; grind

theorem prod_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) :
    ∏ i ∈ Icc m (n+1), a i = (∏ i ∈ Icc m n, a i )* a (n+1) := by
  rw [mul_comm _ (a (n+1))]
  convert prod_insert _
  . ext; simp; omega
  . infer_instance
  simp


theorem prod_concat_finite_series {m n p:ℤ} (hmn: m ≤ n+1) (hpn : n ≤ p) (a: ℤ → ℝ) :
  (∏ i ∈ Icc m n, a i) * ∏ i ∈ Icc (n+1) p, a i = ∏ i ∈ Icc m p, a i := by
    replace hmn : m - 1 ≤ n := by omega
    induction' n, hmn using Int.le_induction with k hk hind
    . simp
    specialize hind (by omega)
    rw[prod_of_nonempty hk a,← hind,mul_assoc]
    congr;symm
    convert prod_insert _
    . ext;simp;omega
    . infer_instance
    simp

theorem prod_shift_finite_series {m n k:ℤ} (a: ℤ → ℝ) :
  ∏ i ∈ Icc m n, a i = ∏ i ∈ Icc (m+k) (n+k), a (i-k) := by
    by_cases hnm : n < m
    . observe hnm' : (n+k) < (m+k)
      rw[prod_of_empty hnm,prod_of_empty hnm']
    simp at hnm
    induction' n,hnm using Int.le_induction with n hn hind
    . simp
    rw[prod_of_nonempty (by omega),hind,mul_comm _ (a (n+1)),show a (n+1) = a (n + 1 + k - k) by simp]
    symm
    convert prod_insert _
    . ext;simp;omega
    . infer_instance
    simp
theorem prod_finite_series_mul {m n:ℤ} (a b: ℤ → ℝ) :
  ∏ i ∈ Icc m n, (a i * b i) = (∏ i ∈ Icc m n, a i) * ∏ i ∈ Icc m n, b i := by
    by_cases hnm : n < m
    . simp[prod_of_empty hnm]
    simp at hnm
    induction' n,hnm using Int.le_induction with n hn hind
    . simp
    have hnm' : n ≥ m-1 := by omega
    simp[prod_of_nonempty hnm', hind]
    ring

-- Note this one requires all a to be nonneg
theorem prod_finite_series_const_pow {m n:ℤ}  (a: ℤ → ℝ) (hpos : ∀ i, a i ≥ 0) (c:ℝ) :
  ∏ i ∈ Icc m n, (a i)^ c =  (∏ i ∈ Icc m n, a i) ^ c := by
    by_cases hnm : n < m
    . simp[prod_of_empty hnm]
    simp at hnm
    induction' n,hnm using Int.le_induction with n hn hind
    . simp
    have hnm' : n ≥ m-1 := by omega
    simp[prod_of_nonempty hnm', hind]
    rw[Real.mul_rpow (by apply prod_nonneg;simp[hpos]) (by simp[hpos])]

theorem prod_abs_finite_series_eq {m n:ℤ}   (a: ℤ → ℝ)  :
  |∏ i ∈ Icc m n, a i| = ∏ i ∈ Icc m n, |a i| := by
    by_cases hnm : n < m
    . simp[prod_of_empty hnm]
    simp at hnm
    induction' n,hnm using Int.le_induction with n hn hind
    . simp
    have hnm' : n ≥ m-1 := by omega
    simp_rw[prod_of_nonempty hnm',← hind]
    apply abs_mul
-- this requires nonneg as well
theorem prod_finite_series_of_le {m n:ℤ}  {a b: ℤ → ℝ}(hanonneg : ∀ i, a i ≥ 0) (hbnonneg : ∀ i, b i ≥ 0)(h: ∀ i, m ≤ i → i ≤ n → a i ≤ b i) :
  ∏ i ∈ Icc m n, a i ≤ ∏ i ∈ Icc m n, b i := by
    by_cases hnm : n < m
    . simp[prod_of_empty hnm]
    simp at hnm
    induction' n,hnm using Int.le_induction with n hn hind
    . simp[h m]
    specialize hind (by
      peel h with i hm h
      intro hn
      exact h (by omega)
    )
    have hnm' : n ≥ m-1 := by omega
    simp_rw[prod_of_nonempty hnm']
    specialize h (n+1) (by linarith) (by simp)
    apply mul_le_mul_of_nonneg hind h
    apply prod_nonneg; simp[hanonneg]
    simp[hbnonneg]

theorem prod_finite_series_of_rearrange {n:ℕ} {X':Type*} (X: Finset X') (hcard: X.card = n)
  (f: X' → ℝ) (g h: Icc (1:ℤ) n → X) (hg: Function.Bijective g) (hh: Function.Bijective h) :
    ∏ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0)
    = ∏ i ∈ Icc (1:ℤ) n, (if hi: i ∈ Icc (1:ℤ) n then f (h ⟨ i, hi ⟩) else 0) := by
  -- This proof is written to broadly follow the structure of the original text.
  revert X n; intro n
  induction' n with n hn
  . simp
  intro X hX g h hg hh
  -- A technical step: we extend g, h to the entire integers using a slightly artificial map π
  set π : ℤ → Icc (1:ℤ) (n+1) :=
    fun i ↦ if hi: i ∈ Icc (1:ℤ) (n+1) then ⟨ i, hi ⟩ else ⟨ 1, by simp ⟩
  have hπ (g : Icc (1:ℤ) (n+1) → X) :
      ∏ i ∈ Icc (1:ℤ) (n+1), (if hi:i ∈ Icc (1:ℤ) (n+1) then f (g ⟨ i, hi ⟩) else 0)
      = ∏ i ∈ Icc (1:ℤ) (n+1), f (g (π i)) := by
    apply prod_congr rfl _
    intro i hi; simp [hi, π, -mem_Icc]
  simp [-mem_Icc, hπ]
  rw [prod_of_nonempty (by omega) _]
  set x := g (π (n+1))
  have ⟨⟨j, hj'⟩, hj⟩ := hh.surjective x
  simp at hj'; obtain ⟨ hj1, hj2 ⟩ := hj'
  set h' : ℤ → X := fun i ↦ if (i:ℤ) < j then h (π i) else h (π (i+1))
  have : ∏ i ∈ Icc (1:ℤ) (n + 1), f (h (π i)) = (∏ i ∈ Icc (1:ℤ) n, f (h' i)) * f x := calc
    _ = (∏ i ∈ Icc (1:ℤ) j, f (h (π i))) * ∏ i ∈ Icc (j+1:ℤ) (n + 1), f (h (π i)) := by
      symm; apply prod_concat_finite_series <;> omega
    _ = (∏ i ∈ Icc (1:ℤ) (j-1), f (h (π i))) * f ( h (π j) )
        * ∏ i ∈ Icc (j+1:ℤ) (n + 1), f (h (π i)) := by
      congr; convert prod_of_nonempty _ _ <;> simp [hj1]
    _ = (∏ i ∈ Icc (1:ℤ) (j-1), f (h (π i))) * f x * ∏ i ∈ Icc (j:ℤ) n, f (h (π (i+1))) := by
      congr 1
      . simp [←hj, π,hj1, hj2]
      symm; convert prod_shift_finite_series _; simp
    _ = (∏ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) )* (∏ i ∈ Icc (j:ℤ) n, f (h (π (i+1)))) * f x := by ring
    _ = (∏ i ∈ Icc (1:ℤ) (j-1), f (h' i)) * (∏ i ∈ Icc (j:ℤ) n, f (h' i)) * f x := by
      congr 2
      all_goals apply prod_congr rfl _; intro i hi; simp [h'] at *
      . simp [show i < j by omega]
      simp [show ¬ i < j by omega]
    _ = _ := by congr; convert prod_concat_finite_series _ _ _ <;> linarith
  rw [this]
  congr 1
  have g_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : g (π i) ≠ x := by
    simp at hi
    simp [x, hg.injective.eq_iff, π, hi.1, show i ≤ n+1 by linarith]
    linarith
  have h'_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : h' i ≠ x := by
    simp at hi
    have hi' : 0 ≤ i := by linarith
    have hi'' : i ≤ n+1 := by linarith
    by_cases hlt: i < j <;> by_contra! heq
    all_goals simp [h', hlt, ←hj, hh.injective.eq_iff, ←Subtype.val_inj,
                    π, hi.1, hi.2, hi',hi''] at heq
    . linarith
    contrapose! hlt; linarith
  set gtil : Icc (1:ℤ) n → X.erase x :=
    fun i ↦ ⟨ (g (π i)).val, by simp [mem_erase, Subtype.val_inj, g_ne_x] ⟩
  set htil : Icc (1:ℤ) n → X.erase x :=
    fun i ↦ ⟨ (h' i).val, by simp [mem_erase, Subtype.val_inj, h'_ne_x] ⟩
  set ftil : X.erase x → ℝ := fun y ↦ f y.val
  have hπinj {i j:ℤ} (hi: i ∈ Icc (1:ℤ) (n+1)) (hj: j ∈ Icc (1:ℤ) (n+1)) (heq: π i = π j): i= j := by 
    simpa[π, -mem_Icc, hi,hj] using heq
  -- gtil is basically g, so simply use hg 
  have why : Function.Bijective gtil := by
    have hmap {x} {hx}: (gtil ⟨x,hx⟩).val = (g ( π x)).val := by
      simp[gtil]
    constructor
    . rintro ⟨a,ha⟩ ⟨b,hb⟩ heq  
      have ha' : a ∈ Icc (1:ℤ) (n+1) := by 
        apply mem_of_subset ?_ ha
        apply Icc_subset_Icc_right
        simp
      have hb' : b ∈ Icc (1:ℤ) (n+1) := by 
        apply mem_of_subset ?_ hb
        apply Icc_subset_Icc_right
        simp
      simp_rw[← Subtype.val_inj,hmap,Subtype.val_inj] at heq
      simp[← Subtype.val_inj]
      apply hπinj ha' hb'
      apply hg.injective heq
    rintro ⟨x',hx'E⟩ 
    obtain ⟨⟨a,ha⟩,ha'⟩ := hg.surjective ⟨x',mem_of_mem_erase hx'E⟩ 
    suffices han : a ∈ Icc (1:ℤ) n from by
      use ⟨a,han⟩ 
      push_cast at ha
      simp[← Subtype.val_inj] at ha'
      simp[← Subtype.val_inj,hmap,← ha']
      simp[π, -mem_Icc,Subtype.val_inj]
      simp[ha]
    simp at ⊢ ha
    suffices han : a ≠ n+1 from by 
      refine ⟨ha.1,?_⟩ 
      rw[Int.le_iff_lt_add_one]
      apply lt_of_le_of_ne ha.2 han
    by_contra! han
    have hx'N := ne_of_mem_erase hx'E
    simp[← Subtype.val_inj] at ha'
    simp[x,π,← han,ha,← ha'] at hx'N
  -- 
  have why2 : Function.Bijective htil := by
    constructor
    . rintro ⟨a,ha⟩  ⟨b,hb⟩  heq
      have ha' : a ∈ Icc (1:ℤ) (n+1) := by 
        simp at ha ⊢
        omega
      have hb' : b ∈ Icc (1:ℤ) (n+1) := by 
        simp at hb ⊢
        omega
      have ha'1 : (a+1) ∈ Icc (1:ℤ) (n+1) := by
        simp at ha ⊢ 
        omega
      have hb'1 : (b+1) ∈ Icc (1:ℤ) (n+1) := by 
        simp at hb ⊢
        omega
      simp[htil,Subtype.val_inj] at heq
      apply Subtype.eq;simp
      simp[h'] at heq;split_ifs at heq with haj hbj
      . have := hh.injective heq
        simpa[π,-mem_Icc,ha',hb'] using this
      . have := hh.injective heq
        simp[π,-mem_Icc,ha',hb'1] at this
        omega
      . have := hh.injective heq
        simp[π,-mem_Icc,ha'1,hb'] at this
        omega
      . have := hh.injective heq
        simpa[π,-mem_Icc,ha'1,hb'1] using this
    rintro ⟨x',hx'⟩ 
    unfold htil h'
    simp[← Subtype.val_inj,-mem_Icc]
    obtain ⟨⟨a,ha⟩,ha'⟩ := hh.surjective ⟨x', mem_of_mem_erase hx'⟩ 
    push_cast at ha
    simp[← Subtype.val_inj] at ha'
    by_cases haj : a < j
    . use a; constructor; simp at ha ⊢; omega
      simp[haj,π,-mem_Icc,ha,← ha']
    use a-1
    suffices hanj : a ≠ j from by
      constructor
      . simp at ha ⊢
        omega
      push_neg at haj
      have : ¬  a - 1 < j := by
        simp[Int.le_sub_one_iff]
        apply lt_of_le_of_ne haj hanj.symm
      simp[this,π,-mem_Icc,ha,← ha']
    by_contra! han
    have hx'N := ne_of_mem_erase hx'
    rw[← Subtype.val_inj] at hj
    simp[← hj,← ha',han] at hx'N
  calc
    _ = ∏ i ∈ Icc (1:ℤ) n, if hi: i ∈ Icc (1:ℤ) n then ftil (gtil ⟨ i, hi ⟩ ) else 0 := by
      apply prod_congr rfl; grind
    _ = ∏ i ∈ Icc (1:ℤ) n, if hi: i ∈ Icc (1:ℤ) n then ftil (htil ⟨ i, hi ⟩ ) else 0 := by
      convert hn _ _ gtil htil why why2
      rw [Finset.card_erase_of_mem _, hX] <;> simp
    _ = _ := by apply prod_congr rfl; grind

theorem prod_finite_series_eq {n:ℕ} {Y:Type*} (X: Finset Y) (f: Y → ℝ) (g: Icc (1:ℤ) n → X)
  (hg: Function.Bijective g) :
    ∏ i ∈ X, f i = ∏ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0) := by
  symm
  convert prod_bij (t:=X) (fun i hi ↦ g ⟨ i, hi ⟩ ) _ _ _ _
  . aesop
  . intro _ _ _ _ h; simpa [Subtype.val_inj, hg.injective.eq_iff] using h
  . intro b hb; have := hg.surjective ⟨ b, hb ⟩; grind
  intros; simp_all
theorem prod_finite_series_of_empty {X':Type*} (f: X' → ℝ) : ∏ i ∈ ∅, f i = 1 := by simp
theorem prod_finite_series_of_singleton {X':Type*} (f: X' → ℝ) (x₀:X') : ∏ i ∈ {x₀}, f i = f x₀ := by simp
theorem prod_finite_series_of_fintype {X':Type*} (f: X' → ℝ) (X: Finset X') :
    ∏ x ∈ X, f x = ∏ x:X, f x.val := (prod_coe_sort X f).symm

theorem prod_map_finite_series {X Y:Type*} [Fintype X] [Fintype Y] (f: X → ℝ) {g:Y → X}
  (hg: Function.Bijective g) :
    ∏ x, f x = ∏ y, f (g y) := by
      set n := Fintype.card X with hn
      symm at hn
      choose hx hhx using exist_bijection Finset.univ hn
      have hyn : Fintype.card Y = Fintype.card X := Fintype.card_of_bijective hg
      rw[hn] at hyn
      rw[prod_finite_series_eq Finset.univ f hx hhx]
      set f' := f ∘ g
      simp only [show ∀ y, f (g y) = f' y by exact fun y ↦ rfl]
      choose hy hhy using exist_bijection Finset.univ hyn
      rw[prod_finite_series_eq Finset.univ f' hy hhy]
      unfold f' 
      set hxx :  Icc 1 (n:ℤ)  → Finset.univ (α := X) := fun i ↦ ⟨ g (hy i), by simp⟩ 
      have hhxx : Function.Bijective hxx := by
        constructor
        . intro i1 i2 heq
          simp[hxx] at heq
          replace heq := hg.injective heq
          rw[Subtype.coe_inj] at heq
          apply hhy.injective heq
        rintro ⟨x,hx⟩ 
        unfold hxx
        simp only [Subtype.eq_iff]
        choose hyav hhyav using hg.surjective x
        set hya : Finset.univ (α:=Y) := ⟨hyav, by simp⟩ 
        choose a ha using hhy.surjective hya
        use a;rw[ha]
        simpa[hya]
      exact prod_finite_series_of_rearrange _ hn f hx hxx hhx hhxx

theorem prod_finite_series_of_disjoint_union {Z:Type*} {X Y: Finset Z} (hdisj: Disjoint X Y) (f: Z → ℝ) :
    ∏ z ∈ X ∪ Y, f z = (∏ z ∈ X, f z) * ∏ z ∈ Y, f z := by
      set nx := #X with hnx
      set ny := #Y with hny
      choose gx hgx using exist_bijection X hnx.symm
      choose gy hgy using exist_bijection Y hny.symm
      have hiy (i:ℤ) (hi : i∈ Icc (1:ℤ) (ny + nx:ℕ)) (nhix : ¬ i ∈ Icc 1 (nx:ℤ)) : i - nx ∈ Icc (1:ℤ) ny := by
        simp at hi nhix ⊢
        omega
      set gz : {x // x ∈ Icc (1:ℤ) (ny + nx:ℕ) } → {x // x ∈ X ∪ Y} := fun ⟨i,hixy⟩  ↦ 
        if hix : i ∈ Icc 1 (nx:ℤ) then ⟨gx ⟨i,hix⟩, by simp ⟩ else ⟨gy ⟨i - nx, hiy i hixy hix⟩, by simp⟩ 
      have hcon (i) (j) : (gx i).val ≠ (gy j).val := by
        have gxx : (gx i).val ∈ X := by simp
        have gyy : (gy j).val ∈ Y := by simp
        by_contra! hcon
        rw[hcon] at gxx
        have hxy : (gy j).val ∈ X ∩ Y := by simpa
        have hxyn : (X ∩ Y).Nonempty := by use (gy j).val
        rw[← not_disjoint_iff_nonempty_inter] at hxyn
        contradiction
      have hgz : Function.Bijective gz := by
        constructor
        . intro i1 i2 heq
          simp[gz] at heq
          split_ifs at heq with hx1 hx2
          . simp[Subtype.coe_inj] at heq
            apply hgx.injective at heq
            simpa[Subtype.coe_inj] using heq
          . simp at heq
            contrapose! heq
            apply hcon
          . simp at heq
            contrapose! heq
            symm
            apply hcon
          . simp[Subtype.coe_inj] at heq
            apply hgy.injective at heq
            simpa[Subtype.coe_inj] using heq
        rintro ⟨z,hz⟩ 
        simp at hz
        obtain hix | hiy := hz 
        . obtain ⟨⟨a,hai⟩ ,ha⟩ :=   hgx.surjective ⟨z,hix⟩ 
          simp at hai
          use ⟨a, by simp;omega⟩
          simp[gz,hai]
          simpa[← Subtype.coe_inj] using ha
        obtain ⟨⟨a,hai⟩ ,ha⟩ :=   hgy.surjective ⟨z,hiy⟩ 
        simp at hai
        use ⟨a+nx,by simp;omega⟩ 
        have hc : ¬ a ≤ 0 := by omega
        simp[gz,hc]
        simpa[← Subtype.coe_inj] using ha
      rw[prod_finite_series_eq X f gx hgx,
         prod_finite_series_eq Y f gy hgy,
         prod_finite_series_eq (X ∪ Y) f gz hgz
      ]
      push_cast
      set αx : ℤ → ℝ := fun i ↦ if hi : i ∈ Icc (1:ℤ) nx then  f (gx ⟨i,hi⟩) else 0 
      set αy : ℤ → ℝ := fun i ↦ if hi : i ∈ Icc (1:ℤ) ny then  f (gy ⟨i,hi⟩) else 0 
      rw[← prod_concat_finite_series (m:=1) (n:=nx) (p:= ny + nx) (by simp) (by simp)]
      set αz : ℤ → ℝ := fun i ↦ if hi : i ∈ Icc (1:ℤ) (ny + nx) then  f (gz ⟨i,hi⟩) else 0 
      have hxz : (∏ i ∈ Icc (1:ℤ) nx, (αx i)) = ∏ i ∈ Icc (1:ℤ) nx, (αz i) := by
        apply prod_congr rfl
        intro x hx
        unfold αx αz
        have hx' : x ∈ Icc (1:ℤ) (ny + nx) := by
          apply Icc_subset_Icc_right ?_ hx
          linarith
        simp[-mem_Icc,hx,hx',gz]
      rw[hxz]
      congr 1
      rw[prod_shift_finite_series (k:=nx) αy,add_comm (1:ℤ) nx]
      apply prod_congr rfl
      intro x hx
      simp at hx
      unfold αy αz
      have hx1 : 1 ≤ x := by omega
      have hxy : 1 ≤ x - nx := by omega
      have hxx : ¬ x ≤ nx := by omega
      simp[hx,hx1,hxy,gz,hxx]

/-- Proposition 7.1.11(f) / Exercise 7.1.2 -/
theorem prod_finite_series_of_add {X':Type*} (f g: X' → ℝ) (X: Finset X') :
    ∏ x ∈ X, (f * g) x = (∏ x ∈ X, f x) * ∏ x ∈ X, g x := by
      set nx := #X with hnx
      choose hx hhx using exist_bijection X hnx.symm
      rw[prod_finite_series_eq X f hx hhx,
         prod_finite_series_eq X g hx hhx,
         prod_finite_series_eq X (f * g) hx hhx,
      ]
      rw[← prod_finite_series_mul]
      apply prod_congr rfl
      intro x hx
      simp[hx]

/-- Proposition 7.1.11(g) / Exercise 7.1.2 -/
theorem prod_finite_series_of_const_pow {X':Type*} (f: X' → ℝ) (hnonneg: ∀ x, f x ≥ 0) (X: Finset X') (c:ℝ) :
    ∏ x ∈ X, (f x)^c = (∏ x ∈ X, f x)^c := by
      set nx := #X with hnx
      choose hx hhx using exist_bijection X hnx.symm
      rw[prod_finite_series_eq X f hx hhx]
      rw[← prod_finite_series_const_pow]
      set f' : X' → ℝ := fun x ↦ (f x) ^c
      rw[prod_finite_series_eq X _ hx hhx]
      apply prod_congr rfl
      . intro x hx
        simp[hx]
      intro i
      split_ifs
      . simp[hnonneg]
      simp
        

/-- Proposition 7.1.11(h) / Exercise 7.1.2 -/
theorem prod_finite_series_of_le' {X':Type*} (f g: X' → ℝ) (hfnonneg : ∀ x, f x ≥ 0) (X: Finset X') (h: ∀ x ∈ X, f x ≤ g x) :
    ∏ x ∈ X, f x ≤ ∏ x ∈ X, g x := by
      set nx := #X with hnx
      choose hx hhx using exist_bijection X hnx.symm
      rw[prod_finite_series_eq X f hx hhx,
         prod_finite_series_eq X g hx hhx,
        ]
      apply prod_finite_series_of_le
      . intro i
        split_ifs<;>grind
      . intro i
        split_ifs<;> grind
      intro i hi1 hix
      simp[hi1,hix]
      exact h (hx ⟨i,by simp;omega⟩) (by simp) 

/-- Proposition 7.1.11(i) / Exercise 7.1.2 -/
theorem prod_abs_finite_series_eq' {X':Type*} (f: X' → ℝ) (X: Finset X') :
    |∏ x ∈ X, f x| = ∏ x ∈ X, |f x| := by 
      set nx := #X with hnx
      choose hx hhx using exist_bijection X hnx.symm
      set f' : X' → ℝ := fun x ↦ |f x|
      rw[prod_finite_series_eq X f hx hhx,prod_finite_series_eq X f' hx hhx]
      rw[prod_abs_finite_series_eq]
      apply prod_congr rfl
      intro x hx
      split_ifs
      simp[f']

/-- Lemma 7.1.13 --/
theorem finite_series_of_finite_series {XX YY:Type*} (X: Finset XX) (Y: Finset YY)
  (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ z ∈ X.product Y, f z := by
  generalize h: X.card = n
  revert X; induction' n with n hn
  . simp
  intro X hX
  have hnon : X.Nonempty := by grind [card_ne_zero]
  choose x₀ hx₀ using hnon.exists_mem
  set X' := X.erase x₀
  have hcard : X'.card = n := by simp [X', card_erase_of_mem hx₀, hX]
  have hunion : X = X' ∪ {x₀} := by ext x; by_cases x = x₀ <;> grind
  have hdisj : Disjoint X' {x₀} := by simp [X']
  calc
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ x ∈ {x₀}, ∑ y ∈ Y, f (x, y) := by
      convert finite_series_of_disjoint_union hdisj _
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ y ∈ Y, f (x₀, y) := by
      rw [finite_series_of_singleton]
    _ = ∑ z ∈ X'.product Y, f z + ∑ y ∈ Y, f (x₀, y) := by rw [hn X' hcard]
    _ = ∑ z ∈ X'.product Y, f z + ∑ z ∈ .product {x₀} Y, f z := by
      congr 1
      rw [finite_series_of_fintype, finite_series_of_fintype f]
      set π : Finset.product {x₀} Y → Y :=
        fun z ↦ ⟨ z.val.2, by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; grind ⟩
      have hπ : Function.Bijective π := by
        constructor
        . intro ⟨ ⟨ x, y ⟩, hz ⟩ ⟨ ⟨ x', y' ⟩, hz' ⟩ hzz'; simp [π] at hz hz' hzz' ⊢; grind
        intro ⟨ y, hy ⟩; use ⟨ (x₀, y), by simp [hy] ⟩
      convert map_finite_series _ hπ with z
      obtain ⟨⟨x, y⟩, hz ⟩ := z
      simp at hz ⊢; grind
    _ = _ := by
      symm; convert finite_series_of_disjoint_union _ _
      . rw[hunion]
        calc
          _ = (X' ∪ {x₀}) ×ˢ Y := by rfl
          _ =  X' ×ˢ  Y ∪ {x₀} ×ˢ Y := by exact union_product
          _ = _ := by congr!
      suffices h:  Disjoint (X' ×ˢ  Y) ({x₀} ×ˢ Y) from by convert h
      rw[disjoint_product];tauto

/-- Corollary 7.1.14 (Fubini's theorem for finite series)-/
theorem finite_series_refl {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ z ∈ X.product Y, f z = ∑ z ∈ Y.product X, f (z.2, z.1) := by
  set h : Y.product X → X.product Y :=
    fun z ↦ ⟨ (z.val.2, z.val.1), by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; tauto ⟩
  have hh : Function.Bijective h := by
    constructor
    . intro ⟨ ⟨ _, _ ⟩, _ ⟩ ⟨ ⟨ _, _ ⟩, _ ⟩ _
      simp_all [h]
    intro ⟨ z, hz ⟩; simp at hz
    use ⟨ (z.2, z.1), by simp [hz] ⟩
  rw [finite_series_of_fintype]
  nth_rewrite 2 [finite_series_of_fintype]
  convert map_finite_series _ hh with z

theorem finite_series_comm {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ y ∈ Y, ∑ x ∈ X, f (x, y) := by
  rw [finite_series_of_finite_series, finite_series_refl,
      finite_series_of_finite_series _ _ (fun z ↦ f (z.2, z.1))]
#check Nat.factorial_zero
#check Nat.factorial_succ

/--
  Exercise 7.1.4. Note: there may be some technicalities passing back and forth between natural
  numbers and integers. Look into the tactics `zify`, `norm_cast`, and `omega`
-/
theorem binomial_theorem (x y:ℝ) (n:ℕ) :
    (x + y)^n
    = ∑ j ∈ Icc (0:ℤ) n,
    n.factorial / (j.toNat.factorial * (n-j).toNat.factorial) * x^j * y^(n - j) := by
  sorry

/-- Exercise 7.1.5 -/
theorem lim_of_finite_series {X:Type*} [Fintype X] (a: X → ℕ → ℝ) (L : X → ℝ)
  (h: ∀ x, Filter.atTop.Tendsto (a x) (nhds (L x))) :
    Filter.atTop.Tendsto (fun n ↦ ∑ x, a x n) (nhds (∑ x, L x)) := by
  sorry



end Finset
