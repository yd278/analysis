import Mathlib.Tactic
import Analysis.Section_6_5

/-!
# Analysis I, Section 6.6: Subsequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of a subsequence.
-/

namespace Chapter6

/-- Definition 6.6.1 -/
abbrev Sequence.subseq (a b: ℕ → ℝ) : Prop := ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, b n = a (f n)

/- Example 6.6.2 -/
example (a:ℕ → ℝ) : Sequence.subseq a (fun n ↦ a (2 * n)) := by
  use fun n ↦ 2 * n
  constructor
  . intro n m hn
    simp[hn]
  intro n
  simp

example {f: ℕ → ℕ} (hf: StrictMono f) : Function.Injective f := by
  intro n m hnm
  contrapose! hnm
  wlog h : n > m
  . replace h : m > n := by omega
    symm
    apply this hf hnm.symm h
  have := hf h
  omega

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ 1 + (10:ℝ)^(-(n:ℤ)-1)) := by
      use fun n ↦ (2*n)
      simp
      intro n m hn
      simp[hn]


example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ (10:ℝ)^(-(n:ℤ)-1)) := by
      use fun n ↦ (2*n+1)
      split_ands
      . intro n m hnm; simp[hnm]
      simp
      omega

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_self (a:ℕ → ℝ) : Sequence.subseq a a := by
  use fun n ↦ n
  simp
  intro n m hn
  simp[hn]

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_trans {a b c:ℕ → ℝ} (hab: Sequence.subseq a b) (hbc: Sequence.subseq b c) :
    Sequence.subseq a c := by
      choose f hf hfab using hab
      choose g hg hgbc using hbc
      use f ∘ g 
      split_ands
      . intro n m hnm
        simp; apply hf
        apply hg hnm
      . peel hgbc with n hgbc
        rw[hgbc]
        rw[hfab]
        simp
        

/-- Proposition 6.6.5 / Exercise 6.6.4 -/
theorem Sequence.convergent_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).TendsTo L ↔ ∀ b:ℕ → ℝ, Sequence.subseq a b → (b:Sequence).TendsTo L := by
      constructor
      . intro ha b hbab 
        peel ha with ε hε N hN ha
        simp at hN
        lift N to ℕ using hN
        choose f hf hfab using hbab
        intro n hn
        simp at hn
        lift n to ℕ using by linarith
        simp[hn,dist ]
        simp at hn
        have hNf : N ≤ f n := by
          apply le_trans hn
          apply StrictMono.le_apply hf
        specialize ha (f n) (by simp[hNf])
        simp[hNf,dist]at ha
        rwa[hfab]
      intro hn
      specialize hn a  (subseq_self a)
      assumption

/-- Proposition 6.6.6 / Exercise 6.6.5 -/
lemma Sequence.exist_close_subseq_index_of_limit_point {a:ℕ→ ℝ} {L:ℝ}(ha : (a:Sequence).LimitPoint L) (n pr : ℕ):
    ∃ (x:ℕ), x > pr ∧ dist (a x) L ≤ (1 / (n+1:ℝ)) := by
      specialize ha (1/(n+1:ℝ)) (by positivity) (pr + 1) (by simp; linarith)
      choose x hx hna using ha
      simp at hx
      simp[hx] at hna
      lift x to ℕ using hx.1
      use x; refine ⟨by omega, ?_⟩ 
      simpa using hna
noncomputable def Sequence.close_subsq_index{a:ℕ→ ℝ} {L:ℝ}(ha : (a:Sequence).LimitPoint L): ℕ → ℕ 
 | 0 => 0
 | k+1 => Nat.find (exist_close_subseq_index_of_limit_point ha k (close_subsq_index ha k))

lemma Sequence.close_subsq_index_strict_mono {a:ℕ→ ℝ} {L:ℝ}(ha : (a:Sequence).LimitPoint L):
    StrictMono (close_subsq_index (ha)) := by
      intro n m hnm
      induction' m,hnm using Nat.le_induction with k hk hind
      . simp[close_subsq_index]
        intro x hx hx'
        linarith
      apply lt_trans hind
      simp[close_subsq_index]
      intro x hx hx'
      linarith
lemma Sequence.close_subsq_index_spec {a:ℕ→ ℝ} {L:ℝ}(ha : (a:Sequence).LimitPoint L) (k:ℕ):
  dist (a (close_subsq_index ha (k + 1))) L ≤ (1/ (k+1:ℝ)) := by
    exact (Nat.find_spec (exist_close_subseq_index_of_limit_point ha k (close_subsq_index ha k))).2




theorem Sequence.limit_point_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).LimitPoint L ↔ ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).TendsTo L := by
      constructor
      . intro ha 
        set index := close_subsq_index ha
        use (fun n ↦ a (index n))
        split_ands
        . use index
          simp
          exact close_subsq_index_strict_mono ha
        intro ε hε
        choose N hN hNε  using Real.exists_nat_pos_inv_lt hε 
        use index N
        simp
        intro n hn 
        simp at hn
        lift n to ℕ using by linarith
        simp[hn]
        induction' n with k hind
        . simp at hn
          have := close_subsq_index_strict_mono ha
          specialize this hN
          simp[close_subsq_index] at this
          linarith
        apply le_trans (close_subsq_index_spec ha _)
        apply le_of_lt
        apply lt_of_le_of_lt ?_ hNε 
        simp
        rw[inv_le_inv₀ (by positivity) (by positivity)]
        norm_cast at hn
        norm_cast
        apply le_trans ?_ hn
        apply StrictMono.le_apply
        exact close_subsq_index_strict_mono ha

      rintro ⟨b,hab,hb⟩ 
      peel hb with ε hε hb
      choose fab hf hfab using hab
      intro N hN 
      simp at hN
      lift N to ℕ using hN
      choose Nb hNb hNbb using hb
      simp at hNb
      lift Nb to ℕ using hNb
      set Nt := max N Nb
      have hNtNb : Nt ≥ Nb := by simp[Nt]
      specialize hNbb Nt (by simp[Nt])
      simp[hNtNb] at hNbb
      specialize hfab Nt
      rw[hfab] at hNbb
      use fab Nt
      have hNf : N ≤ fab Nt := by 
        apply le_trans ?_ (StrictMono.le_apply hf)
        simp[Nt]
      simpa[hNf]


/-- Theorem 6.6.8 (Bolzano-Weierstrass theorem) -/
theorem Sequence.convergent_of_subseq_of_bounded {a:ℕ→ ℝ} (ha: (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).Convergent := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ _, _ ⟩ ⟩ := finite_limsup_liminf_of_bounded ha
  have := limit_point_of_limsup hL_plus
  rw [limit_point_iff_subseq] at this; peel 2 this; solve_by_elim

/- Exercise 6.6.2 -/

def Sequence.exist_subseq_of_subseq :
  Decidable (∃ a b : ℕ → ℝ, a ≠ b ∧ Sequence.subseq a b ∧ Sequence.subseq b a) := by
    -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
    apply isTrue
    use fun n ↦ (-1:ℝ) ^ n
    use fun n ↦ (-1:ℝ) ^ (n+1)
    set f := fun (n:ℕ) ↦  n+1
    have hf : StrictMono f := by
      intro n m hnm
      simp[f,hnm]
    split_ands
    . rw[Function.ne_iff]
      use 0;norm_num
    all_goals
      use f
      refine⟨hf, ?_⟩ 
      intro n
      simp[f]
    ring

/--
  Exercise 6.6.3.  You may find the API around Mathlib's `Nat.find` to be useful
  (and `open Classical` to avoid any decidability issues)
-/
theorem Sequence.subseq_of_unbounded {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence)⁻¹.TendsTo 0 := by
      set a' := (a)⁻¹ 
      have ha': (a':Sequence).LimitPoint 0 := by
        intro ε hε N hN
        have ha : ¬ (((a:Sequence).from N).IsBounded) := by exact unbounded_trans ha hN
        simp at ha
        specialize ha (1/ε) (by positivity)
        choose x hx using ha
        split_ifs at hx with hx0 _ 
        . use x; simp[hx0]
          lift x to ℕ using hx0.1
          simp at hx ⊢
          simp[a']
          rw[abs_inv,inv_le_comm₀ (by apply lt_trans ?_ hx; positivity) (by positivity)]
          apply le_of_lt hx
        all_goals
          simp at hx;linarith
      rw[limit_point_iff_subseq _ _] at ha'
      choose b' hab' hb' using ha'
      use (b')⁻¹ 
      split_ands
      . peel hab' with f hf n hfb
        simp[a'] at hfb
        simp
        rwa[inv_eq_iff_eq_inv]
      rw[inv_coe]
      simpa



end Chapter6
