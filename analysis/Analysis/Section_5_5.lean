import Mathlib.Tactic
import Analysis.Section_5_4
import Analysis.Section_4_4


/-!
# Analysis I, Section 5.5: The least upper bound property

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Upper bound and least upper bound on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.5.1 (upper bounds).  Here we use the `upperBounds` set defined in Mathlib. -/
theorem Real.upperBound_def (E: Set Real) (M: Real) : M ∈ upperBounds E ↔ ∀ x ∈ E, x ≤ M :=
  mem_upperBounds

theorem Real.lowerBound_def (E: Set Real) (M: Real) : M ∈ lowerBounds E ↔ ∀ x ∈ E, x ≥ M :=
  mem_lowerBounds

/-- API for Example 5.5.2 -/
theorem Real.Icc_def (x y:Real) : .Icc x y = { z | x ≤ z ∧ z ≤ y } := rfl

/-- API for Example 5.5.2 -/
theorem Real.mem_Icc (x y z:Real) : z ∈ Set.Icc x y ↔ x ≤ z ∧ z ≤ y := by simp [Real.Icc_def]

/-- Example 5.5.2 -/
example (M: Real) : M ∈ upperBounds (.Icc 0 1) ↔ M ≥ 1 := by
  rw[Real.upperBound_def,Real.Icc_def]
  simp;
  constructor
  . intro a
    specialize a 1; simpa using a
  intro h x hxl hx1
  grind
/-- API for Example 5.5.3 -/
theorem Real.Ioi_def (x:Real) : .Ioi x = { z | z > x } := rfl

/-- Example 5.5.3 -/
example : ¬ ∃ M, M ∈ upperBounds (.Ioi (0:Real)) := by
  simp
  intro x
  by_contra! h
  rw[Real.upperBound_def,Real.Ioi_def] at h
  by_cases hx : x > 0
  . 
    specialize h (x + 1) (by simp;grind)
    linarith
  simp at hx
  specialize h 1 (by simp)
  linarith

/-- Example 5.5.4 -/
example : ∀ M, M ∈ upperBounds (∅ : Set Real) := by
  intro M
  rw[Real.upperBound_def]
  simp

theorem Real.upperBound_upper {M M': Real} (h: M ≤ M') {E: Set Real} (hb: M ∈ upperBounds E) :
    M' ∈ upperBounds E := by
      rw[upperBound_def] at hb ⊢ 
      peel hb with x hx hb
      grind


/-- Definition 5.5.5 (least upper bound).  Here we use the `isLUB` predicate defined in Mathlib. -/
theorem Real.isLUB_def (E: Set Real) (M: Real) :
    IsLUB E M ↔ M ∈ upperBounds E ∧ ∀ M' ∈ upperBounds E, M' ≥ M := by rfl

theorem Real.isGLB_def (E: Set Real) (M: Real) :
    IsGLB E M ↔ M ∈ lowerBounds E ∧ ∀ M' ∈ lowerBounds E, M' ≤ M := by rfl

/-- Example 5.5.6 -/
example : IsLUB (.Icc (0:Real) 1) 1 := by
  rw[Real.isLUB_def]
  split_ands
  . rw[Real.upperBound_def]
    intro x hx; simp at hx
    grind
  intro M hM
  rw[Real.upperBound_def,Real.Icc_def] at hM
  specialize hM 1 (by simp)
  assumption

/-- Example 5.5.7 -/
example : ¬∃ M, IsLUB (∅: Set Real) M := by
  simp

/-- Proposition 5.5.8 (Uniqueness of least upper bound)-/
theorem Real.LUB_unique {E: Set Real} {M M': Real} (h1: IsLUB E M) (h2: IsLUB E M') : M = M' := by grind [Real.isLUB_def]

/-- definition of "bounded above", using Mathlib notation -/
theorem Real.bddAbove_def (E: Set Real) : BddAbove E ↔ ∃ M, M ∈ upperBounds E := Set.nonempty_def

theorem Real.bddBelow_def (E: Set Real) : BddBelow E ↔ ∃ M, M ∈ lowerBounds E := Set.nonempty_def

/-- Exercise 5.5.2 -/
theorem Int.decreasing_induction' {n m:ℤ} {P: ℤ → Prop} (hmn: n > m) (hind: ∀ k, m < k → k ≤ n→ P k → P (k-1)) (hpn : P n):
    P m := by
      set P' : ℕ → Prop := fun x ↦ P (x + m)
      set up := (n - m).toNat ;
      have hup : up > 0 := by simpa[up]
      have hind' : (k': ℕ) →  k' < up → 0≤ k' → P' (k'+1) → P' k' := by
        intro k hk _ hpk
        simp[P'] at hpk ⊢
        specialize hind (k+1+m) (by simp) (by simp[up] at hk;grind) hpk
        abel_nf at hind
        assumption
      have hpn : P' up := by 
        simp[P',up]
        have: max (n-m) 0 = n - m := by simp;grind
        rw[this];ring_nf
        assumption
      suffices h : P' 0 from by
        simpa[P'] using h
      apply Nat.decreasingInduction' 
      exact hind'
      simp
      exact hpn

theorem Real.upperBound_between {E: Set Real} {n:ℕ} {L K:ℤ} (hLK: L < K)
  (hK: K*((1/(n+1):ℚ):Real) ∈ upperBounds E) (hL: L*((1/(n+1):ℚ):Real) ∉ upperBounds E) :
    ∃ m, L < m
    ∧ m ≤ K
    ∧ m*((1/(n+1):ℚ):Real) ∈ upperBounds E
    ∧ (m-1)*((1/(n+1):ℚ):Real) ∉ upperBounds E := by
      by_contra! hind
      have (m:ℤ) : m - (1 : Real) = (m - 1:ℤ ) := by simp
      set P : ℤ → Prop := fun z ↦ 
        (z:Real) * ((1/(n+1):ℚ):Real) ∈ upperBounds  E
      replace hind : ∀ (m:ℤ), L < m → m ≤ K → P m → P (m-1) := by
        peel hind with m hlm hmk hind
        intro hpm
        simp only [P] at hpm
        specialize hind hpm
        specialize this m
        simp only [P]
        rw[this] at hind
        assumption
      have hpk : P K := by
        simp only[P]; assumption
      have hpl : P L := by
        apply Int.decreasing_induction' hLK hind hpk
      simp only[P] at hpl
      contradiction

/-- Exercise 5.5.3 -/
theorem Real.upperBound_discrete_unique {E: Set Real} {n:ℕ} {m m':ℤ}
  (hm1: (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm2: (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E)
  (hm'1: (((m':ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm'2: (((m':ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E) :
    m = m' := by
      by_contra! hne
      wlog hlt: m' < m
      . 
        replace hlt: m < m' := by grind
        specialize this hm'1 hm'2 hm1 hm2 hne.symm hlt
        exact this
      replace hlt : m' ≤ m - 1 := by grind
      set u := (((m:ℚ) / (n+1):ℚ):Real)
      set nu' := (((m':ℚ) / (n+1):ℚ):Real)
      set nu := (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real)
      suffices h : nu' ≤ nu from by
        rw[upperBound_def] at hm'1 hm2
        push_neg at hm2
        choose x hxE hnux using hm2
        specialize hm'1 x hxE
        linarith
      have : nu = (((m-1:ℚ) / (n+1):ℚ ):Real) := by
        simp only[nu]
        rw[ratCast_inj]
        field_simp
      simp only[nu',this]
      rw[le_iff_lt_or_eq,← lt_of_coe, ratCast_inj]
      rw[← le_iff_lt_or_eq]
      have : 0 < ((n:ℚ) + 1)  := by positivity
      rw[ (div_le_div_iff_of_pos_right this)]
      norm_cast

/-- Lemmas that can be helpful for proving 5.5.4 -/
theorem Sequence.IsCauchy.abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy):
  ((|a| : ℕ → ℚ) : Sequence).IsCauchy := by
    peel ha with ε hε N hN n hn m hm ha
    simp at hN
    lift N to ℕ using hN
    simp at hn hm
    lift n to ℕ using by grind
    lift m to ℕ using by grind
    simp at hn hm
    simp[hn,hm,Rat.Close] at ha ⊢ 
    have :|(|a n| - |a m|)| ≤ |a n - a m| := by
      exact abs_abs_sub_abs_le (a n) (a m)
    grind

theorem Real.LIM.abs_eq {a b:ℕ → ℚ} (ha: (a: Sequence).IsCauchy)
    (hb: (b: Sequence).IsCauchy) (h: LIM a = LIM b): LIM |a| = LIM |b| := by
      have haabs := Sequence.IsCauchy.abs ha
      have hbabs := Sequence.IsCauchy.abs hb
      rw[LIM_eq_LIM haabs hbabs]
      rw[LIM_eq_LIM ha hb] at h
      peel h with ε hε N n hna hnb h
      simp at hna hnb
      lift n to ℕ using hna.1
      simp[hna,Rat.Close] at h ⊢
      have := abs_abs_sub_abs_le (a n) (b n)
      grind


theorem Real.LIM.abs_eq_pos {a: ℕ → ℚ} (h: LIM a > 0) (ha: (a:Sequence).IsCauchy):
    LIM a = LIM |a| := by
      rw[← isPos_iff, isPos_def] at h
      obtain ⟨ a',hbon ,ha' ,hrfl ⟩:= h
      have haabs := Sequence.IsCauchy.abs ha
      rw[LIM_eq_LIM ha haabs]
      intro ε hε 
      rw[Rat.eventuallyClose_def]

      suffices h : ∃ N, ∀ n ≥ N, (a:Sequence).seq n ≥ 0 from by
        peel h with N n h
        intro hn; simp at hn
        lift n to ℕ using hn.1
        simp[hn] at h ⊢ 
        simp[Rat.Close]
        rw[_root_.abs_of_nonneg h]
        simp;grind

      rw[LIM_eq_LIM ha ha'] at hrfl
      choose b hb hqb using hbon
      specialize hrfl (b/2) (by positivity)
      choose N hN using hrfl
      use N; intro n hn
      specialize hN n
      simp[hn] at hN
      by_cases hnn : 0 ≤ n <;> simp[hnn] at hN
      . 
        lift n to ℕ using hnn
        simp[Rat.Close,abs_le] at hN
        simp
        specialize hqb n
        linarith
      simp[hnn]

theorem Real.LIM_abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy): |LIM a| = LIM |a| := by
  have haabs := Sequence.IsCauchy.abs ha
  obtain (h1|h2|h3) := trichotomous (LIM a)
  . 
    simp[h1]
    rw[← LIM.zero] at h1 ⊢ 
    rw[LIM_eq_LIM (by apply Sequence.IsCauchy.const) haabs]
    rw[LIM_eq_LIM ha (by apply Sequence.IsCauchy.const)] at h1
    peel h1 with ε hε N n hn hec
    simp at hn
    lift n to ℕ using hn.1
    simp[hn,Rat.Close] at hec ⊢ 
    assumption
  .
    rw[isPos_iff] at h2
    rw[_root_.abs_of_pos h2]
    exact LIM.abs_eq_pos h2 ha
  . 
    set a' := -a
    have hLIMLIM: LIM a' = - LIM a := by simp[a']; exact Eq.symm (neg_LIM a ha)
    have hpos : (LIM a') > 0 := by 
      simp[a']
      rw[hLIMLIM]
      have := (neg_iff_pos_of_neg (LIM a)).mp h3
      exact (isPos_iff (-LIM a)).mp this
    have hcau' : (a':Sequence).IsCauchy := by  simp[a'] ; apply Sequence.IsCauchy.neg ha
    replace h3 : LIM a < 0 := by exact (isNeg_iff (LIM a)).mp h3
    have := LIM.abs_eq_pos hpos hcau'
    rw[_root_.abs_of_neg h3]
    have haa : |a| = |a'| := by simp[a']
    rw[haa,← this]
    symm
    assumption

    

theorem Real.LIM_of_le' {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy)
    (h: ∃ N, ∀ n ≥ N, a n ≤ x) : LIM a ≤ x := by
      by_contra! hcon
      -- find a rat between x and a
      choose q hlower hupper using rat_between hcon
      choose N h using h
      have hanq : ∀n ≥ N, a n < q:= by
        peel h with n hn h
        rw[lt_of_coe]
        grind
      rw[ratCast_def,
        lt_iff,
        LIM_sub (by apply Sequence.IsCauchy.const) hcauchy,
        isNeg_def
      ] at hupper
      -- so the difference need to be neg (which is not)
      set d := (fun x ↦ q) - a
      have hd : (d:Sequence).IsCauchy := by 
        simp[d]
        apply Sequence.IsCauchy.sub
        apply Sequence.IsCauchy.const
        exact hcauchy
      choose a' hbon ha' heq using hupper
      choose b hb hbon using hbon
      rw[LIM_eq_LIM hd ha'] at heq
      specialize heq (b/2) (by positivity)
      choose N' hclose using heq
      set n := (max (N:ℤ) N').toNat 
      have hnN' : N' ≤ n := by grind
      specialize hanq n (by simp[n])
      specialize hbon n
      specialize hclose n (by
        simp[hnN']
      ) (by simp[hnN'])
      simp[hnN',Rat.Close] at hclose
      have hdn : d n ≤  a' n + b/2 := by
        rw[abs_le] at hclose
        grind
      have ha'npb : a' n + b / 2 < 0 := by 
        calc 
          _ ≤ - b + b/2 := by grind
          _ < 0 := by simp[hb]
      replace hdn : d n < 0 := by grind
      simp only [d] at hdn
      rw[show ((fun x ↦ q) - a) = fun n ↦ q - a n by rfl] at hdn
      simp at hdn
      linarith

/-- Exercise 5.5.4 -/
theorem Real.LIM_of_Cauchy {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
    (q:Sequence).IsCauchy ∧ ∀ M, |q M - LIM q| ≤ 1 / (M+1) := by
      have : (q:Sequence).IsCauchy  := by
        intro ε hε 
        rw[Rat.eventuallySteady_def]
        set M := Nat.ceil (ε⁻¹)
        use M; simp
        intro n hn m hm
        lift n to ℕ using by grind
        lift m to ℕ using by grind
        simp at hn hm
        simp[hn,hm,Rat.Close]
        specialize hq M n hn m hm
        suffices h: (1:ℚ) / (M + 1:ℚ) ≤ ε from by
          grind
        simp[M]
        calc
          _ ≤ (ε⁻¹ + 1)⁻¹ := by rw[inv_le_inv₀ (by positivity) (by positivity)]
                                gcongr
                                exact Nat.le_ceil ε⁻¹
          _ ≤ (ε⁻¹)⁻¹ := by gcongr;grind
          _ = _ := by simp
      split_ands; exact this
      intro M
      have hsteady : ((1:ℚ)/ ( M+1 :ℚ)).Steady ((q:Sequence).from M) := by
        intro n hn m hm
        lift n to ℕ using by grind
        lift m to ℕ using by grind
        simp at hn hm
        simp[hn,hm,Rat.Close] 
        specialize hq M  n hn m hm
        simpa using hq
      obtain⟨hupper,hlower⟩  := Sequence.LIM_within_steady this hsteady (by positivity)
      have : (((1:ℚ) / (M + 1):ℚ ):Real) = (1:Real) / (M+1:Real) := by simp
      rw[this] at hupper hlower
      rw[abs_le]
      grind

/--
The sequence m₁, m₂, … is well-defined.
This proof uses a different indexing convention than the text
-/
lemma Real.LUB_claim1 (n : ℕ) {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E)
:  ∃! m:ℤ,
      (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E
      ∧ ¬ (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∈ upperBounds E := by
  set x₀ := Set.Nonempty.some hE
  observe hx₀ : x₀ ∈ E
  set ε := ((1/(n+1):ℚ):Real)
  have hpos : ε.IsPos := by simp [isPos_iff, ε]; positivity
  apply existsUnique_of_exists_of_unique
  . rw [bddAbove_def] at hbound; obtain ⟨ M, hbound ⟩ := hbound
    choose K _ hK using le_mul hpos M
    choose L' _ hL using le_mul hpos (-x₀)
    set L := -(L':ℤ)
    have claim1_1 : L * ε < x₀ := by simp [L]; linarith
    have claim1_2 : L * ε ∉ upperBounds E := by grind [upperBound_def]
    have claim1_3 : (K:Real) > (L:Real) := by
      contrapose! claim1_2
      replace claim1_2 := mul_le_mul_left claim1_2 hpos
      simp_rw [mul_comm] at claim1_2
      replace claim1_2 : M ≤ L * ε := by order
      grind [upperBound_upper]
    have claim1_4 : ∃ m:ℤ, L < m ∧ m ≤ K ∧ m*ε ∈ upperBounds E ∧ (m-1)*ε ∉ upperBounds E := by
      convert Real.upperBound_between (n := n) _ _ claim1_2
      . qify; rwa [←gt_iff_lt, gt_of_coe]
      simp [ε] at *; apply upperBound_upper _ hbound; order
    choose m _ _ hm hm' using claim1_4; use m
    have : (m/(n+1):ℚ) = m*ε := by simp [ε]; field_simp
    exact ⟨ by convert hm, by convert hm'; simp [this, sub_mul, ε] ⟩
  grind [upperBound_discrete_unique]

lemma Real.LUB_claim2 {E : Set Real} (N:ℕ) {a b: ℕ → ℚ}
  (hb : ∀ n, b n = 1 / (↑n + 1))
  (hm1 : ∀ (n : ℕ), ↑(a n) ∈ upperBounds E)
  (hm2 : ∀ (n : ℕ), ↑((a - b) n) ∉ upperBounds E)
: ∀ n ≥ N, ∀ n' ≥ N, |a n - a n'| ≤ 1 / (N+1) := by
    intro n hn n' hn'
    rw [abs_le]
    split_ands
    . specialize hm1 n; specialize hm2 n'
      have bound1 : ((a-b) n') < a n := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
      have bound3 : 1/((n':ℚ)+1) ≤ 1/(N+1) := by gcongr
      rw [←neg_le_neg_iff] at bound3; rw [Pi.sub_apply] at bound1; grind
    specialize hm1 n'; specialize hm2 n
    have bound1 : ((a-b) n) < a n' := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
    have bound2 : ((a-b) n) = a n - 1 / (n+1) := by simp [hb n]
    have bound3 : 1/((n+1):ℚ) ≤ 1/(N+1) := by gcongr
    linarith

/-- Theorem 5.5.9 (Existence of least upper bound)-/
theorem Real.LUB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E): ∃ S, IsLUB E S := by
  -- This proof is written to follow the structure of the original text.
  set x₀ := hE.some
  have hx₀ : x₀ ∈ E := hE.some_mem
  set m : ℕ → ℤ := fun n ↦ (LUB_claim1 n hE hbound).exists.choose
  set a : ℕ → ℚ := fun n ↦ (m n:ℚ) / (n+1)
  set b : ℕ → ℚ := fun n ↦ 1 / (n+1)
  have claim1 (n: ℕ) := LUB_claim1 n hE hbound
  have hb : (b:Sequence).IsCauchy := .harmonic'
  have hm1 (n:ℕ) := (claim1 n).exists.choose_spec.1
  have hm2 (n:ℕ) : ¬((a - b) n: Real) ∈ upperBounds E := (claim1 n).exists.choose_spec.2
  have claim2 (N:ℕ) := LUB_claim2 N (by aesop) hm1 hm2
  have claim3 : (a:Sequence).IsCauchy := (LIM_of_Cauchy claim2).1
  set S := LIM a; use S
  have claim4 : S = LIM (a - b) := by
    have : LIM b = 0 := LIM.harmonic
    simp [←LIM_sub claim3 hb, S, this]
  rw [isLUB_def, upperBound_def]
  split_ands
  . intros; apply LIM_of_ge claim3; grind [upperBound_def]
  intro y hy
  have claim5 (n:ℕ) : y ≥ (a-b) n := by contrapose! hm2; use n; apply upperBound_upper _ hy; order
  rw [claim4]; apply LIM_of_le _ claim5; solve_by_elim [Sequence.IsCauchy.sub]

/-- A bare-bones extended real class to define supremum. -/
inductive ExtendedReal where
| neg_infty : ExtendedReal
| real (x:Real) : ExtendedReal
| infty : ExtendedReal

/-- Mathlib prefers ⊤ to denote the +∞ element. -/
instance ExtendedReal.inst_Top : Top ExtendedReal where
  top := infty

/-- Mathlib prefers ⊥ to denote the -∞ element.-/
instance ExtendedReal.inst_Bot: Bot ExtendedReal where
  bot := neg_infty

instance ExtendedReal.coe_real : Coe Real ExtendedReal where
  coe x := ExtendedReal.real x

instance ExtendedReal.real_coe : Coe ExtendedReal Real where
  coe X := match X with
  | neg_infty => 0
  | real x => x
  | infty => 0

abbrev ExtendedReal.IsFinite (X : ExtendedReal) : Prop := match X with
  | neg_infty => False
  | real _ => True
  | infty => False

theorem ExtendedReal.finite_eq_coe {X: ExtendedReal} (hX: X.IsFinite) :
    X = ((X:Real):ExtendedReal) := by
  cases X <;> try simp [IsFinite] at hX
  simp

open Classical in
/-- Definition 5.5.10 (Supremum)-/
noncomputable abbrev ExtendedReal.sup (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddAbove E then ((Real.LUB_exist h1 h2).choose:Real) else ⊤) else ⊥

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_empty : sup ∅ = ⊥ := by simp [sup]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_unbounded {E: Set Real} (hb: ¬ BddAbove E) : sup E = ⊤ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [sup, hE, hb]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sup E) := by
  simp [hnon, hb, sup]; exact (Real.LUB_exist hnon hb).choose_spec

theorem ExtendedReal.sup_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    (sup E).IsFinite := by simp [sup, hnon, hb, IsFinite]

/-- Proposition 5.5.12 -/
theorem Real.exist_sqrt_two : ∃ x:Real, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  set E := { y:Real | y ≥ 0 ∧ y^2 < 2 }
  have claim1: 2 ∈ upperBounds E := by
    rw [upperBound_def]
    intro y hy; simp [E] at hy; contrapose! hy
    intro hpos
    calc
      _ ≤ 2 * 2 := by norm_num
      _ ≤ y * y := by gcongr
      _ = y^2 := by ring
  have claim1' : BddAbove E := by rw [bddAbove_def]; use 2
  have claim2: 1 ∈ E := by simp [E]
  observe claim2': E.Nonempty
  set x := ((ExtendedReal.sup E):Real)
  have claim3 : IsLUB E x := by grind [ExtendedReal.sup_of_bounded]
  have claim4 : x ≥ 1 := by grind [isLUB_def, upperBound_def]
  have claim5 : x ≤ 2 := by grind [isLUB_def]
  have claim6 : x.IsPos := by rw [isPos_iff]; linarith
  use x; obtain h | h | h := trichotomous' (x^2) 2
  . have claim11: ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 - 4*ε > 2 := by
      set ε := min (1/2) ((x^2-2)/8)
      have hx : x^2 - 2 > 0 := by linarith
      have hε : 0 < ε := by positivity
      observe hε1: ε ≤ 1/2
      observe hε2: ε ≤ (x^2-2)/8
      refine' ⟨ ε, hε, _, _ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim11
    have claim12: (x-ε)^2 > 2 := calc
      _ = x^2 - 2 * ε * x + ε * ε := by ring
      _ ≥ x^2 - 2 * ε * 2 + 0 * 0 := by gcongr
      _ = x^2 - 4 * ε := by ring
      _ > 2 := hε3
    have why (y:Real) (hy: y ∈ E) : x - ε ≥ y := by
      simp[E] at hy
      obtain ⟨hy1, hy2⟩ := hy 
      have hdif: 0 ≤ (x - ε) := by grind
      have : (x - ε)^2 ≥  y^2 := by linarith
      simp at ⊢ this
      rwa[sq_le_sq₀ hy1 hdif] at this
    have claim13: x-ε ∈ upperBounds E := by rwa [upperBound_def]
    have claim14: x ≤ x-ε := by grind [isLUB_def]
    linarith
  . have claim7 : ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 + 5*ε < 2 := by
      set ε := min (1/2) ((2-x^2)/10)
      have hx : 2 - x^2 > 0 := by linarith
      have hε: 0 < ε := by positivity
      have hε1: ε ≤ 1/2 := min_le_left _ _
      have hε2: ε ≤ (2 - x^2)/10 := min_le_right _ _
      refine ⟨ ε, hε, ?_, ?_ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim7
    have claim8 : (x+ε)^2 < 2 := calc
      _ = x^2 + (2*x)*ε + ε*ε := by ring
      _ ≤ x^2 + (2*2)*ε + 1*ε := by gcongr
      _ = x^2 + 5*ε := by ring
      _ < 2 := hε3
    have claim9 : x + ε ∈ E := by simp [E, claim8]; linarith
    have claim10 : x + ε ≤ x := by grind [isLUB_def, upperBound_def]
    linarith
  assumption

/-- Remark 5.5.13 -/
theorem Real.exist_irrational : ∃ x:Real, ¬ ∃ q:ℚ, x = (q:Real) := by
  obtain ⟨sqr2, hsqr2⟩ := exist_sqrt_two 
  use sqr2
  by_contra!
  choose q hq using this
  rw[hq] at hsqr2
  have := Rat.not_exist_sqrt_two
  simp at this
  specialize this q
  norm_cast at hsqr2

/-- Helper lemma for Exercise 5.5.1. -/
theorem Real.mem_neg (E: Set Real) (x:Real) : x ∈ -E ↔ -x ∈ E := Set.mem_neg

/-- Exercise 5.5.1-/
theorem Real.inf_neg {E: Set Real} {M:Real} (h: IsLUB E M) : IsGLB (-E) (-M) := by
  simpa


theorem Real.GLB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddBelow E): ∃ S, IsGLB E S := by
  set E' := -E;
  have hE' : E'.Nonempty := by simp[E',hE]
  have hbound' : BddAbove E' := by simp[E',hbound]
  obtain ⟨S,hS⟩  := LUB_exist hE' hbound'
  simp[E'] at hS
  use -S

open Classical in
noncomputable abbrev ExtendedReal.inf (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddBelow E then ((Real.GLB_exist h1 h2).choose:Real) else ⊥) else ⊤

theorem ExtendedReal.inf_of_empty : inf ∅ = ⊤ := by simp [inf]

theorem ExtendedReal.inf_of_unbounded {E: Set Real} (hb: ¬ BddBelow E) : inf E = ⊥ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [inf, hE, hb]

theorem ExtendedReal.inf_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    IsGLB E (inf E) := by simp [hnon, hb, inf]; exact (Real.GLB_exist hnon hb).choose_spec

theorem ExtendedReal.inf_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    (inf E).IsFinite := by simp [inf, hnon, hb, IsFinite]

/-- Exercise 5.5.5 -/
abbrev Real.irrational (x:Real) : Prop := ¬∃ (q:ℚ), x = q
abbrev Real.rational (x:Real) : Prop := ∃ (q:ℚ), x = q
lemma Real.exist_pos_irrational : ∃ x : Real, x.IsPos ∧ x.irrational := by
  choose ir hir using exist_irrational
  push_neg at hir
  by_cases hirpos : ir > 0
  . 
    use ir; simp[isPos_iff,hirpos]
    intro x; specialize hir x; exact hir
  replace hirpos : ir < 0 := by
    simp at hirpos;rw[le_iff_lt_or_eq] at hirpos
    have : ir ≠ 0 := by
      by_contra hez
      specialize hir 0
      simp at hir; contradiction
    simpa[this] using hirpos
  use (-ir)
  simp[isPos_iff,hirpos]
  intro x;specialize hir (-x)
  rw[neg_eq_iff_eq_neg,neg_ratCast]
  exact hir

theorem Real.irrat_of_irrat_plus_rat {x y : Real} (hx : x.irrational) (hy : y.rational) : (x + y).irrational := by
  by_contra hrat
  choose sum hsum using hrat
  choose qy hqy using hy
  rw[hqy] at hsum
  set  qx := sum - qy
  push_neg at hx
  specialize hx qx
  have : x = qx := by simp[qx];exact eq_sub_of_add_eq hsum
  contradiction


theorem Real.irrat_between {x y:Real} (hxy: x < y) :
    ∃ z, x < z ∧ z < y ∧ ¬ ∃ q:ℚ, z = (q:Real) := by
      observe hdifp : (y-x).IsPos
      choose ir hirp hir using exist_pos_irrational
      rw[isPos_iff] at hirp
      choose M hM hεir using le_mul hdifp ir
      set ε := (ir/ M) / 2
      have hεp : ε > 0 := by 
        simp[ε]
        apply div_pos hirp 
        simpa
      have hεirr : ε.irrational := by
        simp[ε]
        contrapose! hir
        push_neg
        choose q hq using hir
        use q * M * 2
        field_simp[← hq];ring
      by_cases hεpir : (x + ε).irrational 
      . 
        use (x+ε)
        split_ands
        . simp[hεp]
        . simp[ε]
          calc
            _ < x + ir / M := by simp; positivity
            _ < x + (y - x) := by gcongr; rw[div_lt_iff₀' (by simp[hM])]; grind
            _ = _ := by abel
        exact hεpir
      replace hεpir : (x + ε).rational := by
        simpa using hεpir 
      use (x + ε + ε)
      split_ands
      . rw[add_assoc];simp[hεp]
      . simp[ε]
        calc
          _ = x + ir / M := by ring
          _ < x + (y - x) := by gcongr; rw[div_lt_iff₀' (by simp[hM])];grind
          _ = _ := by simp
      rw[add_comm]
      apply irrat_of_irrat_plus_rat hεirr hεpir 

/- Use the notion of supremum in this section to define a Mathlib `sSup` operation -/
noncomputable instance Real.inst_SupSet : SupSet Real where
  sSup E := ((ExtendedReal.sup E):Real)

/-- Use the `sSup` operation to build a conditionally complete lattice structure on `Real`-/
noncomputable instance Real.inst_conditionallyCompleteLattice :
    ConditionallyCompleteLattice Real :=
  conditionallyCompleteLatticeOfLatticeOfsSup Real
  (by intros; solve_by_elim [ExtendedReal.sup_of_bounded])

theorem ExtendedReal.sSup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sSup E) := sup_of_bounded hnon hb

end Chapter5
