import Mathlib

/-! Formalizing a proof of Erdos problem \#379, arising from conversations between Stijn Cambie, Vjeko Kovac, and Terry Tao.-/

theorem binom_eq {n k:ℕ} (hk: 1 ≤ k) (hn: k ≤ n) : (n.choose k) * k = ((n-1).choose (k-1)) * n := by
  symm
  rw [←Nat.choose_symm]; nth_rewrite 2 [←Nat.choose_symm]
  convert Nat.choose_mul_succ_eq (n-1) ((n-1)-(k-1)) using 3
  all_goals omega

theorem binom_eq_2 {n k:ℕ} (hk: 2 ≤ k) (hn: k ≤ n) : (n.choose k) * k * (k-1) = ((n-2).choose (k-2)) * (n-1) * n := calc
  _ = ((n-1).choose (k-1)) * n * (k-1) := by rw [binom_eq] <;> omega
  _ = ((n-1).choose (k-1)) * (k-1) * n := by ring
  _ = _ := by
    rw [binom_eq]; congr 2
    all_goals omega

theorem lemma_1 {n k p a b:ℕ} (hk: 1 ≤ k) (hn: k ≤ n)
 (hp: p.Prime) (h1: p^(a+b+1) ∣ n) : p^(a+1) ∣ n.choose k ∨ p^(b+1) ∣ k := by
  replace h1 := h1.trans (n.dvd_mul_left ((n-1).choose (k-1)))
  rw [←binom_eq hk hn] at h1
  contrapose! h1
  apply Nat.Prime.prime at hp
  apply finiteMultiplicity_mul_aux <;> tauto


theorem lemma_2 {n k p r:ℕ} (hk: 2 ≤ k) (hn: k ≤ n)
 (hp: p.Prime) (h1: p^r ∣ n-1) (hr: 0 < r) (h2: ¬p∣k) (h3: ¬ p∣n-k) : p^r ∣ n.choose k := by
  have h1' : p ∣ n-1 := by
    apply dvd_trans _ h1; apply dvd_pow_self; omega
  replace h1 := h1.trans ((n-1).dvd_mul_left ((n-2).choose (k-2)))
  replace h1 := h1.trans (Nat.dvd_mul_right _ n)
  rw [←binom_eq_2 hk hn] at h1
  apply Nat.Prime.prime at hp
  replace h3 : ¬ p∣k-1 := by
    contrapose! h3
    convert Nat.dvd_sub h1' h3 using 1
    omega
  apply hp.pow_dvd_of_dvd_mul_right _ h3 at h1
  apply hp.pow_dvd_of_dvd_mul_right _ h2 at h1
  assumption

theorem key_prop {k n p r R:ℕ} (hn: n = 2^((p^R).totient))
  (hk: 1 ≤ k) (hkn: k < n) (hp: p.Prime) (hpr: p > 2^(r-1))
  (hr: 1 < r) (hr' : r ≤ (p^R).totient):
  2^r ∣ n.choose k ∨ p^R ∣ n.choose k := by
  set m := (p^R).totient
  have : 2 ^ (r - 1 + 1) ∣ n.choose k ∨ 2 ^ (m - r + 1) ∣ k := by
    apply lemma_1 hk (le_of_lt hkn) _ _
    . decide
    convert dvd_rfl; rw [hn]; congr; omega
  rcases this with this | this
  . left; convert this; omega
  have hcoprime : Nat.Coprime 2 p := by
    simp; apply hp.odd_of_ne_two
    contrapose! hpr; subst hpr; apply Nat.le_self_pow; omega
  have hrm : 2^(r-1) * 2^(m-r+1) = n := by
    rw [hn,←pow_add]; congr; omega
  have hrp : 2^(r-1) * 2^(m-r+1) < p * 2^(m-r+1) := by gcongr
  right; apply lemma_2 _ (le_of_lt hkn) hp
  . rw [←Nat.modEq_iff_dvd']; symm
    . rw [hn]; apply Nat.ModEq.pow_totient
      apply Nat.Coprime.pow_right _ hcoprime
    omega
  . by_contra!; simp at this; subst this; simp [m] at hr'; omega
  . by_contra! h
    replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ h this
    . apply Nat.le_of_dvd (by positivity) at this
      linarith
    apply Nat.Coprime.pow_right _ hcoprime.symm
  . by_contra! h
    replace : 2^(m-r+1) ∣ n-k := by
      apply Nat.dvd_sub _ this
      rw [←hrm]; apply Nat.dvd_mul_left
    replace := Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ h this
    . apply Nat.le_of_dvd (by omega) at this
      omega
    apply Nat.Coprime.pow_right _ hcoprime.symm
  apply Nat.le_of_dvd (by omega) at this
  apply LE.le.trans _ this
  apply Nat.le_self_pow
  omega

noncomputable abbrev S (n:ℕ) : ℕ := sSup { r | ∀ k ∈ Finset.Ico 1 n, ∃ p, p.Prime ∧ p^r ∣ (n.choose k) }

theorem S_ge {n r:ℕ} (hn: 1 < n) (h: ∀ k ∈ Finset.Ico 1 n, ∃ p, p.Prime ∧ p^r ∣ n.choose k) : r ≤ S n := by
  apply le_csSup
  . rw [bddAbove_def]; use n; simp; intro r h
    specialize h 1 (by simp) hn
    obtain ⟨ p, hp, hp' ⟩ := h
    simp at hp'; apply Nat.le_of_dvd (by positivity) at hp'
    have : r < p^r := Nat.lt_pow_self hp.one_lt
    order
  aesop

theorem key_cor {n p r:ℕ} (hn: n = 2^((p^r).totient))
  (hp: p.Prime) (hpr: p > 2^(r-1)) (hr: 1 < r) :
  r ≤ S n := by
  apply S_ge
  . simp [hn]; intro h; subst h; simp at hpr
  intro k hk; simp at hk
  have := key_prop hn hk.1 hk.2 hp hpr hr ?_; swap
  . sorry
  rcases this with this | this
  . use 2; simp [this, Nat.prime_two]
  use p; tauto

theorem erdos_379 : Filter.atTop.limsup (fun n ↦ (S n:EReal)) = ⊤ := by
  sorry
