import Mathlib

/-!
# Condorcet's jury theorem, small and exact

Each of `n` independent voters is right with probability `p`; the majority is right with
probability `maj n p = Σ_{k ≤ n, 2k > n} C(n,k) p^k (1-p)^(n-k)` (the condition `2k > n`
is `k > n/2` read over the reals).

PROVED
* `maj_three` : `maj 3 p = 3p² - 2p³`.
* `maj_five`  : `maj 5 p = 10p³(1-p)² + 5p⁴(1-p) + p⁵`.
* `three_gt` : `p ∈ (1/2,1) → 3p² - 2p³ > p`.
* `three_lt` : `p ∈ (0,1/2) → 3p² - 2p³ < p`.
* `three_eq_iff` : `3p² - 2p³ = p ↔ p = 0 ∨ p = 1/2 ∨ p = 1`.
* `five_gt_three` : `p ∈ (1/2,1) → 10p³(1-p)² + 5p⁴(1-p) + p⁵ > 3p² - 2p³`.
* `maj_step` : for `n = 2m+1`,
  `maj (2m+3) p = maj (2m+1) p + C(2m+1,m) (p(1-p))^(m+1) (2p-1)` (all real `p`).
* `maj_strictMono` : for `p ∈ (1/2,1)`, `m ↦ maj (2m+1) p` is strictly increasing.
* `condorcet` : for odd `n ≥ 3` and `p ∈ (1/2,1)`, `maj n p > p`.

INTERPRETED
* "Probability the majority is right" is taken to be the binomial upper-tail sum `maj n p`
  above; no measure-theoretic model of independent voters is constructed.
-/

namespace CondorcetJuryB

open Finset

/-- Probability that the strict majority of `n` voters, each right with probability `p`,
is right: `Σ_{k ≤ n, n < 2k} C(n,k) p^k (1-p)^(n-k)`. -/
noncomputable def maj (n : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ (range (n + 1)).filter (fun k => n < 2 * k),
    (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

/-- Single binomial term with independent parameters `p` and `q`. -/
noncomputable def f (p q : ℝ) (n k : ℕ) : ℝ := (n.choose k : ℝ) * p ^ k * q ^ (n - k)

/-- Upper tail `Σ_{j ≤ k ≤ n} f n k`. -/
noncomputable def T (p q : ℝ) (n j : ℕ) : ℝ := ∑ k ∈ Ico j (n + 1), f p q n k

lemma f_eq_zero {p q : ℝ} {n k : ℕ} (h : n < k) : f p q n k = 0 := by
  simp [f, Nat.choose_eq_zero_of_lt h]

lemma f_succ (p q : ℝ) (n k : ℕ) :
    f p q (n + 1) (k + 1) = p * f p q n k + q * f p q n (k + 1) := by
  unfold f
  rw [Nat.choose_succ_succ, Nat.cast_add]
  rcases lt_or_ge n (k + 1) with h | h
  · rw [Nat.choose_eq_zero_of_lt h]
    rcases lt_or_ge n k with h' | h'
    · rw [Nat.choose_eq_zero_of_lt h']; simp
    · have : n - k = 0 := by omega
      have h2 : n + 1 - (k + 1) = 0 := by omega
      rw [this, h2]; simp; ring
  · have h1 : n + 1 - (k + 1) = n - k := by omega
    have h2 : n - k = (n - (k + 1)) + 1 := by omega
    rw [h1, h2]; ring

lemma T_succ (p q : ℝ) (n j : ℕ) :
    T p q (n + 1) (j + 1) = p * T p q n j + q * T p q n (j + 1) := by
  unfold T
  have hs : ∑ k ∈ Ico (j + 1) (n + 1 + 1), f p q (n + 1) k
      = ∑ k ∈ Ico j (n + 1), f p q (n + 1) (k + 1) := by
    rw [Finset.sum_Ico_add' (fun k => f p q (n + 1) k) j (n + 1) 1]
  rw [hs]
  simp_rw [f_succ, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  congr 1
  rw [Finset.sum_Ico_add' (fun k => f p q n k) j (n + 1) 1]
  rcases le_or_gt (j + 1) (n + 1) with h | h
  · rw [Finset.sum_Ico_succ_top h, f_eq_zero (Nat.lt_succ_self n), add_zero]
  · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.Ico_eq_empty_of_le (by omega)]

lemma T_bot (p q : ℝ) {n j : ℕ} (h : j ≤ n) :
    T p q n j = f p q n j + T p q n (j + 1) := by
  unfold T
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]

lemma T_succ_up {p q : ℝ} (hpq : p + q = 1) {n j : ℕ} (h : j ≤ n) :
    T p q (n + 1) (j + 1) = T p q n (j + 1) + p * f p q n j := by
  rw [T_succ, T_bot p q h]
  have : q = 1 - p := by linarith
  subst this; ring

lemma T_succ_down {p q : ℝ} (hpq : p + q = 1) {n j : ℕ} (h : j ≤ n) :
    T p q (n + 1) (j + 1) = T p q n j - q * f p q n j := by
  rw [T_succ, T_bot p q h]
  have : q = 1 - p := by linarith
  subst this; ring

lemma maj_eq_T (p : ℝ) (m : ℕ) : maj (2 * m + 1) p = T p (1 - p) (2 * m + 1) (m + 1) := by
  unfold maj T f
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

/-- Adding two voters changes the majority probability by `C(2m+1,m) (p(1-p))^(m+1) (2p-1)`. -/
theorem maj_step (p : ℝ) (m : ℕ) :
    maj (2 * (m + 1) + 1) p
      = maj (2 * m + 1) p + ((2 * m + 1).choose m : ℝ) * (p * (1 - p)) ^ (m + 1) * (2 * p - 1) := by
  have hpq : p + (1 - p) = 1 := by ring
  rw [maj_eq_T, maj_eq_T]
  have e1 : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by ring
  rw [e1, T_succ_down hpq (by omega : m + 1 ≤ 2 * m + 2)]
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, T_succ_up hpq (by omega : m ≤ 2 * m + 1)]
  have hc : ((2 * m + 1 + 1).choose (m + 1) : ℝ) = 2 * ((2 * m + 1).choose m : ℝ) := by
    rw [Nat.choose_succ_succ, Nat.cast_add, Nat.choose_symm_half]; ring
  unfold f
  rw [hc]
  have h1 : 2 * m + 1 + 1 - (m + 1) = m + 1 := by omega
  have h2 : 2 * m + 1 - m = m + 1 := by omega
  rw [h1, h2, mul_pow]
  ring

theorem maj_strictMono {p : ℝ} (h1 : 1 / 2 < p) (h2 : p < 1) :
    StrictMono (fun m : ℕ => maj (2 * m + 1) p) := by
  apply strictMono_nat_of_lt_succ
  intro m
  show maj (2 * m + 1) p < maj (2 * (m + 1) + 1) p
  rw [maj_step]
  have hc : (0 : ℝ) < ((2 * m + 1).choose m : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hpq : 0 < p * (1 - p) := mul_pos (by linarith) (by linarith)
  have := mul_pos (mul_pos hc (pow_pos hpq (m + 1))) (show (0 : ℝ) < 2 * p - 1 by linarith)
  linarith

lemma maj_one (p : ℝ) : maj 1 p = p := by
  unfold maj
  simp [Finset.sum_filter, Finset.sum_range_succ]

theorem maj_three (p : ℝ) : maj 3 p = 3 * p ^ 2 - 2 * p ^ 3 := by
  unfold maj
  simp [Finset.sum_filter, Finset.sum_range_succ, Nat.choose]
  ring

theorem maj_five (p : ℝ) :
    maj 5 p = 10 * p ^ 3 * (1 - p) ^ 2 + 5 * p ^ 4 * (1 - p) + p ^ 5 := by
  unfold maj
  simp [Finset.sum_filter, Finset.sum_range_succ, Nat.choose]

lemma three_sub (p : ℝ) : 3 * p ^ 2 - 2 * p ^ 3 - p = p * (2 * p - 1) * (1 - p) := by ring

theorem three_gt {p : ℝ} (h1 : 1 / 2 < p) (h2 : p < 1) : 3 * p ^ 2 - 2 * p ^ 3 > p := by
  have := mul_pos (mul_pos (show 0 < p by linarith) (show 0 < 2 * p - 1 by linarith))
    (show 0 < 1 - p by linarith)
  linarith [three_sub p]

theorem three_lt {p : ℝ} (h1 : 0 < p) (h2 : p < 1 / 2) : 3 * p ^ 2 - 2 * p ^ 3 < p := by
  have := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h1 (show 2 * p - 1 < 0 by linarith))
    (show 0 < 1 - p by linarith)
  linarith [three_sub p]

theorem three_eq_iff (p : ℝ) : 3 * p ^ 2 - 2 * p ^ 3 = p ↔ p = 0 ∨ p = 1 / 2 ∨ p = 1 := by
  rw [← sub_eq_zero, three_sub]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))
  · rintro (h | h | h) <;> subst h <;> norm_num

theorem five_gt_three {p : ℝ} (h1 : 1 / 2 < p) (h2 : p < 1) :
    10 * p ^ 3 * (1 - p) ^ 2 + 5 * p ^ 4 * (1 - p) + p ^ 5 > 3 * p ^ 2 - 2 * p ^ 3 := by
  have e : 10 * p ^ 3 * (1 - p) ^ 2 + 5 * p ^ 4 * (1 - p) + p ^ 5 - (3 * p ^ 2 - 2 * p ^ 3)
      = 3 * p ^ 2 * (1 - p) ^ 2 * (2 * p - 1) := by ring
  have hp : 0 < p := by linarith
  have := mul_pos (mul_pos (mul_pos (show (0:ℝ) < 3 by norm_num) (pow_pos hp 2))
    (pow_pos (show 0 < 1 - p by linarith) 2)) (show 0 < 2 * p - 1 by linarith)
  linarith

/-- Condorcet's jury theorem: for odd `n ≥ 3` and `p ∈ (1/2,1)`, the majority is right with
probability strictly greater than `p`. -/
theorem condorcet {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) {p : ℝ} (h1 : 1 / 2 < p) (h2 : p < 1) :
    maj n p > p := by
  obtain ⟨m, rfl⟩ := hn
  have hm : 0 < m := by omega
  have := maj_strictMono h1 h2 hm
  simp only [mul_zero, zero_add] at this
  rw [maj_one] at this
  exact this

end CondorcetJuryB
