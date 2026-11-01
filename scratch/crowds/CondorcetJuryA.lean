import Mathlib

/-!
# Condorcet's jury theorem, small and exact

`majorityProb n p = ∑_{k ≤ n, n < 2k} C(n,k) p^k (1-p)^(n-k)`: the probability that a strict
majority of `n` independent voters, each right with probability `p`, is right.

PROVED
* `majorityProb_three`: `majorityProb 3 p = 3p² − 2p³`.
* `majorityProb_five`: `majorityProb 5 p = 10p³(1−p)² + 5p⁴(1−p) + p⁵`.
* `three_gt`: `3p² − 2p³ > p` for `p ∈ (1/2, 1)`.
* `three_lt`: `3p² − 2p³ < p` for `p ∈ (0, 1/2)`.
* `three_eq_iff`: `3p² − 2p³ = p ↔ p = 0 ∨ p = 1/2 ∨ p = 1`.
* `five_gt_three`: the `n = 5` value exceeds the `n = 3` value for `p ∈ (1/2, 1)`.
* `majorityProb_odd_succ`: the exact step identity
  `majorityProb (2m+3) p = majorityProb (2m+1) p + C(2m+1,m) (p(1−p))^(m+1) (2p−1)`.
* `majorityProb_strictMono`: for `p ∈ (1/2, 1)` the majority probability is strictly increasing
  along odd jury sizes.
* `condorcet_jury` (general statement): for odd `n ≥ 3` and `p ∈ (1/2, 1)`,
  `majorityProb n p > p`.
* `condorcet_jury_lt` (mirror): for odd `n ≥ 3` and `p ∈ (0, 1/2)`, `majorityProb n p < p`.

INTERPRETED
* "independent voters each right with probability `p`" is encoded by the binomial sum itself;
  no measure-theoretic model is built.
* "`k > n/2`" is read as `n < 2k` (real-valued half), which for odd `n` is the strict majority.
-/

namespace CondorcetJuryA

open Finset

/-- Probability that a strict majority of `n` voters is right. -/
noncomputable def majorityProb (n : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ (range (n + 1)).filter (fun k => n < 2 * k),
    (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

/-- Probability that at most `r - 1` of `n` voters are wrong. -/
noncomputable def S (n r : ℕ) (p : ℝ) : ℝ :=
  ∑ i ∈ range r, (n.choose i : ℝ) * p ^ (n - i) * (1 - p) ^ i

theorem majorityProb_three (p : ℝ) : majorityProb 3 p = 3 * p ^ 2 - 2 * p ^ 3 := by
  simp [majorityProb, Finset.sum_filter, Finset.sum_range_succ, Nat.choose]
  ring

theorem majorityProb_five (p : ℝ) :
    majorityProb 5 p = 10 * p ^ 3 * (1 - p) ^ 2 + 5 * p ^ 4 * (1 - p) + p ^ 5 := by
  simp [majorityProb, Finset.sum_filter, Finset.sum_range_succ, Nat.choose]

theorem three_gt {p : ℝ} (h1 : 1 / 2 < p) (h2 : p < 1) : p < 3 * p ^ 2 - 2 * p ^ 3 := by
  have h : 3 * p ^ 2 - 2 * p ^ 3 - p = p * (2 * p - 1) * (1 - p) := by ring
  have : 0 < p * (2 * p - 1) * (1 - p) := by
    apply mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  linarith

theorem three_lt {p : ℝ} (h1 : 0 < p) (h2 : p < 1 / 2) : 3 * p ^ 2 - 2 * p ^ 3 < p := by
  have h : 3 * p ^ 2 - 2 * p ^ 3 - p = -(p * (1 - 2 * p) * (1 - p)) := by ring
  have : 0 < p * (1 - 2 * p) * (1 - p) := by
    apply mul_pos (mul_pos h1 (by linarith)) (by linarith)
  linarith

theorem three_eq_iff (p : ℝ) : 3 * p ^ 2 - 2 * p ^ 3 = p ↔ p = 0 ∨ p = 1 / 2 ∨ p = 1 := by
  have h : 3 * p ^ 2 - 2 * p ^ 3 - p = p * (2 * p - 1) * (1 - p) := by ring
  constructor
  · intro hp
    have h0 : p * (2 * p - 1) * (1 - p) = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h0 | h0
    · rcases mul_eq_zero.1 h0 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num

theorem five_gt_three {p : ℝ} (h1 : 1 / 2 < p) (h2 : p < 1) :
    3 * p ^ 2 - 2 * p ^ 3 < 10 * p ^ 3 * (1 - p) ^ 2 + 5 * p ^ 4 * (1 - p) + p ^ 5 := by
  have h : 10 * p ^ 3 * (1 - p) ^ 2 + 5 * p ^ 4 * (1 - p) + p ^ 5 - (3 * p ^ 2 - 2 * p ^ 3)
      = 3 * (p * (1 - p)) ^ 2 * (2 * p - 1) := by ring
  have : 0 < 3 * (p * (1 - p)) ^ 2 * (2 * p - 1) := by
    apply mul_pos (mul_pos (by norm_num) (pow_pos (mul_pos (by linarith) (by linarith)) 2))
      (by linarith)
  linarith

/-- Adding one voter: `P(wrong ≤ r)` drops by `(1-p) · P(wrong = r)`. -/
theorem S_succ (n r : ℕ) (p : ℝ) :
    S (n + 1) (r + 1) p = S n (r + 1) p - (1 - p) * ((n.choose r : ℝ) * p ^ (n - r) * (1 - p) ^ r) := by
  induction r with
  | zero => simp [S]; ring
  | succ r ih =>
    have e1 : S (n + 1) (r + 1 + 1) p = S (n + 1) (r + 1) p +
        ((n + 1).choose (r + 1) : ℝ) * p ^ (n + 1 - (r + 1)) * (1 - p) ^ (r + 1) := by
      simp [S, Finset.sum_range_succ]
    have e2 : S n (r + 1 + 1) p = S n (r + 1) p +
        (n.choose (r + 1) : ℝ) * p ^ (n - (r + 1)) * (1 - p) ^ (r + 1) := by
      simp [S, Finset.sum_range_succ]
    rw [e1, e2, ih, Nat.choose_succ_succ', Nat.cast_add, Nat.succ_sub_succ]
    rcases lt_or_ge r n with hr | hr
    · have hp : p ^ (n - r) = p ^ (n - (r + 1)) * p := by
        rw [← pow_succ]; congr 1; omega
      rw [hp]; ring
    · have h0 : n.choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h0]; simp; ring

/-- Reflection: the majority sum written by number of wrong votes. -/
theorem majorityProb_eq_S (m : ℕ) (p : ℝ) :
    majorityProb (2 * m + 1) p = S (2 * m + 1) (m + 1) p := by
  unfold majorityProb S
  rw [Finset.sum_filter]
  rw [← Finset.sum_range_reflect]
  have hsplit : 2 * m + 1 + 1 = (m + 1) + (m + 1) := by ring
  rw [hsplit, Finset.sum_range_add]
  have hrest : ∑ x ∈ range (m + 1),
      (if 2 * m + 1 < 2 * (m + 1 + (m + 1) - 1 - (m + 1 + x)) then
        ((2 * m + 1).choose (m + 1 + (m + 1) - 1 - (m + 1 + x)) : ℝ) *
          p ^ (m + 1 + (m + 1) - 1 - (m + 1 + x)) *
          (1 - p) ^ (2 * m + 1 - (m + 1 + (m + 1) - 1 - (m + 1 + x)))
      else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    split_ifs with h
    · exact absurd h (by omega)
    · rfl
  rw [hrest, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  split_ifs with h
  swap
  · exact absurd h (by omega)
  have h1 : m + 1 + (m + 1) - 1 - i = 2 * m + 1 - i := by omega
  have h2 : 2 * m + 1 - (2 * m + 1 - i) = i := by omega
  rw [h1, h2, Nat.choose_symm (by omega)]

/-- Exact step identity between consecutive odd jury sizes. -/
theorem majorityProb_odd_succ (m : ℕ) (p : ℝ) :
    majorityProb (2 * (m + 1) + 1) p = majorityProb (2 * m + 1) p +
      ((2 * m + 1).choose m : ℝ) * (p * (1 - p)) ^ (m + 1) * (2 * p - 1) := by
  rw [majorityProb_eq_S, majorityProb_eq_S]
  have e0 : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by ring
  rw [e0, S_succ]
  have e1 : S (2 * m + 2) (m + 1 + 1) p = S (2 * m + 2) (m + 1) p +
      ((2 * m + 2).choose (m + 1) : ℝ) * p ^ (2 * m + 2 - (m + 1)) * (1 - p) ^ (m + 1) := by
    simp [S, Finset.sum_range_succ]
  rw [e1]
  have e2 : S (2 * m + 2) (m + 1) p = S (2 * m + 1) (m + 1) p -
      (1 - p) * (((2 * m + 1).choose m : ℝ) * p ^ (2 * m + 1 - m) * (1 - p) ^ m) := by
    rw [show 2 * m + 2 = 2 * m + 1 + 1 by ring, S_succ]
  rw [e2]
  have hc : (2 * m + 2).choose (m + 1) = 2 * (2 * m + 1).choose m := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, Nat.choose_succ_succ',
      show m + 1 = (2 * m + 1) - m by omega, Nat.choose_symm (by omega)]
    ring
  rw [hc]
  have q1 : 2 * m + 2 - (m + 1) = m + 1 := by omega
  have q2 : 2 * m + 1 - m = m + 1 := by omega
  rw [q1, q2, mul_pow]
  push_cast
  ring

theorem majorityProb_one (p : ℝ) : majorityProb 1 p = p := by
  simp [majorityProb, Finset.sum_filter, Finset.sum_range_succ]

theorem majorityProb_lt_succ {p : ℝ} (h1 : 1 / 2 < p) (h2 : p < 1) (m : ℕ) :
    majorityProb (2 * m + 1) p < majorityProb (2 * (m + 1) + 1) p := by
  rw [majorityProb_odd_succ]
  have hc : (0 : ℝ) < ((2 * m + 1).choose m : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have : 0 < ((2 * m + 1).choose m : ℝ) * (p * (1 - p)) ^ (m + 1) * (2 * p - 1) :=
    mul_pos (mul_pos hc (pow_pos (mul_pos (by linarith) (by linarith)) _)) (by linarith)
  linarith

/-- Strict monotonicity along odd jury sizes for `p ∈ (1/2, 1)`. -/
theorem majorityProb_strictMono {p : ℝ} (h1 : 1 / 2 < p) (h2 : p < 1) :
    StrictMono (fun m : ℕ => majorityProb (2 * m + 1) p) :=
  strictMono_nat_of_lt_succ (fun m => majorityProb_lt_succ h1 h2 m)

/-- Condorcet's jury theorem (finite form): for odd `n ≥ 3` and `p ∈ (1/2, 1)`,
the majority is right with probability strictly greater than `p`. -/
theorem condorcet_jury {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) {p : ℝ}
    (h1 : 1 / 2 < p) (h2 : p < 1) : p < majorityProb n p := by
  obtain ⟨m, rfl⟩ := hodd
  have hm : 0 < m := by omega
  have := majorityProb_strictMono h1 h2 hm
  simp only [mul_zero, zero_add, majorityProb_one] at this
  exact this

theorem majorityProb_gt_succ {p : ℝ} (h1 : 0 < p) (h2 : p < 1 / 2) (m : ℕ) :
    majorityProb (2 * (m + 1) + 1) p < majorityProb (2 * m + 1) p := by
  rw [majorityProb_odd_succ]
  have hc : (0 : ℝ) < ((2 * m + 1).choose m : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have : 0 < ((2 * m + 1).choose m : ℝ) * (p * (1 - p)) ^ (m + 1) * (1 - 2 * p) :=
    mul_pos (mul_pos hc (pow_pos (mul_pos h1 (by linarith)) _)) (by linarith)
  nlinarith

/-- Mirror statement: for odd `n ≥ 3` and `p ∈ (0, 1/2)`, the majority does worse than `p`. -/
theorem condorcet_jury_lt {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) {p : ℝ}
    (h1 : 0 < p) (h2 : p < 1 / 2) : majorityProb n p < p := by
  obtain ⟨m, rfl⟩ := hodd
  have hm : 0 < m := by omega
  have hanti : StrictAnti (fun m : ℕ => majorityProb (2 * m + 1) p) :=
    strictAnti_nat_of_succ_lt (fun m => majorityProb_gt_succ h1 h2 m)
  have := hanti hm
  simp only [mul_zero, zero_add, majorityProb_one] at this
  exact this

end CondorcetJuryA
