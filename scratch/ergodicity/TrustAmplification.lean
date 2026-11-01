/-
# Trust along a chain decays; trust by majority amplifies

A source is reliable with probability p. Sources are independent.

PROVED
Modelling choices (definitions, not derived): a chain of independent relays is reliable with
probability ∏ pᵢ, and a majority of three independent sources each reliable with probability p is
reliable with probability maj3 p = p³ + 3p²(1 − p).

1. `chain_bound`, `chain_decays`: ∏ pᵢ ≤ cⁿ when each pᵢ ∈ [0, c], and cⁿ → 0 when 0 ≤ c < 1.
2. `maj3_gap`: maj3 p − p = p(1 − p)(2p − 1).
3. `maj3_amplifies`, `maj3_attenuates`: so majority improves reliability when 1/2 < p < 1 and worsens
   it when 0 < p < 1/2.
4. `maj3_symm`: maj3 (1 − p) = 1 − maj3 p.
5. `iterated_majority_to_one`: taking majorities of majorities, starting from any p with 1/2 < p ≤ 1,
   the reliability tends to 1.

6. `iterate_symm`: k levels of majority commute with the flip p ↦ 1 − p.
7. `iterated_majority_to_zero`: starting from any p with 0 ≤ p < 1/2, iterated majority tends to 0.
8. `coin_is_fixed`: p = 1/2 is fixed at every level: majority cannot extract reliability from a fair coin.
   Together with items 5 and 7: a sharp threshold at 1/2.
9. `error_squares`, `error_bound`: the error e = 1 − p satisfies e' ≤ 3e² per level, so after k levels
   3e_k ≤ (3e₀)^(2^k).

INTERPRETED (not formalized)
- Trust is not transitive along a single chain (item 1).
- From item 9, error ε is reached once k ≥ log₂(log(1/(3ε)) / log(1/(3e₀))), when 3e₀ < 1: doubly
  exponential convergence.
- Trust becomes "transitive eventually, almost surely" only through redundancy: independent paths
  combined by majority, and only when each path is better than a coin. Below 1/2, the same procedure
  drives reliability to 0.

CITED
- Condorcet's jury theorem: the majority of n independent voters each correct with probability p > 1/2
  is correct with probability tending to 1 as n grows.
-/

import Mathlib

namespace TrustAmplification

open Filter Topology

theorem chain_bound (n : ℕ) (p : Fin n → ℝ) (c : ℝ) (h0 : ∀ i, 0 ≤ p i) (hc : ∀ i, p i ≤ c) :
    ∏ i, p i ≤ c ^ n := by
  calc ∏ i, p i ≤ ∏ _i : Fin n, c := by
        apply Finset.prod_le_prod₀
        · intro i _; exact h0 i
        · intro i _; exact hc i
    _ = c ^ n := Fin.prod_const n c

theorem chain_decays (c : ℝ) (h0 : 0 ≤ c) (h1 : c < 1) : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1

def maj3 (p : ℝ) : ℝ := p ^ 3 + 3 * p ^ 2 * (1 - p)

theorem maj3_gap (p : ℝ) : maj3 p - p = p * (1 - p) * (2 * p - 1) := by
  unfold maj3; ring

theorem maj3_amplifies (p : ℝ) (h1 : 1 / 2 < p) (h2 : p < 1) : p < maj3 p := by
  have := maj3_gap p
  have hpos : 0 < p * (1 - p) * (2 * p - 1) := by
    apply mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  linarith

theorem maj3_attenuates (p : ℝ) (h1 : 0 < p) (h2 : p < 1 / 2) : maj3 p < p := by
  have := maj3_gap p
  have hneg : p * (1 - p) * (2 * p - 1) < 0 := by
    apply mul_neg_of_pos_of_neg (mul_pos h1 (by linarith)) (by linarith)
  linarith

theorem maj3_symm (p : ℝ) : maj3 (1 - p) = 1 - maj3 p := by
  unfold maj3; ring

theorem maj3_le_one (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : maj3 p ≤ 1 := by
  have : 1 - maj3 p = (1 - p) ^ 2 * (1 + 2 * p) := by unfold maj3; ring
  nlinarith [sq_nonneg (1 - p)]

theorem maj3_mono (p q : ℝ) (hp : 0 ≤ p) (hq : q ≤ 1) (hpq : p ≤ q) : maj3 p ≤ maj3 q := by
  have : maj3 q - maj3 p = (q - p) * (3 * (p + q) - 2 * (p ^ 2 + p * q + q ^ 2)) := by
    unfold maj3; ring
  have h3 : 0 ≤ 3 * (p + q) - 2 * (p ^ 2 + p * q + q ^ 2) := by nlinarith
  nlinarith

theorem iterated_majority_to_one (p : ℝ) (h1 : 1 / 2 < p) (h2 : p ≤ 1) :
    Tendsto (fun n => maj3^[n] p) atTop (𝓝 1) := by
  set a : ℕ → ℝ := fun n => maj3^[n] p
  have hbounds : ∀ n, 1 / 2 < a n ∧ a n ≤ 1 := by
    intro n
    induction n with
    | zero => exact ⟨h1, h2⟩
    | succ n ih =>
      have hs : a (n + 1) = maj3 (a n) := Function.iterate_succ_apply' maj3 n p
      rw [hs]
      refine ⟨?_, maj3_le_one _ (by linarith [ih.1]) ih.2⟩
      rcases lt_or_eq_of_le ih.2 with hlt | heq
      · linarith [maj3_amplifies (a n) ih.1 hlt, ih.1]
      · rw [heq]; norm_num [maj3]
  have hstep : ∀ n, a n ≤ a (n + 1) := by
    intro n
    have hs : a (n + 1) = maj3 (a n) := Function.iterate_succ_apply' maj3 n p
    rw [hs]
    rcases lt_or_eq_of_le (hbounds n).2 with hlt | heq
    · exact (maj3_amplifies (a n) (hbounds n).1 hlt).le
    · rw [heq]; norm_num [maj3]
  have hmono : Monotone a := monotone_nat_of_le_succ hstep
  have hbdd : BddAbove (Set.range a) := ⟨1, by rintro _ ⟨n, rfl⟩; exact (hbounds n).2⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ n, a n
  have hcont : Continuous maj3 := by unfold maj3; fun_prop
  have hlim' : Tendsto (fun n => a (n + 1)) atTop (𝓝 (maj3 L)) := by
    have : (fun n => a (n + 1)) = fun n => maj3 (a n) :=
      funext fun n => Function.iterate_succ_apply' maj3 n p
    rw [this]
    exact (hcont.tendsto L).comp hlim
  have hlim'' : Tendsto (fun n => a (n + 1)) atTop (𝓝 L) := (tendsto_add_atTop_iff_nat 1).mpr hlim
  have hfix : maj3 L = L := tendsto_nhds_unique hlim' hlim''
  have hL1 : L ≤ 1 := ciSup_le fun n => (hbounds n).2
  have hLp : 1 / 2 < L := lt_of_lt_of_le (hbounds 0).1 (le_ciSup hbdd 0)
  have hgap := maj3_gap L
  rw [hfix, sub_self] at hgap
  have hL : L = 1 := by
    rcases mul_eq_zero.mp hgap.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · linarith
      · linarith
    · linarith
  rw [← hL]
  exact hlim

theorem iterate_symm (k : ℕ) (p : ℝ) : maj3^[k] (1 - p) = 1 - maj3^[k] p := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, maj3_symm, ih]

theorem iterated_majority_to_zero (p : ℝ) (h0 : 0 ≤ p) (h1 : p < 1 / 2) :
    Tendsto (fun n => maj3^[n] p) atTop (𝓝 0) := by
  have h := iterated_majority_to_one (1 - p) (by linarith) (by linarith)
  have h' : Tendsto (fun n => 1 - maj3^[n] (1 - p)) atTop (𝓝 (1 - 1)) := tendsto_const_nhds.sub h
  rw [sub_self] at h'
  refine h'.congr fun n => ?_
  rw [iterate_symm, sub_sub_cancel]

theorem coin_is_fixed (k : ℕ) : maj3^[k] (1 / 2) = 1 / 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    norm_num [maj3]

theorem error_squares (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : 1 - maj3 p ≤ 3 * (1 - p) ^ 2 := by
  have : 1 - maj3 p = (1 - p) ^ 2 * (1 + 2 * p) := by unfold maj3; ring
  rw [this]
  nlinarith [sq_nonneg (1 - p)]

theorem error_bound (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (k : ℕ) :
    3 * (1 - maj3^[k] p) ≤ (3 * (1 - p)) ^ (2 ^ k) := by
  have hrange : ∀ k, 0 ≤ maj3^[k] p ∧ maj3^[k] p ≤ 1 := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨?_, maj3_le_one _ ih.1 ih.2⟩
      unfold maj3
      have hx := ih.1
      have hy : 0 ≤ 1 - maj3^[k] p := by linarith [ih.2]
      exact add_nonneg (pow_nonneg hx 3) (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hy)
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ, pow_mul]
    have hsq := error_squares (maj3^[k] p) (hrange k).1 (hrange k).2
    have hnn : 0 ≤ 3 * (1 - maj3^[k] p) := by linarith [(hrange k).2]
    calc 3 * (1 - maj3 (maj3^[k] p)) ≤ (3 * (1 - maj3^[k] p)) ^ 2 := by nlinarith [hsq]
      _ ≤ ((3 * (1 - p)) ^ 2 ^ k) ^ 2 := by gcongr

end TrustAmplification

#print axioms TrustAmplification.chain_bound
#print axioms TrustAmplification.chain_decays
#print axioms TrustAmplification.maj3_gap
#print axioms TrustAmplification.maj3_amplifies
#print axioms TrustAmplification.maj3_attenuates
#print axioms TrustAmplification.maj3_symm
#print axioms TrustAmplification.iterated_majority_to_one
#print axioms TrustAmplification.iterate_symm
#print axioms TrustAmplification.iterated_majority_to_zero
#print axioms TrustAmplification.coin_is_fixed
#print axioms TrustAmplification.error_squares
#print axioms TrustAmplification.error_bound
