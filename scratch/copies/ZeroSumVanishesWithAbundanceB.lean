import Mathlib

/-!
# Zero-sum conflict vanishes with abundance

Model: two players each pick a resource `i, j : Fin n` uniformly and independently, so each
outcome `(i, j) : Fin n × Fin n` has probability `1 / n ^ 2`. A claimed resource is worth 1;
if both claim the same one (`i = j`) they split it, getting `1/2` each.
Payoffs: `payoffA i j = payoffB i j = if i = j then 1/2 else 1`.
CoCo decomposition per outcome: shared part `(a + b) / 2`, zero-sum part `(a - b) / 2`.
Expectations are written explicitly as `∑ p : Fin n × Fin n, f p / n ^ 2`.

PROVED
* `expectedA_eq`, `expectedB_eq`: each player's expected payoff is `1 - 1/(2n)` (for `n ≥ 1`).
* `conflictLossA_eq`, `conflictLossB_eq`: the expected loss relative to the no-interaction
  payoff 1 is exactly `1/(2n)` per player.
* `conflictLoss_tendsto_zero`: that loss tends to 0 as `n → ∞`.
* `zeroSumPart_eq_zero`: the zero-sum part `(a - b)/2` is 0 at every outcome.
* `expectedZeroSum_eq_zero`: hence its expectation is 0 for every `n`.
* `sharedPart_eq`: the shared part `(a + b)/2` equals player A's payoff at every outcome.
* `expectedShared_eq`: the expected shared part is `1 - 1/(2n)` (for `n ≥ 1`).
* `expectedShared_tendsto_one`: the expected shared part tends to 1 as `n → ∞`.
* `coco_decomposition`: `a = shared + zeroSum` and `b = shared - zeroSum` at every outcome.
-/

namespace ZeroSumVanishesWithAbundanceB

open Filter Topology

/-- Payoff to player A when A claims `i` and B claims `j`. -/
noncomputable def payoffA {n : ℕ} (i j : Fin n) : ℝ := if i = j then 1 / 2 else 1

/-- Payoff to player B when A claims `i` and B claims `j`. -/
noncomputable def payoffB {n : ℕ} (i j : Fin n) : ℝ := if j = i then 1 / 2 else 1

/-- CoCo shared (cooperative) part at an outcome. -/
noncomputable def sharedPart {n : ℕ} (i j : Fin n) : ℝ := (payoffA i j + payoffB i j) / 2

/-- CoCo zero-sum (competitive) part at an outcome. -/
noncomputable def zeroSumPart {n : ℕ} (i j : Fin n) : ℝ := (payoffA i j - payoffB i j) / 2

/-- Expectation under the uniform independent distribution on `Fin n × Fin n`. -/
noncomputable def expect (n : ℕ) (f : Fin n → Fin n → ℝ) : ℝ :=
  ∑ p : Fin n × Fin n, f p.1 p.2 / (n : ℝ) ^ 2

noncomputable def expectedA (n : ℕ) : ℝ := expect n payoffA
noncomputable def expectedB (n : ℕ) : ℝ := expect n payoffB
noncomputable def expectedShared (n : ℕ) : ℝ := expect n sharedPart
noncomputable def expectedZeroSum (n : ℕ) : ℝ := expect n zeroSumPart

/-- Loss from conflict relative to the no-interaction payoff 1. -/
noncomputable def conflictLossA (n : ℕ) : ℝ := 1 - expectedA n
noncomputable def conflictLossB (n : ℕ) : ℝ := 1 - expectedB n

theorem payoffB_eq_payoffA {n : ℕ} (i j : Fin n) : payoffB i j = payoffA i j := by
  unfold payoffA payoffB
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem zeroSumPart_eq_zero {n : ℕ} (i j : Fin n) : zeroSumPart i j = 0 := by
  simp [zeroSumPart, payoffB_eq_payoffA]

theorem sharedPart_eq {n : ℕ} (i j : Fin n) : sharedPart i j = payoffA i j := by
  simp [sharedPart, payoffB_eq_payoffA]

theorem coco_decomposition {n : ℕ} (i j : Fin n) :
    payoffA i j = sharedPart i j + zeroSumPart i j ∧
      payoffB i j = sharedPart i j - zeroSumPart i j := by
  unfold sharedPart zeroSumPart
  constructor <;> ring

theorem sum_payoffA (n : ℕ) :
    ∑ p : Fin n × Fin n, payoffA p.1 p.2 = (n : ℝ) ^ 2 - (n : ℝ) / 2 := by
  have h : ∀ i j : Fin n, payoffA i j = 1 - (1 / 2 : ℝ) * (if i = j then 1 else 0) := by
    intro i j
    unfold payoffA
    split_ifs <;> norm_num
  rw [Fintype.sum_prod_type]
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  ring

theorem expect_eq (n : ℕ) (f : Fin n → Fin n → ℝ) :
    expect n f = (∑ p : Fin n × Fin n, f p.1 p.2) / (n : ℝ) ^ 2 := by
  unfold expect
  rw [Finset.sum_div]

theorem expectedA_eq {n : ℕ} (hn : 1 ≤ n) : expectedA n = 1 - 1 / (2 * (n : ℝ)) := by
  have hn' : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold expectedA
  rw [expect_eq, sum_payoffA]
  field_simp

theorem expectedB_eq {n : ℕ} (hn : 1 ≤ n) : expectedB n = 1 - 1 / (2 * (n : ℝ)) := by
  have : expectedB n = expectedA n := by
    unfold expectedB expectedA
    congr 1
    funext i j
    exact payoffB_eq_payoffA i j
  rw [this, expectedA_eq hn]

theorem conflictLossA_eq {n : ℕ} (hn : 1 ≤ n) : conflictLossA n = 1 / (2 * (n : ℝ)) := by
  unfold conflictLossA
  rw [expectedA_eq hn]
  ring

theorem conflictLossB_eq {n : ℕ} (hn : 1 ≤ n) : conflictLossB n = 1 / (2 * (n : ℝ)) := by
  unfold conflictLossB
  rw [expectedB_eq hn]
  ring

theorem inv_two_n_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) := by
  have h := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have : (fun n : ℕ => 1 / (2 * (n : ℝ))) = fun n : ℕ => (1 / 2 : ℝ) * (1 / (n : ℝ)) := by
    funext n
    rw [one_div_mul_one_div]
  rw [this]
  simpa using h.const_mul (1 / 2 : ℝ)

theorem conflictLoss_tendsto_zero :
    Tendsto conflictLossA atTop (𝓝 0) ∧ Tendsto conflictLossB atTop (𝓝 0) := by
  constructor
  · refine inv_two_n_tendsto_zero.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (conflictLossA_eq hn).symm
  · refine inv_two_n_tendsto_zero.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (conflictLossB_eq hn).symm

theorem expectedZeroSum_eq_zero (n : ℕ) : expectedZeroSum n = 0 := by
  unfold expectedZeroSum expect
  simp [zeroSumPart_eq_zero]

theorem expectedShared_eq {n : ℕ} (hn : 1 ≤ n) :
    expectedShared n = 1 - 1 / (2 * (n : ℝ)) := by
  have : expectedShared n = expectedA n := by
    unfold expectedShared expectedA
    congr 1
    funext i j
    exact sharedPart_eq i j
  rw [this, expectedA_eq hn]

theorem expectedShared_tendsto_one : Tendsto expectedShared atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => 1 - 1 / (2 * (n : ℝ))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub inv_two_n_tendsto_zero
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (expectedShared_eq hn).symm

end ZeroSumVanishesWithAbundanceB
