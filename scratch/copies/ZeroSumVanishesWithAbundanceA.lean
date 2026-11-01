import Mathlib

/-!
# Zero-sum conflict vanishes with abundance

Model. Two players each claim one of `n` resources, uniformly and independently, so the
outcome space is `Fin n × Fin n` with weight `1 / n^2` on each outcome. A claimed resource is
worth `1`; if both claim the same resource they split it, `1/2` each. The CoCo decomposition
of an outcome with payoffs `(a, b)` is the shared part `(a + b) / 2` and the zero-sum part
`(a - b) / 2`.

PROVED
* `payB_eq_payA` : the two players' payoffs agree at every outcome (symmetry).
* `sum_payA` : the total of player A's payoff over all `n^2` outcomes is `n * n - n / 2`.
* `expected_payA`, `expected_payB` : each player's expected payoff is `1 - 1 / (2 n)` (for `n ≥ 1`).
* `conflict_loss_A`, `conflict_loss_B` : the expected loss relative to no interaction
  (payoff `1`) is exactly `1 / (2 n)` per player.
* `conflict_loss_tendsto_zero` : that loss tends to `0` as `n → ∞`.
* `zeroSum_eq_zero` : the zero-sum part is `0` at every outcome (the game is symmetric).
* `expected_zeroSum` : hence its expectation is `0`.
* `expected_shared` : the expected shared part equals `1 - 1 / (2 n)`.
* `expected_shared_tendsto_one` : the expected shared part tends to `1` as `n → ∞`.
-/

namespace ZeroSumVanishesWithAbundanceA

open Filter Topology

/-- Player A claims `i`, player B claims `j`; A gets `1/2` on collision, else `1`. -/
noncomputable def payA {n : ℕ} (i j : Fin n) : ℝ := if i = j then 1 / 2 else 1

/-- Player B's payoff at the same outcome. -/
noncomputable def payB {n : ℕ} (i j : Fin n) : ℝ := if j = i then 1 / 2 else 1

/-- Expectation under the uniform independent distribution on `Fin n × Fin n`. -/
noncomputable def expect {n : ℕ} (f : Fin n → Fin n → ℝ) : ℝ :=
  (∑ p : Fin n × Fin n, f p.1 p.2) / ((n : ℝ) ^ 2)

/-- CoCo shared (cooperative) part at an outcome. -/
noncomputable def shared {n : ℕ} (i j : Fin n) : ℝ := (payA i j + payB i j) / 2

/-- CoCo zero-sum (competitive) part at an outcome. -/
noncomputable def zeroSum {n : ℕ} (i j : Fin n) : ℝ := (payA i j - payB i j) / 2

theorem payB_eq_payA {n : ℕ} (i j : Fin n) : payB i j = payA i j := by
  unfold payA payB
  by_cases h : i = j
  · simp [h]
  · have h' : ¬ j = i := fun e => h e.symm
    simp [h, h']

theorem sum_payA (n : ℕ) :
    ∑ p : Fin n × Fin n, payA p.1 p.2 = (n : ℝ) * n - n / 2 := by
  have hrow : ∀ i : Fin n, ∑ j : Fin n, payA i j = (n : ℝ) - 1 / 2 := by
    intro i
    have : ∀ j : Fin n, payA i j = 1 - (if i = j then (1 : ℝ) / 2 else 0) := by
      intro j
      unfold payA
      split_ifs <;> norm_num
    simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [Fintype.sum_prod_type]
  simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem expected_payA {n : ℕ} (hn : 0 < n) :
    expect (payA (n := n)) = 1 - 1 / (2 * (n : ℝ)) := by
  unfold expect
  rw [sum_payA]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem expected_payB {n : ℕ} (hn : 0 < n) :
    expect (payB (n := n)) = 1 - 1 / (2 * (n : ℝ)) := by
  have : (payB (n := n)) = payA := by
    funext i j; exact payB_eq_payA i j
  rw [this]; exact expected_payA hn

theorem conflict_loss_A {n : ℕ} (hn : 0 < n) :
    1 - expect (payA (n := n)) = 1 / (2 * (n : ℝ)) := by
  rw [expected_payA hn]; ring

theorem conflict_loss_B {n : ℕ} (hn : 0 < n) :
    1 - expect (payB (n := n)) = 1 / (2 * (n : ℝ)) := by
  rw [expected_payB hn]; ring

theorem conflict_loss_tendsto_zero :
    Tendsto (fun n : ℕ => 1 - expect (payA (n := n))) atTop (𝓝 0) := by
  have h : ∀ᶠ n : ℕ in atTop, 1 / (2 * (n : ℝ)) = 1 - expect (payA (n := n)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (conflict_loss_A hn).symm
  refine Tendsto.congr' h ?_
  have : Tendsto (fun n : ℕ => (2 * (n : ℝ))) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have h2 := this.inv_tendsto_atTop
  refine h2.congr' (Eventually.of_forall fun n => ?_)
  simp [one_div]

theorem zeroSum_eq_zero {n : ℕ} (i j : Fin n) : zeroSum i j = 0 := by
  unfold zeroSum; rw [payB_eq_payA]; ring

theorem expected_zeroSum (n : ℕ) : expect (zeroSum (n := n)) = 0 := by
  unfold expect; simp [zeroSum_eq_zero]

theorem expected_shared {n : ℕ} (hn : 0 < n) :
    expect (shared (n := n)) = 1 - 1 / (2 * (n : ℝ)) := by
  have : (shared (n := n)) = payA := by
    funext i j; unfold shared; rw [payB_eq_payA]; ring
  rw [this]; exact expected_payA hn

theorem expected_shared_tendsto_one :
    Tendsto (fun n : ℕ => expect (shared (n := n))) atTop (𝓝 1) := by
  have h : ∀ᶠ n : ℕ in atTop,
      1 - (1 - expect (payA (n := n))) = expect (shared (n := n)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [expected_shared hn, expected_payA hn]; ring
  refine Tendsto.congr' h ?_
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub conflict_loss_tendsto_zero

end ZeroSumVanishesWithAbundanceA
