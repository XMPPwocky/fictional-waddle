import Mathlib

/-!
# Grim trigger threshold in the repeated prisoner's dilemma with continuation probability δ

Setting: payoffs `T > R > P > S` (reals); the game continues each round with probability
`δ ∈ [0,1)`, so a stream paying `a` every round has expected value `a / (1 - δ)`.

PROVED:
* `coop_ge_deviate_iff`: `R/(1-δ) ≥ T + δ*P/(1-δ) ↔ δ ≥ (T-R)/(T-P)`.
* `threshold_pos`, `threshold_lt_one`, `threshold_mem_Ioo`: `0 < (T-R)/(T-P) < 1`.
* `hasSum_rounds`, `tsum_rounds`: `∑_{k≥0} δ^k = 1/(1-δ)` (HasSum and tsum forms).
* `hasSum_const_stream`: a stream paying `a` each round has expected value `a/(1-δ)`,
  i.e. `∑_{k≥0} δ^k * a = a/(1-δ)`.
* `hasSum_deviation_stream`: the deviation stream (`T` in round 0, `P` thereafter) has
  expected value `T + δ*P/(1-δ)`.

INTERPRETED:
* `δ^k` is the probability that round `k` (0-indexed) is played; the expected payoff of a
  per-round payoff stream `x k` is `∑ δ^k * x k`.
* Cooperating forever against grim trigger is the constant stream `R`; deviating once is
  `T` at round 0 and `P` forever after (grim trigger punishes with `D` forever and the
  best response to `D` is `D`, giving `P`).
* `S` appears only in the payoff-order hypothesis; it does not enter the threshold.
-/

namespace GrimTriggerThresholdA

/-- (1) Cooperation against grim trigger is weakly better than a one-shot deviation iff
`δ ≥ (T-R)/(T-P)`. -/
theorem coop_ge_deviate_iff {T R P S δ : ℝ} (_hTR : R < T) (_hRP : P < R) (_hPS : S < P)
    (_hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    R / (1 - δ) ≥ T + δ * P / (1 - δ) ↔ δ ≥ (T - R) / (T - P) := by
  have h1 : 0 < 1 - δ := by linarith
  have hTP : 0 < T - P := by linarith
  have key : T + δ * P / (1 - δ) = (T * (1 - δ) + δ * P) / (1 - δ) := by
    field_simp
  rw [ge_iff_le, ge_iff_le, key, div_le_div_iff_of_pos_right h1, div_le_iff₀ hTP]
  constructor <;> intro h <;> nlinarith

/-- (2a) The threshold is strictly positive. -/
theorem threshold_pos {T R P S : ℝ} (hTR : R < T) (hRP : P < R) (_hPS : S < P) :
    0 < (T - R) / (T - P) := by
  apply div_pos <;> linarith

/-- (2b) The threshold is strictly below one. -/
theorem threshold_lt_one {T R P S : ℝ} (hTR : R < T) (hRP : P < R) (_hPS : S < P) :
    (T - R) / (T - P) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

/-- (2) The threshold lies in the open interval `(0,1)`. -/
theorem threshold_mem_Ioo {T R P S : ℝ} (hTR : R < T) (hRP : P < R) (hPS : S < P) :
    (T - R) / (T - P) ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨threshold_pos hTR hRP hPS, threshold_lt_one hTR hRP hPS⟩

/-- (3) Expected number of rounds, HasSum form. -/
theorem hasSum_rounds {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    HasSum (fun k : ℕ => δ ^ k) (1 / (1 - δ)) := by
  rw [one_div]
  exact hasSum_geometric_of_lt_one hδ0 hδ1

/-- (3) Expected number of rounds, tsum form. -/
theorem tsum_rounds {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∑' k : ℕ, δ ^ k = 1 / (1 - δ) :=
  (hasSum_rounds hδ0 hδ1).tsum_eq

/-- A stream paying `a` every round has expected value `a/(1-δ)`. -/
theorem hasSum_const_stream {δ : ℝ} (a : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    HasSum (fun k : ℕ => δ ^ k * a) (a / (1 - δ)) := by
  have := (hasSum_rounds hδ0 hδ1).mul_right a
  simpa [div_eq_mul_inv, mul_comm] using this

/-- The one-shot deviation stream (`T` at round 0, `P` afterwards) has expected value
`T + δ*P/(1-δ)`. -/
theorem hasSum_deviation_stream {δ : ℝ} (T P : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    HasSum (fun k : ℕ => δ ^ k * (if k = 0 then T else P)) (T + δ * P / (1 - δ)) := by
  have hP := hasSum_const_stream P hδ0 hδ1
  have htail : HasSum (fun k : ℕ => δ ^ (k + 1) * P) (δ * (P / (1 - δ))) := by
    have := hP.mul_left δ
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one, pow_zero, one_mul, ite_true, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, ite_false]
  convert htail using 1
  ring

end GrimTriggerThresholdA
