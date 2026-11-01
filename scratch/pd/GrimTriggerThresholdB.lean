import Mathlib

/-!
# Grim trigger threshold in the infinitely repeated prisoner's dilemma

Payoffs `T > R > P > S` (reals). Each round the game continues with probability
`δ ∈ [0,1)`, so a stream paying `a` every round has expected value `a / (1 - δ)`.

PROVED
* `coop_ge_deviate_iff`: for `0 ≤ δ < 1`,
  `R / (1 - δ) ≥ T + δ * P / (1 - δ) ↔ δ ≥ (T - R) / (T - P)`.
* `threshold_pos`, `threshold_lt_one`, `threshold_mem_Ioo`:
  `0 < (T - R) / (T - P) < 1`.
* `hasSum_rounds`, `tsum_rounds`: `∑_{k ≥ 0} δ ^ k = 1 / (1 - δ)` (as `HasSum` and `tsum`).

INTERPRETED
* `R / (1 - δ)` is the expected value of cooperating forever against grim trigger;
  `T + δ * P / (1 - δ)` is the expected value of a one-shot deviation (temptation `T`
  now, mutual punishment `P` in every later round). The informal "stream paying `a`
  forever is worth `a/(1-δ)`" is justified by `hasSum_stream`.
* `S` and `S < P` appear as hypotheses for fidelity to the PD setup; the statements
  use only `T > R > P`.
-/

namespace GrimTriggerThresholdB

/-- Cooperation against grim trigger is weakly better than a one-shot deviation iff
`δ` is at least the threshold `(T - R) / (T - P)`. -/
theorem coop_ge_deviate_iff (T R P S δ : ℝ) (hTR : T > R) (hRP : R > P) (_hPS : P > S)
    (_hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    R / (1 - δ) ≥ T + δ * P / (1 - δ) ↔ δ ≥ (T - R) / (T - P) := by
  have h1 : 0 < 1 - δ := by linarith
  have hTP : 0 < T - P := by linarith
  have lhs : T + δ * P / (1 - δ) = (T * (1 - δ) + δ * P) / (1 - δ) := by
    field_simp
  rw [lhs, ge_iff_le, ge_iff_le, div_le_div_iff_of_pos_right h1, div_le_iff₀ hTP]
  constructor <;> intro h <;> nlinarith

/-- The threshold is strictly positive. -/
theorem threshold_pos (T R P S : ℝ) (hTR : T > R) (hRP : R > P) (_hPS : P > S) :
    0 < (T - R) / (T - P) :=
  div_pos (by linarith) (by linarith)

/-- The threshold is strictly below one. -/
theorem threshold_lt_one (T R P S : ℝ) (hTR : T > R) (hRP : R > P) (_hPS : P > S) :
    (T - R) / (T - P) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

/-- The threshold lies in the open interval `(0, 1)`. -/
theorem threshold_mem_Ioo (T R P S : ℝ) (hTR : T > R) (hRP : R > P) (hPS : P > S) :
    (T - R) / (T - P) ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨threshold_pos T R P S hTR hRP hPS, threshold_lt_one T R P S hTR hRP hPS⟩

/-- Expected number of rounds: `∑_{k ≥ 0} δ ^ k = 1 / (1 - δ)`. -/
theorem hasSum_rounds (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    HasSum (fun k : ℕ => δ ^ k) (1 / (1 - δ)) := by
  rw [one_div]
  exact hasSum_geometric_of_lt_one hδ0 hδ1

/-- `tsum` form of `hasSum_rounds`. -/
theorem tsum_rounds (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∑' k : ℕ, δ ^ k = 1 / (1 - δ) :=
  (hasSum_rounds δ hδ0 hδ1).tsum_eq

/-- A stream paying `a` in every round reached (round `k` reached with probability `δ ^ k`)
has expected value `a / (1 - δ)`. -/
theorem hasSum_stream (a δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    HasSum (fun k : ℕ => a * δ ^ k) (a / (1 - δ)) := by
  have h := (hasSum_rounds δ hδ0 hδ1).mul_left a
  rwa [mul_one_div] at h

end GrimTriggerThresholdB
