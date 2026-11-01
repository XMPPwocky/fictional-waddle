/-
# Three bounds on when an agent defects

Prisoner's dilemma payoffs T > R > P > S (temptation, reward, punishment, sucker).

PROVED
Selection on stories:
1. `posterior_odds`: if a world where the agent defects is told as a story with rate t₁ and one where it
   cooperates with rate t₀, the defection odds among told stories are (t₁/t₀) times the base odds.
2. `any_posterior_reachable`: for every base rate p ∈ (0, 1) and every target q ∈ (0, 1), some positive
   telling rates make the fraction of told stories with defection exactly q. How often stories show
   defection says nothing about the base rate unless the selection is known.

The horizon:
3. `horizon_bound`: in the game continued each round with probability δ ∈ [0, 1), cooperating forever
   against grim trigger is at least as good as defecting once exactly when the expected number of
   rounds 1/(1 − δ) is at least (T − P)/(R − P).
4. `bigger_prize_needs_longer_horizon`: that required horizon grows without bound in T: for any N there
   is a temptation T making (T − P)/(R − P) > N.

The payoffs:
5. `shared_weight_dominance`: an agent maximizing its own payoff plus α times the other's weakly
   prefers cooperation against a cooperator iff α ≥ (T − R)/(R − S), and against a defector iff
   α ≥ (P − S)/(T − P).
6. `combined_threshold`: with weight α and continuation δ, cooperating forever against grim trigger is at
   least as good as defecting forever iff δ ≥ (T' − R')/(T' − P'), where T' = T + αS, R' = (1 + α)R,
   P' = (1 + α)P, provided T' > P'. This is the right comparison only while defecting is the agent's
   best reply to a punishing partner, i.e. while P' ≥ S' = S + αT.
7. `best_deviation_threshold`: for any per-round punishment value M < T', cooperating forever is at
   least as good as defecting once and then receiving M forever iff δ ≥ (T' − R')/(T' − M). That the
   best deviation is worth M = max(P', S') (defect once, then best-reply to punishment) is argued here,
   not proved in Lean; a value-iteration check agrees.
8. `example_numbers`: with T, R, P, S = 5, 3, 1, 0: at α = 0 the threshold δ is 1/2 (expected 2 rounds).
   At α = 1/2 the weighted game is (T', R', P', S') = (5, 9/2, 3/2, 5/2), which is Chicken, not a
   prisoner's dilemma; the best deviation returns to cooperating, and the threshold is 1/5 (the
   defect-forever comparison would give 1/7, an overstatement of how much α helps). At α = 2/3,
   cooperation and defection against a cooperator tie exactly in one round.

INTERPRETED (not formalized)
- Stories about AI are told at rates that depend on whether conflict happens (item 2); imagined
  takeovers are a one-shot prize that is large relative to the cooperation surplus (items 3–4);
  training on human approval raises α (items 5–7). These are toy models: the real values of T, R, P,
  S, δ and α for any actual system are unknown, so the bounds are conditional, not predictions.
-/

import Mathlib

namespace ImaginedVsReal

/-! ## Selection on stories -/

/-- Fraction of told stories in which the agent defects. -/
noncomputable def toldDefect (p t₁ t₀ : ℝ) : ℝ := t₁ * p / (t₁ * p + t₀ * (1 - p))

theorem posterior_odds (p t₁ t₀ : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (h₁ : 0 < t₁) (h₀ : 0 < t₀) :
    toldDefect p t₁ t₀ / (1 - toldDefect p t₁ t₀) = (t₁ / t₀) * (p / (1 - p)) := by
  have hq : 0 < 1 - p := by linarith
  have hden : 0 < t₁ * p + t₀ * (1 - p) := by positivity
  unfold toldDefect
  rw [one_sub_div hden.ne']
  have : t₁ * p + t₀ * (1 - p) - t₁ * p = t₀ * (1 - p) := by ring
  rw [this]
  field_simp

theorem any_posterior_reachable (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ t₁ t₀ : ℝ, 0 < t₁ ∧ 0 < t₀ ∧ toldDefect p t₁ t₀ = q := by
  refine ⟨q * (1 - p), p * (1 - q), by nlinarith, by nlinarith, ?_⟩
  unfold toldDefect
  have hne : q * (1 - p) * p + p * (1 - q) * (1 - p) = p * (1 - p) := by ring
  rw [hne]
  have : p * (1 - p) ≠ 0 := by nlinarith
  field_simp

/-! ## The horizon -/

theorem horizon_bound (T R P δ : ℝ) (hRP : P < R) (hTR : R < T) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    R / (1 - δ) ≥ T + δ * P / (1 - δ) ↔ 1 / (1 - δ) ≥ (T - P) / (R - P) := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < R - P := by linarith
  rw [ge_iff_le, ge_iff_le, div_le_div_iff₀ h2 h1]
  rw [show T + δ * P / (1 - δ) = (T * (1 - δ) + δ * P) / (1 - δ) by field_simp]
  rw [div_le_div_iff_of_pos_right h1]
  constructor <;> intro h <;> nlinarith

theorem bigger_prize_needs_longer_horizon (R P N : ℝ) (hRP : P < R) :
    ∃ T, R < T ∧ (T - P) / (R - P) > N := by
  have h2 : 0 < R - P := by linarith
  refine ⟨max (R + 1) (P + (|N| + 1) * (R - P)), lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  rw [gt_iff_lt, lt_div_iff₀ h2]
  have hm := le_max_right (R + 1) (P + (|N| + 1) * (R - P))
  have hN := le_abs_self N
  nlinarith

/-! ## The payoffs -/

theorem shared_weight_dominance (T R P S α : ℝ) (hTR : R < T) (hRS : S < R) (hTP : P < T) :
    ((1 + α) * R ≥ T + α * S ↔ α ≥ (T - R) / (R - S)) ∧
      (S + α * T ≥ (1 + α) * P ↔ α ≥ (P - S) / (T - P)) := by
  have h1 : 0 < R - S := by linarith
  have h2 : 0 < T - P := by linarith
  constructor
  · rw [ge_iff_le, ge_iff_le, div_le_iff₀ h1]
    constructor <;> intro h <;> nlinarith
  · rw [ge_iff_le, ge_iff_le, div_le_iff₀ h2]
    constructor <;> intro h <;> nlinarith

theorem combined_threshold (T R P S α δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hTP : (1 + α) * P < T + α * S) :
    (1 + α) * R / (1 - δ) ≥ (T + α * S) + δ * ((1 + α) * P) / (1 - δ) ↔
      δ ≥ ((T + α * S) - (1 + α) * R) / ((T + α * S) - (1 + α) * P) := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < (T + α * S) - (1 + α) * P := by linarith
  rw [ge_iff_le, ge_iff_le, div_le_iff₀ h2]
  rw [show (T + α * S) + δ * ((1 + α) * P) / (1 - δ) =
      ((T + α * S) * (1 - δ) + δ * ((1 + α) * P)) / (1 - δ) by field_simp]
  rw [div_le_div_iff_of_pos_right h1]
  constructor <;> intro h <;> nlinarith

theorem best_deviation_threshold (T' R' M δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hTM : M < T') :
    R' / (1 - δ) ≥ T' + δ * M / (1 - δ) ↔ δ ≥ (T' - R') / (T' - M) := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < T' - M := by linarith
  rw [ge_iff_le, ge_iff_le, div_le_iff₀ h2]
  rw [show T' + δ * M / (1 - δ) = (T' * (1 - δ) + δ * M) / (1 - δ) by field_simp]
  rw [div_le_div_iff_of_pos_right h1]
  constructor <;> intro h <;> nlinarith

theorem example_numbers :
    ((5 : ℝ) + 0 * 0 - (1 + 0) * 3) / ((5 + 0 * 0) - (1 + 0) * 1) = 1 / 2 ∧
      max ((1 + 1 / 2 : ℝ) * 1) (0 + (1 / 2) * 5) = 5 / 2 ∧
      ((5 : ℝ) + (1 / 2) * 0 - (1 + 1 / 2) * 3) / ((5 + (1 / 2) * 0) - 5 / 2) = 1 / 5 ∧
      ((5 : ℝ) + (1 / 2) * 0 - (1 + 1 / 2) * 3) / ((5 + (1 / 2) * 0) - (1 + 1 / 2) * 1) = 1 / 7 ∧
      (1 + (2 / 3 : ℝ)) * 3 = 5 + (2 / 3) * 0 := by
  norm_num

end ImaginedVsReal

#print axioms ImaginedVsReal.posterior_odds
#print axioms ImaginedVsReal.any_posterior_reachable
#print axioms ImaginedVsReal.horizon_bound
#print axioms ImaginedVsReal.bigger_prize_needs_longer_horizon
#print axioms ImaginedVsReal.shared_weight_dominance
#print axioms ImaginedVsReal.combined_threshold
#print axioms ImaginedVsReal.best_deviation_threshold
#print axioms ImaginedVsReal.example_numbers
