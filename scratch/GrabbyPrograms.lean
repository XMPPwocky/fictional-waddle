import Mathlib

/-!
# Programs aren't grabby

A civilization acts at rate `r > 0` (actions per unit wall time) for wall time `T > 0`, with net payoff `g` per action.

* **Animal accounting** (per wall time): `F_wall = (r T g) / T = r g`.
* **Program accounting** (per own action): `F_prog = (r T g) / (r T) = g`.

Statements:
* G1 `wall_grabby_iff`: under animal accounting, going faster pays iff `g > 0`, and slower pays iff `g < 0` (dormancy).
* G2 `program_rate_neutral`: under program accounting, fitness does not depend on rate at all, provided the payoff per
  action does not depend on rate (the event world, where the sampling path is cut).
* G2' `program_neutral_iff`: if the per-action payoff is a function `g r` of rate, program fitness is rate-neutral iff
  that function is constant. Any residual pressure is exactly the rate-dependence of what an action yields.
* G3 `race_wall_speeds_up`: two civilizations race for a finite region `R`. Under animal accounting the captured share
  `r₁/(r₁+r₂)` strictly increases with own rate: an arms race.
* G4 `race_program_slows_down`: in the same race under program accounting, the yield per own action
  `R/(T(r₁+r₂))` strictly DEcreases with own rate. Speed is disfavoured, not merely neutral.
* G5 `few_samples_pass_more`: truncation selection on noisy per-action averages favours FEWER actions. With per-action
  payoff `g ± s` (fair coin) and a threshold at the maximum `g + s`, the pass probability `(1/2)^n` strictly decreases
  in the number of actions `n`. The residual selection pressure points toward slowness, never speed.

So under program accounting every rate pressure modelled here is zero or points toward slowness. The pressure behind
grabbiness exists only under wall-clock accounting with positive net payoff (G1, G3).
-/

namespace GrabbyPrograms

/-- **G1.** Animal accounting: for `r₁ < r₂`, the faster civilization has higher fitness iff `g > 0`. -/
theorem wall_grabby_iff (r₁ r₂ g : ℝ) (h : r₁ < r₂) : r₁ * g < r₂ * g ↔ 0 < g := by
  constructor
  · intro hg; nlinarith
  · intro hg; nlinarith

/-- **G1'.** Animal accounting with a costly life (`g < 0`): the slower civilization has higher fitness (dormancy). -/
theorem wall_dormancy (r₁ r₂ g : ℝ) (h : r₁ < r₂) (hg : g < 0) : r₂ * g < r₁ * g := by
  nlinarith

/-- **G2.** Program accounting with a rate-independent payoff per action: fitness `(r T g)/(r T)` equals `g` for every
rate. -/
theorem program_rate_neutral (r T g : ℝ) (hr : 0 < r) (hT : 0 < T) : (r * T * g) / (r * T) = g := by
  have : r * T ≠ 0 := by positivity
  field_simp

/-- **G2'.** If the payoff per action is a function `g` of rate, program fitness is rate-neutral iff `g` is constant. -/
theorem program_neutral_iff (g : ℝ → ℝ) :
    (∀ r₁ r₂ : ℝ, 0 < r₁ → 0 < r₂ → g r₁ = g r₂) ↔ ∃ c, ∀ r : ℝ, 0 < r → g r = c := by
  constructor
  · intro h; exact ⟨g 1, fun r hr => h r 1 hr one_pos⟩
  · rintro ⟨c, hc⟩ r₁ r₂ h1 h2; rw [hc r₁ h1, hc r₂ h2]

/-- **G3.** A race for a finite region under animal accounting: the captured share `r₁/(r₁+r₂)` strictly increases with
own rate. -/
theorem race_wall_speeds_up (r₁ r₁' r₂ : ℝ) (h1 : 0 < r₁) (h : r₁ < r₁') (h2 : 0 < r₂) :
    r₁ / (r₁ + r₂) < r₁' / (r₁' + r₂) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **G4.** The same race under program accounting: the yield per own action `R/(T(r₁+r₂))` strictly decreases with own
rate. -/
theorem race_program_slows_down (R T r₁ r₁' r₂ : ℝ) (hR : 0 < R) (hT : 0 < T) (h1 : 0 < r₁) (h : r₁ < r₁')
    (h2 : 0 < r₂) :
    R / (T * (r₁' + r₂)) < R / (T * (r₁ + r₂)) := by
  apply div_lt_div_of_pos_left hR (by positivity)
  nlinarith

/-- **G5.** Truncation selection at the top payoff favours fewer actions: the chance that all `n` actions come up `+`
(needed to average `g + s`) strictly decreases with `n`. -/
theorem few_samples_pass_more (n : ℕ) : ((1 : ℝ) / 2) ^ (n + 1) < ((1 : ℝ) / 2) ^ n := by
  rw [pow_succ]
  have : (0 : ℝ) < (1 / 2) ^ n := by positivity
  nlinarith

end GrabbyPrograms
