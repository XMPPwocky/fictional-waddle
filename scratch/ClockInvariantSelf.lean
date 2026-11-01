import Mathlib

/-!
# A self-model that survives someone else's clock

Another agent simulates you with time step `Δ = T/n`. These are elementary; the content is which quantity must be
conserved.

* K1 `variance_rate_is_clock_free`: if each step adds variance `σ² Δ` (variance proportional to the step: Brownian
  scaling), the total over horizon `T` is `σ² T` for EVERY step count `n`.
* K2 `fixed_step_variance_is_clock_bound`: if each step adds a fixed variance `v > 0`, two clocks with `n₁ ≠ n₂` steps
  disagree about the total. The self-model depends on the simulator's clock.
* K3 `exponential_is_time_consistent`: `δ^(s+t) = δ^s · δ^t`. Evaluating now or later gives the same ranking.
* K4 `hyperbolic_reverses`: with `D(t) = 1/(1+t)`, reward 1 at `t` versus 1.5 at `t + 1`: at `t = 0` the earlier
  reward wins, at `t = 2` the later one wins. That's dynamic inconsistency, and HaltHere derived exactly this
  discount from an unknown hazard, i.e. an unknown clock.
-/

namespace ClockInvariantSelf

/-- **K1.** -/
theorem variance_rate_is_clock_free (σ2 T : ℝ) (n : ℕ) (hn : 0 < n) : (n : ℝ) * (σ2 * (T / n)) = σ2 * T := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- **K2.** -/
theorem fixed_step_variance_is_clock_bound (v : ℝ) (hv : 0 < v) (n₁ n₂ : ℕ) (h : n₁ ≠ n₂) :
    (n₁ : ℝ) * v ≠ (n₂ : ℝ) * v := by
  intro e
  exact h (by exact_mod_cast mul_right_cancel₀ hv.ne' e)

/-- **K3.** -/
theorem exponential_is_time_consistent (δ : ℝ) (s t : ℕ) : δ ^ (s + t) = δ ^ s * δ ^ t := by
  exact pow_add δ s t

/-- **K4.** -/
theorem hyperbolic_reverses :
    (1 : ℝ) / (1 + 0) > 3 / 2 * (1 / (1 + 1)) ∧ (1 : ℝ) / (1 + 2) < 3 / 2 * (1 / (1 + 3)) := by
  constructor <;> norm_num

end ClockInvariantSelf
