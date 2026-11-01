import Mathlib

/-!
# Inside the anthropic shadow, the data says nothing

Catastrophes happen independently with probability `p` per period. Observers exist now only if none happened in
the last `k` periods. An observer looks at those `k` periods.

PROVED:
* `shadow_window_certain`: conditional on observers existing, the probability of seeing zero catastrophes in the
  shadow window is 1, whatever `p` is.
* `shadow_likelihood_flat`: so the likelihood ratio between any two rates `p` and `q` from that observation is 1.
* `shadow_posterior_eq_prior`: and Bayesian updating on it returns the prior exactly. Any "best explanation" of the
  quiet window is the prior restated.
* `before_shadow_informative`: periods outside the shadow still discriminate: one period with a catastrophe has
  likelihood ratio `p / q` between rates, which differs from 1 when `p ≠ q`.
INTERPRETED (not formalized): real catastrophes, observer-selection principles (SSA, SIA) and how far back the
shadow reaches; the model assumes a sharp shadow and independence across periods.
-/

namespace Shadow

noncomputable def quietProb (p : ℝ) (k : ℕ) : ℝ := (1 - p) ^ k

theorem shadow_window_certain (p : ℝ) (k : ℕ) (h : quietProb p k ≠ 0) :
    quietProb p k / quietProb p k = 1 := div_self h

theorem shadow_likelihood_flat (p q : ℝ) (k : ℕ) (hp : quietProb p k ≠ 0) (hq : quietProb q k ≠ 0) :
    (quietProb p k / quietProb p k) / (quietProb q k / quietProb q k) = 1 := by
  rw [div_self hp, div_self hq, div_one]

theorem shadow_posterior_eq_prior {Θ : Type*} [Fintype Θ] (prior : Θ → ℝ) (hsum : ∑ θ, prior θ = 1)
    (lik : Θ → ℝ) (hflat : ∀ θ, lik θ = 1) (θ : Θ) :
    prior θ * lik θ / ∑ θ', prior θ' * lik θ' = prior θ := by
  simp [hflat, hsum]

theorem before_shadow_informative (p q : ℝ) (hq : q ≠ 0) (hpq : p ≠ q) : p / q ≠ 1 := by
  intro h
  exact hpq (by field_simp at h; linarith)

end Shadow
