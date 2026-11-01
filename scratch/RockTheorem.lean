import Mathlib

/-!
# The rock theorem

A blackmailer picks a threat intensity `t ≥ 0`, which costs `c * t` with `c > 0`. The victim's
response is `r t`, and the blackmailer's payoff is `g (r t) - c * t` for an arbitrary `g`.
If the victim's Jacobian with respect to the threat is zero everywhere, then every positive
threat is strictly worse for the blackmailer than not threatening.
-/

theorem rock_no_threat (r g : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (hr : Differentiable ℝ r)
    (hJ : ∀ t, deriv r t = 0) : ∀ t : ℝ, 0 < t → g (r t) - c * t < g (r 0) - c * 0 := by
  intro t ht
  have hconst : r t = r 0 := is_const_of_deriv_eq_zero hr hJ t 0
  rw [hconst]
  have : 0 < c * t := mul_pos hc ht
  linarith

/-- The fake rock: zero Jacobian at the origin only (a stationary point) does NOT protect you.
Here `r t = t ^ 2` has `deriv r 0 = 0`, yet a large enough threat buys a response that pays. -/
theorem fake_rock_exploitable :
    ∃ (r g : ℝ → ℝ) (c t : ℝ), 0 < c ∧ deriv r 0 = 0 ∧ 0 < t ∧ g (r t) - c * t > g (r 0) - c * 0 := by
  refine ⟨fun t => t ^ 2, id, 1, 2, one_pos, ?_, by norm_num, ?_⟩
  · simp
  · norm_num

#print axioms rock_no_threat
#print axioms fake_rock_exploitable
