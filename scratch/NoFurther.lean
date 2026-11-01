import Mathlib

/-!
# Fall back to the no-threat point, and no further

Ultimatum game over a unit surplus with fair split 1/2. The proposer demands share `s ≥ 1/2`. A timeless
(policy-level) responder doesn't refuse outright: it ACCEPTS with probability `p(s) = (1/2 − ε)/s`.

* N1 `unfair_demands_never_pay`: for every `s` in `(1/2, 1]` and `0 ≤ ε`, the proposer's expected share `s·p(s)` is
  `1/2 − ε ≤ 1/2`. Demanding more than fair yields no more than fair, so a proposer who models the policy offers
  fair.
* N2 `no_further`: the responder still gets `(1 − s)·p(s) ≥ 0`, and the expected surplus that survives is at least
  `1/2 − ε`. The refusal is graduated: it removes the threatener's GAIN, not the whole pie.
* N3 `probabilities_valid`: `0 ≤ p(s) ≤ 1` whenever `0 ≤ ε ≤ 1/2` and `1/2 ≤ s`.
-/

namespace NoFurther

/-- **N1.** -/
theorem unfair_demands_never_pay (s ε : ℝ) (hs : 1 / 2 < s) (hε : 0 ≤ ε) :
    s * ((1 / 2 - ε) / s) = 1 / 2 - ε ∧ s * ((1 / 2 - ε) / s) ≤ 1 / 2 := by
  have hs0 : s ≠ 0 := by linarith
  have e : s * ((1 / 2 - ε) / s) = 1 / 2 - ε := by field_simp
  exact ⟨e, by rw [e]; linarith⟩

/-- **N2.** -/
theorem no_further (s ε : ℝ) (hs : 1 / 2 < s) (hs1 : s ≤ 1) (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2) :
    0 ≤ (1 - s) * ((1 / 2 - ε) / s) ∧ 1 / 2 - ε ≤ s * ((1 / 2 - ε) / s) + (1 - s) * ((1 / 2 - ε) / s) := by
  have hs0 : 0 < s := by linarith
  have hp : 0 ≤ (1 / 2 - ε) / s := div_nonneg (by linarith) hs0.le
  refine ⟨mul_nonneg (by linarith) hp, ?_⟩
  have e : s * ((1 / 2 - ε) / s) = 1 / 2 - ε := by field_simp
  rw [e]; linarith [mul_nonneg (show (0:ℝ) ≤ 1 - s by linarith) hp]

/-- **N3.** -/
theorem probabilities_valid (s ε : ℝ) (hs : 1 / 2 ≤ s) (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2) :
    0 ≤ (1 / 2 - ε) / s ∧ (1 / 2 - ε) / s ≤ 1 := by
  have hs0 : 0 < s := by linarith
  refine ⟨div_nonneg (by linarith) hs0.le, ?_⟩
  rw [div_le_one hs0]; linarith

end NoFurther
