import Mathlib

/-!
# "Do you halt here?": per-step selection, exponential vs hyperbolic discounting

A program faces one question per step: halt here, or continue. With a per-step halting probability `p`, surviving `t`
steps has probability `(1 - p)^t`.

* D1 `known_hazard_memoryless`: if `p` is known, the chance of surviving one more step is `1 - p` at every age:
  exponential discounting, time-consistent, memoryless.
* D2 `uniform_hazard_survival`: if the program does not know its own hazard (uniform prior on `p`), the survival curve is
  `∫₀¹ (1 - p)^t dp = 1/(t+1)`: hyperbolic discounting.
* D3 `rule_of_succession`, `lindy`: having survived `t` steps, the chance of surviving the next is `(t+1)/(t+2)`
  (Laplace's rule of succession), which strictly increases with age. Surviving is evidence of a low hazard: the Lindy
  effect.
-/

namespace HaltHere

/-- **D1.** Known hazard: the one-step continuation probability is `1 - p` whatever the age. -/
theorem known_hazard_memoryless (p : ℝ) (hp : p < 1) (t : ℕ) : (1 - p) ^ (t + 1) / (1 - p) ^ t = 1 - p := by
  have h : (1 - p) ^ t ≠ 0 := pow_ne_zero _ (by linarith)
  rw [pow_succ]; field_simp

/-- **D2.** Unknown hazard, uniform prior: the survival curve is hyperbolic. -/
theorem uniform_hazard_survival (t : ℕ) : ∫ p in (0 : ℝ)..1, (1 - p) ^ t = 1 / ((t : ℝ) + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ t) (1 : ℝ)]
  simp [integral_pow]

/-- **D3a.** Rule of succession: given survival to `t`, survival to `t + 1` has probability `(t+1)/(t+2)`. -/
theorem rule_of_succession (t : ℕ) :
    (1 / (((t + 1 : ℕ) : ℝ) + 1)) / (1 / ((t : ℝ) + 1)) = ((t : ℝ) + 1) / ((t : ℝ) + 2) := by
  push_cast
  have h1 : (t : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (t : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **D3b.** Lindy: that continuation probability strictly increases with age. -/
theorem lindy (t : ℕ) : ((t : ℝ) + 1) / ((t : ℝ) + 2) < ((t : ℝ) + 2) / ((t : ℝ) + 3) := by
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end HaltHere
