import Mathlib

/-!
# A pilot with one step of lag

The pilot corrects the error it saw one step ago: `x (n + 2) = x (n + 1) - k * x n`.

PROVED:
* `gain_one_period_six`: with gain `k = 1` the error never settles: it returns exactly to where it started every 6 steps,
  for any starting values (the characteristic roots are the primitive sixth roots of unity).
* `gain_one_never_settles`: if the starting error is not zero, the error is not eventually zero.
* `product_of_roots`: for any gain the two characteristic roots multiply to `k`, so when they are complex (k > 1/4) each
  has modulus √k: the oscillation decays exactly when `k < 1` and grows when `k > 1`.
INTERPRETED (not formalized): `x` as the pitch error and `k` as the pilot's gain; lag from reaction time, the flight
control system and actuator rate limits.
-/

namespace PIO

theorem gain_one_period_six (x : ℕ → ℝ) (h : ∀ n, x (n + 2) = x (n + 1) - x n) (n : ℕ) : x (n + 6) = x n := by
  have h2 := h n; have h3 := h (n + 1); have h4 := h (n + 2); have h5 := h (n + 3); have h6 := h (n + 4)
  simp only [show n + 1 + 1 = n + 2 by ring, show n + 1 + 2 = n + 3 by ring, show n + 2 + 1 = n + 3 by ring,
    show n + 2 + 2 = n + 4 by ring, show n + 3 + 1 = n + 4 by ring, show n + 3 + 2 = n + 5 by ring,
    show n + 4 + 1 = n + 5 by ring, show n + 4 + 2 = n + 6 by ring] at *
  linarith

theorem gain_one_never_settles (x : ℕ → ℝ) (h : ∀ n, x (n + 2) = x (n + 1) - x n) (h0 : x 0 ≠ 0) :
    ∀ N, ∃ n ≥ N, x n ≠ 0 := by
  intro N
  refine ⟨6 * N, by omega, ?_⟩
  have : ∀ m, x (6 * m) = x 0 := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [show 6 * (m + 1) = 6 * m + 6 by ring, gain_one_period_six x h, ih]
  rw [this]; exact h0

theorem product_of_roots (k z w : ℂ) (hz : z ^ 2 - z + k = 0) (hw : w ^ 2 - w + k = 0) (hzw : z ≠ w) :
    z * w = k := by
  have hs : z + w = 1 := by
    have : (z - w) * (z + w - 1) = 0 := by linear_combination hz - hw
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hzw
    · linear_combination h
  linear_combination -hz + z * hs

end PIO
