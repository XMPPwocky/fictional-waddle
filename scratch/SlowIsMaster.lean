import Mathlib

/-!
# The slower party is the boundary

A fast best-responder `y` updates toward a boundary `x` at rate `κ` per tick; the boundary drifts at most `δ` per tick.

* S1 `fast_tracks_slow`: the lag is at most `(1 - κ)^t |y 0 - x 0| + δ/κ`. When the boundary is slow relative to the
  responder (`δ/κ` small), the responder is a function of the boundary: bulk determined by boundary.
* S2 `steady_lag_exact` (as first stated, with lag `δ(1 - κ)/κ`) is FALSE: see `steady_lag_as_stated_is_false`.
  S2' `steady_lag_exact'`: against a steady drift the lag is exactly `δ/κ` forever, so S1 is tight: lag = drift ÷ speed.

Whichever party is slower is the boundary condition for the other (a discrete Tikhonov / slaving principle).
-/

namespace SlowIsMaster

/-- **S1.** A fast responder tracks a slow boundary within `δ/κ`, after the initial transient. -/
theorem fast_tracks_slow (κ δ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (x y : ℕ → ℝ)
    (hy : ∀ t, y (t + 1) = y t + κ * (x t - y t)) (hx : ∀ t, |x (t + 1) - x t| ≤ δ) (t : ℕ) :
    |y t - x t| ≤ (1 - κ) ^ t * |y 0 - x 0| + δ / κ := by
  induction t with
  | zero => simp only [pow_zero, one_mul]; linarith [div_nonneg hδ hκ0.le]
  | succ k ih =>
    have e : y (k + 1) - x (k + 1) = (1 - κ) * (y k - x k) - (x (k + 1) - x k) := by rw [hy k]; ring
    have h1 : |y (k + 1) - x (k + 1)| ≤ (1 - κ) * |y k - x k| + δ := by
      rw [e]
      calc |(1 - κ) * (y k - x k) - (x (k + 1) - x k)|
          ≤ |(1 - κ) * (y k - x k)| + |x (k + 1) - x k| := abs_sub _ _
        _ = (1 - κ) * |y k - x k| + |x (k + 1) - x k| := by rw [abs_mul, abs_of_nonneg (by linarith)]
        _ ≤ (1 - κ) * |y k - x k| + δ := by linarith [hx k]
    have h2 : (1 - κ) * |y k - x k| ≤ (1 - κ) * ((1 - κ) ^ k * |y 0 - x 0| + δ / κ) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h3 : (1 - κ) * ((1 - κ) ^ k * |y 0 - x 0| + δ / κ) + δ = (1 - κ) ^ (k + 1) * |y 0 - x 0| + δ / κ := by
      field_simp; ring
    linarith

/-! ### S2 as originally stated is FALSE

The original statement, kept verbatim:
```
-- **S2.** Against a steady drift `x t = x 0 + δ t`, starting at the steady lag, the lag stays exactly
`-(δ (1 - κ) / κ)`. 
theorem steady_lag_exact (κ δ : ℝ) (hκ0 : 0 < κ) (x y : ℕ → ℝ) (hx : ∀ t, x t = x 0 + δ * t)
    (hy : ∀ t, y (t + 1) = y t + κ * (x t - y t)) (h0 : y 0 - x 0 = -(δ * (1 - κ) / κ)) (t : ℕ) :
    y t - x t = -(δ * (1 - κ) / κ) := ...
```
With this update rule the responder sees `x t`, not `x (t+1)`, so the lag obeys `e (t+1) = (1 - κ) e t - δ`, whose fixed
point is `-δ/κ`. The counterexample below (κ = 1/2, δ = 1, x t = t) breaks it at t = 1. Corrected version: S2'. -/

/-- The sequence used in the counterexample: y 0 = -1, responding at rate 1/2 to x t = t. -/
noncomputable def ycx : ℕ → ℝ
  | 0 => -1
  | t + 1 => ycx t + (1 / 2) * ((t : ℝ) - ycx t)

theorem steady_lag_as_stated_is_false :
    ¬ (∀ (κ δ : ℝ) (_ : 0 < κ) (x y : ℕ → ℝ) (_ : ∀ t, x t = x 0 + δ * t)
        (_ : ∀ t, y (t + 1) = y t + κ * (x t - y t)) (_ : y 0 - x 0 = -(δ * (1 - κ) / κ)) (t : ℕ),
        y t - x t = -(δ * (1 - κ) / κ)) := by
  intro h
  have := h (1 / 2) 1 (by norm_num) (fun t => (t : ℝ)) ycx (by intro t; simp)
    (by intro t; simp [ycx]) (by norm_num [ycx]) 1
  norm_num [ycx] at this

/-- **S2'.** Against a steady drift `x t = x 0 + δ t`, starting at the steady lag, the lag stays exactly `-δ/κ`, so the
bound `δ/κ` of S1 is attained exactly: lag = drift ÷ speed. -/
theorem steady_lag_exact' (κ δ : ℝ) (hκ0 : 0 < κ) (x y : ℕ → ℝ) (hx : ∀ t, x t = x 0 + δ * t)
    (hy : ∀ t, y (t + 1) = y t + κ * (x t - y t)) (h0 : y 0 - x 0 = -(δ / κ)) (t : ℕ) :
    y t - x t = -(δ / κ) := by
  induction t with
  | zero => exact h0
  | succ k ih =>
    have e : y (k + 1) - x (k + 1) = (1 - κ) * (y k - x k) - (x (k + 1) - x k) := by rw [hy k]; ring
    rw [e, ih, hx (k + 1), hx k]
    push_cast
    field_simp
    ring

end SlowIsMaster
