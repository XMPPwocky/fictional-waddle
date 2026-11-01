import Mathlib

/-!
# Trusting your future self: reflection, Brier score and quadratic variation

A finite probability space `Ω` with weights `μ` (summing to 1). `X : Ω → ℝ` is what you will eventually learn
(for an event, 0 or 1); `Q : Ω → ℝ` is your credence at a later time. Your future self is calibrated by your present
lights when, on every set where `Q` takes the value `q`, the average of `X` is `q`:
`Σ_{Q = q} μ (X − Q) = 0` for every `q`.

PROVED:
* `cross_zero`: then `Σ μ (X − Q) g(Q) = 0` for every function `g`.
* `reflection`: your present expectation of `X` equals your present expectation of your future credence.
* `pythagoras`: for any present credence `p`, `E[(X − p)²] = E[(Q − p)²] + E[(X − Q)²]`. The expected Brier score of
  the whole journey is the sum of the expected squared steps: squared steps add, as quadratic variation does for a
  martingale.
* `brier_gap`: reporting `r` instead of `m = E[Q]` costs exactly `(r − m)²` in expected Brier score.
* `move_is_free_improvement`: if you expect your credence to move away from `r`, then `r` is strictly beaten by
  where you expect it to move.
-/

namespace Reflection
open Finset

variable {Ω : Type*} [Fintype Ω] (μ X Q : Ω → ℝ)

def Calibrated : Prop := ∀ q : ℝ, ∑ ω ∈ univ.filter (fun ω => Q ω = q), μ ω * (X ω - Q ω) = 0

theorem cross_zero (h : Calibrated μ X Q) (g : ℝ → ℝ) : ∑ ω, μ ω * (X ω - Q ω) * g (Q ω) = 0 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ.image Q) (g := Q)
    (fun ω _ => Finset.mem_image_of_mem Q (Finset.mem_univ ω))]
  refine Finset.sum_eq_zero (fun q _ => ?_)
  have hq : ∑ ω ∈ univ.filter (fun ω => Q ω = q), μ ω * (X ω - Q ω) * g (Q ω) =
      (∑ ω ∈ univ.filter (fun ω => Q ω = q), μ ω * (X ω - Q ω)) * g q := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun ω hω => by rw [(Finset.mem_filter.mp hω).2])
  rw [hq, h q, zero_mul]

theorem reflection (h : Calibrated μ X Q) : ∑ ω, μ ω * X ω = ∑ ω, μ ω * Q ω := by
  have := cross_zero μ X Q h (fun _ => 1)
  simp only [mul_one, mul_sub, Finset.sum_sub_distrib] at this
  linarith

theorem pythagoras (h : Calibrated μ X Q) (p : ℝ) :
    ∑ ω, μ ω * (X ω - p) ^ 2 = ∑ ω, μ ω * (Q ω - p) ^ 2 + ∑ ω, μ ω * (X ω - Q ω) ^ 2 := by
  have hc := cross_zero μ X Q h (fun q => q - p)
  have e : ∀ ω, μ ω * (X ω - p) ^ 2 =
      μ ω * (Q ω - p) ^ 2 + μ ω * (X ω - Q ω) ^ 2 + 2 * (μ ω * (X ω - Q ω) * (Q ω - p)) := fun ω => by ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hc, mul_zero, add_zero]

theorem brier_gap (hμ : ∑ ω, μ ω = 1) (h : Calibrated μ X Q) (r : ℝ) :
    let m := ∑ ω, μ ω * Q ω
    ∑ ω, μ ω * (X ω - r) ^ 2 = ∑ ω, μ ω * (X ω - m) ^ 2 + (r - m) ^ 2 := by
  intro m
  have hX : ∑ ω, μ ω * X ω = m := reflection μ X Q h
  have e : ∀ ω, μ ω * (X ω - r) ^ 2 =
      μ ω * (X ω - m) ^ 2 + 2 * (m - r) * (μ ω * X ω) - 2 * (m - r) * m * μ ω + (r - m) ^ 2 * μ ω := fun ω => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hX, hμ]
  ring

theorem move_is_free_improvement (hμ : ∑ ω, μ ω = 1) (h : Calibrated μ X Q) (r : ℝ)
    (hr : r ≠ ∑ ω, μ ω * Q ω) :
    ∑ ω, μ ω * (X ω - ∑ ω', μ ω' * Q ω') ^ 2 < ∑ ω, μ ω * (X ω - r) ^ 2 := by
  have := brier_gap μ X Q hμ h r
  simp only at this
  rw [this]
  have : 0 < (r - ∑ ω, μ ω * Q ω) ^ 2 := by positivity [sub_ne_zero.mpr hr]
  linarith

end Reflection
