import Mathlib

/-!
# A leaky self-prediction makes the world seem to follow you

Sensation is `s = a + w`: the consequence of your own action `a` plus an independent world signal `w`. The brain
subtracts a prediction `g·a` made from a copy of the motor command (efference copy, gain `g`) and treats the
residual `r = s − g·a` as "the world". Expectations are weighted averages over a finite set of trials.

PROVED:
* `residual_eq`: the residual is `(1 − g)·a + w`.
* `residual_cov_action`: if your actions are centred and uncorrelated with the world, the covariance between
  "the world" (the residual) and your own actions is exactly `(1 − g)·Var(a)`.
* `world_follows_you_iff`: so the world appears correlated with what you do iff the self-prediction is miscalibrated
  (`g ≠ 1`) and you act at all (`Var(a) ≠ 0`).
* `perfect_copy_no_correlation`: with a perfect copy (`g = 1`), the residual is the world alone and carries no trace of
  your actions.
INTERPRETED (not formalized): `g < 1` lets your own actions leak into what feels external (a self-tickle that works,
actions that feel done to you), and the same leak makes the world seem to track you. This is one parameter giving both
directions of a self/world boundary error; it is a toy model, not a theory of any condition.
-/

namespace LeakyEfference
open Finset

variable {Ω : Type*} [Fintype Ω] (μ a w : Ω → ℝ) (g : ℝ)

def resid (ω : Ω) : ℝ := (a ω + w ω) - g * a ω

theorem residual_eq (ω : Ω) : resid a w g ω = (1 - g) * a ω + w ω := by unfold resid; ring

theorem residual_cov_action (ha : ∑ ω, μ ω * a ω = 0) (haw : ∑ ω, μ ω * a ω * w ω = 0) :
    ∑ ω, μ ω * resid a w g ω * a ω = (1 - g) * ∑ ω, μ ω * a ω ^ 2 := by
  have e : ∀ ω, μ ω * resid a w g ω * a ω = (1 - g) * (μ ω * a ω ^ 2) + μ ω * a ω * w ω := by
    intro ω; rw [residual_eq]; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, haw, add_zero]

theorem world_follows_you_iff (ha : ∑ ω, μ ω * a ω = 0) (haw : ∑ ω, μ ω * a ω * w ω = 0) :
    ∑ ω, μ ω * resid a w g ω * a ω ≠ 0 ↔ g ≠ 1 ∧ ∑ ω, μ ω * a ω ^ 2 ≠ 0 := by
  rw [residual_cov_action μ a w g ha haw, mul_ne_zero_iff, sub_ne_zero, ne_comm]

theorem perfect_copy_no_correlation (ω : Ω) : resid a w 1 ω = w ω := by
  rw [residual_eq]; ring

end LeakyEfference
