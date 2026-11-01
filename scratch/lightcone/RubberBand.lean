import Mathlib

/-!
# A rubber band around a light cone: the individual and the ensemble

A rubber band pinned at two events p (time 0) and q (time T) can only enclose what both cones allow: the causal
diamond, the future of p intersected with the past of q.

PROVED:
* `diamond_iff`, `diamond_width_le`: a point at time t and offset x lies in the diamond iff |x| ≤ min t (T - t), so the
  band is widest, T/2, at the middle.
* `bridge_product`: for diffusion, the forward message from p (variance t) times the backward message from q
  (variance T - t) is a Gaussian of variance t(T - t)/T. Two-sided conditioning multiplies the two cones' kernels.
* `bridge_variance_le`, `bridge_variance_mid`: that ensemble spread is at most T/4, reached exactly at t = T/2.
* `ring_average_zero`: the ensemble average of n ≥ 2 rays spread evenly round the band is the apex: the sum of the
  n-th roots of unity is 0. Each individual ray moves away at full speed; their average does not move at all.
INTERPRETED (not formalized): the individual as one path pinned at both ends, the ensemble as the band's profile.
-/

namespace RubberBand
open Real

theorem diamond_iff (t T x : ℝ) : (|x| ≤ t ∧ |x| ≤ T - t) ↔ |x| ≤ min t (T - t) := le_min_iff.symm

theorem diamond_width_le (t T : ℝ) : min t (T - t) ≤ T / 2 := by
  rcases le_total t (T - t) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

theorem bridge_product (x t T : ℝ) (ht : 0 < t) (htT : t < T) :
    exp (-x ^ 2 / (2 * t)) * exp (-x ^ 2 / (2 * (T - t))) = exp (-x ^ 2 / (2 * (t * (T - t) / T))) := by
  rw [← exp_add]; congr 1
  have h1 : 0 < T - t := by linarith
  have h2 : 0 < T := by linarith
  field_simp
  ring

theorem bridge_variance_le (t T : ℝ) (hT : 0 < T) : t * (T - t) / T ≤ T / 4 := by
  rw [div_le_div_iff₀ hT (by norm_num)]
  nlinarith [sq_nonneg (2 * t - T)]

theorem bridge_variance_mid (T : ℝ) (hT : 0 < T) : (T / 2) * (T - T / 2) / T = T / 4 := by
  field_simp; ring

theorem ring_average_zero (n : ℕ) (hn : 1 < n) :
    ∑ k ∈ Finset.range n, Complex.exp (2 * π * Complex.I / n) ^ k = 0 :=
  (Complex.isPrimitiveRoot_exp n (by omega)).geom_sum_eq_zero hn

end RubberBand
