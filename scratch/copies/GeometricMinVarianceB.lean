import Mathlib

/-!
# Geometric run time: mean, variance, and monotonicity in the number of copies

A run time `T ∈ {1, 2, ...}` with per-step success probability `r ∈ (0,1]` has
`P(T = n + 1) = (1 - r)^n * r`. The moments are computed from the series.

PROVED
* `hasSum_pmf`: the geometric probabilities `(1-r)^n * r` sum to `1`.
* `hasSum_mean`: `∑ (n+1) * (1-r)^n * r = 1/r` (mean run time is `1/r`).
* `hasSum_second_moment`: `∑ (n+1)^2 * (1-r)^n * r = (2 - r)/r^2`.
* `hasSum_variance`: `∑ ((n+1) - 1/r)^2 * (1-r)^n * r = (1-r)/r^2`
  (variance about the mean, computed directly as a series).
* `variance_eq_second_moment_sub_sq`: `(2-r)/r^2 - (1/r)^2 = (1-r)/r^2`.
* `rN_pos`, `rN_le_one`, `rN_lt_one`: for `p ∈ (0,1)` and `N ≥ 1`,
  `r_N = 1 - (1-p)^N ∈ (0,1)`.
* `rN_strictMono`: `r_N` is strictly increasing in `N`.
* `mean_strictAntiOn`: `N ↦ 1/r_N` is strictly decreasing on `N ≥ 1`.
* `variance_strictAntiOn`: `N ↦ (1-r_N)/r_N^2` is strictly decreasing on `N ≥ 1`.
* `mean_strictAntiOn_series`, `variance_strictAntiOn_series`: the same statements
  with mean and variance given as the `tsum` of the series, not the closed forms.
* `variance_closed_strictAntiOn_r`: `r ↦ (1-r)/r^2` is strictly decreasing on `(0,1]`.

INTERPRETED
* The run time is indexed as `T = n + 1` with `n : ℕ`, and its law is the
  sequence `(1-r)^n * r`; no measure-theoretic random variable is constructed.
* `N` copies are monotone in `N` on `N ≥ 1` (`Set.Ici 1`); at `N = 0` one has
  `r_0 = 0` and no finite mean.
-/

namespace GeometricMinVarianceB

open Finset

/-- Geometric probability `P(T = n+1)`. -/
noncomputable def pmf (r : ℝ) (n : ℕ) : ℝ := (1 - r) ^ n * r

lemma norm_q_lt_one {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) : ‖1 - r‖ < 1 := by
  rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith

lemma hs0 {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    HasSum (fun n : ℕ => (1 - r) ^ n) (1 / r) := by
  have := hasSum_geometric_of_norm_lt_one (norm_q_lt_one h0 h1)
  simpa using this

lemma hs1 {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    HasSum (fun n : ℕ => (n : ℝ) * (1 - r) ^ n) ((1 - r) / r ^ 2) := by
  have := hasSum_coe_mul_geometric_of_norm_lt_one (norm_q_lt_one h0 h1)
  simpa using this

lemma hs2 {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * (1 - r) ^ n)
      ((1 - r) / r ^ 2 + 2 * (1 - r) ^ 2 / r ^ 3) := by
  have := hasSum_pow_mul_geometric_of_norm_lt_one 2 (norm_q_lt_one h0 h1)
  have e : (∑ j ∈ range (2 + 1),
      (Nat.stirlingSecond 2 j : ℝ) * j.factorial * (1 - r) ^ j / (1 - (1 - r)) ^ (j + 1))
      = (1 - r) / r ^ 2 + 2 * (1 - r) ^ 2 / r ^ 3 := by
    simp [Finset.sum_range_succ, Nat.stirlingSecond]
  rwa [e] at this

theorem hasSum_pmf {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    HasSum (fun n : ℕ => pmf r n) 1 := by
  have := (hs0 h0 h1).mul_right r
  unfold pmf
  convert this using 1
  field_simp

theorem hasSum_mean {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * pmf r n) (1 / r) := by
  have := ((hs1 h0 h1).add (hs0 h0 h1)).mul_right r
  unfold pmf
  convert this using 1
  · funext n; ring
  · field_simp; ring

theorem hasSum_second_moment {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * pmf r n) ((2 - r) / r ^ 2) := by
  have := (((hs2 h0 h1).add ((hs1 h0 h1).mul_left 2)).add (hs0 h0 h1)).mul_right r
  unfold pmf
  convert this using 1
  · funext n; ring
  · field_simp; ring

theorem hasSum_variance {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    HasSum (fun n : ℕ => (((n : ℝ) + 1) - 1 / r) ^ 2 * pmf r n) ((1 - r) / r ^ 2) := by
  have := ((hasSum_second_moment h0 h1).sub ((hasSum_mean h0 h1).mul_left (2 / r))).add
    ((hasSum_pmf h0 h1).mul_left (1 / r ^ 2))
  convert this using 1
  · funext n; ring
  · field_simp; ring

theorem variance_eq_second_moment_sub_sq {r : ℝ} (h0 : 0 < r) :
    (2 - r) / r ^ 2 - (1 / r) ^ 2 = (1 - r) / r ^ 2 := by
  field_simp; ring

/-- Per-step success of the fastest of `N` independent copies. -/
noncomputable def rN (p : ℝ) (N : ℕ) : ℝ := 1 - (1 - p) ^ N

theorem rN_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {N : ℕ} (hN : 1 ≤ N) : 0 < rN p N := by
  unfold rN
  have : (1 - p) ^ N < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  linarith

theorem rN_lt_one {p : ℝ} (hp1 : p < 1) (N : ℕ) : rN p N < 1 := by
  unfold rN
  have : 0 < (1 - p) ^ N := pow_pos (by linarith) N
  linarith

theorem rN_le_one {p : ℝ} (hp1 : p < 1) (N : ℕ) : rN p N ≤ 1 :=
  (rN_lt_one hp1 N).le

theorem rN_strictMono {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : StrictMono (rN p) := by
  intro a b hab
  unfold rN
  have : (1 - p) ^ b < (1 - p) ^ a := pow_lt_pow_right_of_lt_one₀ (by linarith) (by linarith) hab
  linarith

theorem variance_closed_strictAntiOn_r :
    StrictAntiOn (fun r : ℝ => (1 - r) / r ^ 2) (Set.Ioc 0 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  simp only
  have hsq : a ^ 2 < b ^ 2 := by nlinarith
  have hpa : 0 < a ^ 2 := by positivity
  have hpb : 0 < b ^ 2 := by positivity
  rw [div_lt_div_iff₀ hpb hpa]
  nlinarith [mul_le_mul_of_nonneg_left hsq.le (by linarith : (0 : ℝ) ≤ 1 - b)]

theorem mean_strictAntiOn {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictAntiOn (fun N : ℕ => 1 / rN p N) (Set.Ici 1) := by
  intro a ha b _ hab
  simp only
  exact one_div_lt_one_div_of_lt (rN_pos hp0 hp1 ha) (rN_strictMono hp0 hp1 hab)

theorem variance_strictAntiOn {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictAntiOn (fun N : ℕ => (1 - rN p N) / rN p N ^ 2) (Set.Ici 1) := by
  intro a ha b hb hab
  exact variance_closed_strictAntiOn_r
    ⟨rN_pos hp0 hp1 ha, rN_le_one hp1 a⟩ ⟨rN_pos hp0 hp1 hb, rN_le_one hp1 b⟩
    (rN_strictMono hp0 hp1 hab)

/-- Mean of the geometric run time, defined as a series. -/
noncomputable def mean (r : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) * pmf r n

/-- Variance of the geometric run time, defined as a series about the mean. -/
noncomputable def variance (r : ℝ) : ℝ := ∑' n : ℕ, (((n : ℝ) + 1) - mean r) ^ 2 * pmf r n

theorem mean_eq {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) : mean r = 1 / r :=
  (hasSum_mean h0 h1).tsum_eq

theorem variance_eq {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) : variance r = (1 - r) / r ^ 2 := by
  unfold variance
  rw [mean_eq h0 h1]
  exact (hasSum_variance h0 h1).tsum_eq

theorem mean_strictAntiOn_series {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictAntiOn (fun N : ℕ => mean (rN p N)) (Set.Ici 1) := by
  intro a ha b hb hab
  simp only
  rw [mean_eq (rN_pos hp0 hp1 ha) (rN_le_one hp1 a),
    mean_eq (rN_pos hp0 hp1 hb) (rN_le_one hp1 b)]
  exact mean_strictAntiOn hp0 hp1 ha hb hab

theorem variance_strictAntiOn_series {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictAntiOn (fun N : ℕ => variance (rN p N)) (Set.Ici 1) := by
  intro a ha b hb hab
  simp only
  rw [variance_eq (rN_pos hp0 hp1 ha) (rN_le_one hp1 a),
    variance_eq (rN_pos hp0 hp1 hb) (rN_le_one hp1 b)]
  exact variance_strictAntiOn hp0 hp1 ha hb hab

end GeometricMinVarianceB
