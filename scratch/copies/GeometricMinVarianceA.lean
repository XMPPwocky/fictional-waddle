import Mathlib

/-!
# Geometric run time: mean, variance, and the effect of running N copies

A run time `T ∈ {1, 2, ...}` with per-step success probability `r` has
`P(T = n) = r (1 - r)^(n - 1)` for `n ≥ 1` (encoded by `geomPmf r`).
Running `N` independent copies, each succeeding per step with probability `p`, gives
per-step success `rN p N = 1 - (1 - p)^N`.

All moment formulas below are derived from the series, not assumed.

PROVED
* `hasSum_geomPmf`: for `r ∈ (0,1]` the probabilities `geomPmf r n` sum to `1`.
* `hasSum_mean`: `∑ n · P(T = n) = 1 / r`.
* `hasSum_second_moment`: `∑ n² · P(T = n) = (2 - r) / r²`.
* `hasSum_variance`: `∑ (n - 1/r)² · P(T = n) = (1 - r) / r²`.
* `tsum_mean`, `tsum_variance`: the same identities stated with `tsum`.
* `rN_zero`: `rN p 0 = 0` (zero copies never succeed).
* `rN_mem`: for `p ∈ (0,1)` and `N ≥ 1`, `rN p N ∈ (0,1)`.
* `rN_strictMono`: `N ↦ rN p N` is strictly increasing.
* `mean_closed_strictAntiOn`: `N ↦ 1 / rN p N` is strictly decreasing on `N ≥ 1`.
* `variance_closed_strictAntiOn`: `N ↦ (1 - rN p N) / rN p N ^ 2` is strictly decreasing
  on `N ≥ 1`.
* `mean_series_strictAntiOn`, `variance_series_strictAntiOn`: the series-defined mean
  `∑' n, n · P(T = n)` and variance `∑' n, (n - mean)² · P(T = n)` of the run time with
  success `rN p N` are strictly decreasing on `N ≥ 1`.

INTERPRETED
* The domain of `N` is `N ≥ 1`: with `N = 0` copies the success probability is `0`, the run
  never terminates, and no geometric law exists; Lean's `1 / 0 = 0` would make the
  `N = 0` value meaningless, so it is excluded.
-/

namespace GeometricMinVarianceA

open Finset

/-- `P(T = n)` for a geometric run time on `{1, 2, ...}` with per-step success `r`. -/
noncomputable def geomPmf (r : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => r * (1 - r) ^ n

/-- Per-step success probability of `N` independent copies, each with success `p`. -/
noncomputable def rN (p : ℝ) (N : ℕ) : ℝ := 1 - (1 - p) ^ N

lemma norm_one_sub_lt {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) : ‖1 - r‖ < 1 := by
  rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith

/-- Shift a series over `n ≥ 1` with vanishing `0`-th term. -/
lemma hasSum_of_shift {f : ℕ → ℝ} {a : ℝ} (h0 : f 0 = 0)
    (h : HasSum (fun n => f (n + 1)) a) : HasSum f a := by
  have := (hasSum_nat_add_iff (f := f) 1 (g := a)).1 h
  simpa [h0] using this

theorem hasSum_geomPmf {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    HasSum (geomPmf r) 1 := by
  apply hasSum_of_shift rfl
  have hg := hasSum_geometric_of_norm_lt_one (norm_one_sub_lt h0 h1)
  have := hg.mul_left r
  convert this using 1
  · funext n; rfl
  · have : (1 : ℝ) - (1 - r) = r := by ring
    rw [this, mul_inv_cancel₀ h0.ne']

theorem hasSum_mean {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    HasSum (fun n : ℕ => (n : ℝ) * geomPmf r n) (1 / r) := by
  apply hasSum_of_shift (by simp [geomPmf])
  have hq := norm_one_sub_lt h0 h1
  have hg := hasSum_geometric_of_norm_lt_one hq
  have h1' := hasSum_coe_mul_geometric_of_norm_lt_one hq
  have := (h1'.add hg).mul_left r
  convert this using 1
  · funext n; simp only [geomPmf]; push_cast; ring
  · have : (1 : ℝ) - (1 - r) = r := by ring
    rw [this]; field_simp; ring

theorem hasSum_second_moment {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * geomPmf r n) ((2 - r) / r ^ 2) := by
  apply hasSum_of_shift (by simp [geomPmf])
  have hq := norm_one_sub_lt h0 h1
  have hg := hasSum_geometric_of_norm_lt_one hq
  have h1' := hasSum_coe_mul_geometric_of_norm_lt_one hq
  have h2' := hasSum_sq_mul_geometric_of_norm_lt_one hq
  have := ((h2'.add (h1'.mul_left 2)).add hg).mul_left r
  convert this using 1
  · funext n; simp only [geomPmf]; push_cast; ring
  · have : (1 : ℝ) - (1 - r) = r := by ring
    rw [this]; field_simp; ring

theorem hasSum_variance {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    HasSum (fun n : ℕ => ((n : ℝ) - 1 / r) ^ 2 * geomPmf r n) ((1 - r) / r ^ 2) := by
  have h2 := hasSum_second_moment h0 h1
  have hm := hasSum_mean h0 h1
  have hp := hasSum_geomPmf h0 h1
  have := (h2.sub (hm.mul_left (2 / r))).add (hp.mul_left ((1 / r) ^ 2))
  convert this using 1
  · funext n; ring
  · field_simp; ring

theorem tsum_mean {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    ∑' n : ℕ, (n : ℝ) * geomPmf r n = 1 / r :=
  (hasSum_mean h0 h1).tsum_eq

theorem tsum_variance {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    ∑' n : ℕ, ((n : ℝ) - ∑' m : ℕ, (m : ℝ) * geomPmf r m) ^ 2 * geomPmf r n
      = (1 - r) / r ^ 2 := by
  rw [tsum_mean h0 h1]; exact (hasSum_variance h0 h1).tsum_eq

theorem rN_zero (p : ℝ) : rN p 0 = 0 := by simp [rN]

theorem rN_mem {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {N : ℕ} (hN : 1 ≤ N) :
    0 < rN p N ∧ rN p N < 1 := by
  unfold rN
  have hq0 : 0 < 1 - p := by linarith
  have hq1 : 1 - p < 1 := by linarith
  constructor
  · have : (1 - p) ^ N < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
    linarith
  · have : 0 < (1 - p) ^ N := pow_pos hq0 N
    linarith

theorem rN_strictMono {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : StrictMono (rN p) := by
  intro a b hab
  unfold rN
  have : (1 - p) ^ b < (1 - p) ^ a :=
    pow_lt_pow_right_of_lt_one₀ (by linarith) (by linarith) hab
  linarith

lemma inv_strictAnti {r s : ℝ} (hr : 0 < r) (hrs : r < s) : 1 / s < 1 / r :=
  one_div_lt_one_div_of_lt hr hrs

lemma varFormula_strictAnti {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1) :
    (1 - s) / s ^ 2 < (1 - r) / r ^ 2 := by
  have hs : 0 < s := lt_trans hr hrs
  have hsq : r ^ 2 < s ^ 2 := by nlinarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hsq.le (by linarith : (0 : ℝ) ≤ 1 - s)]

theorem mean_closed_strictAntiOn {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictAntiOn (fun N => 1 / rN p N) (Set.Ici 1) := by
  intro a ha b _ hab
  exact inv_strictAnti (rN_mem hp0 hp1 ha).1 (rN_strictMono hp0 hp1 hab)

theorem variance_closed_strictAntiOn {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictAntiOn (fun N => (1 - rN p N) / rN p N ^ 2) (Set.Ici 1) := by
  intro a ha b hb hab
  exact varFormula_strictAnti (rN_mem hp0 hp1 ha).1 (rN_strictMono hp0 hp1 hab)
    (rN_mem hp0 hp1 hb).2.le

theorem mean_series_strictAntiOn {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictAntiOn (fun N => ∑' n : ℕ, (n : ℝ) * geomPmf (rN p N) n) (Set.Ici 1) := by
  intro a ha b hb hab
  have ha' := rN_mem hp0 hp1 ha
  have hb' := rN_mem hp0 hp1 hb
  simp only
  rw [tsum_mean ha'.1 ha'.2.le, tsum_mean hb'.1 hb'.2.le]
  exact mean_closed_strictAntiOn hp0 hp1 ha hb hab

theorem variance_series_strictAntiOn {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictAntiOn (fun N => ∑' n : ℕ,
      ((n : ℝ) - ∑' m : ℕ, (m : ℝ) * geomPmf (rN p N) m) ^ 2 * geomPmf (rN p N) n)
      (Set.Ici 1) := by
  intro a ha b hb hab
  have ha' := rN_mem hp0 hp1 ha
  have hb' := rN_mem hp0 hp1 hb
  simp only
  rw [tsum_variance ha'.1 ha'.2.le, tsum_variance hb'.1 hb'.2.le]
  exact variance_closed_strictAntiOn hp0 hp1 ha hb hab

end GeometricMinVarianceA
