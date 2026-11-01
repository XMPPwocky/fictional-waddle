import Mathlib

/-!
# PrecisionDialB

Weighted combination of a prior guess and an observation of a quantity θ.
The prior error has variance `vp = σp² > 0`, the observation error has variance
`vx = σx² > 0`, the errors are independent, and the estimate is
`w · observation + (1 − w) · prior` with `w ∈ ℝ`.

The mean squared error is taken as the definition
`L vp vx w = w² · vx + (1 − w)² · vp`, and the optimal weight is
`wstar vp vx = vp / (vp + vx)`.

PROVED
* `mse_finite_model`: in a finite model (prior error `a` on a finite index type with
  weights `p`, observation error `b` on a finite index type with weights `q`, the joint
  law being the product weighting, so the errors are independent; weights summing to 1;
  both errors of zero mean), the mean squared error of the weighted estimate equals
  `L vp vx w` with `vp = ∑ p a²`, `vx = ∑ q b²`. Nonnegativity of the weights is not needed.
* (1) `wstar_minimizes`: `L (wstar) ≤ L w` for all `w`;
  `L_eq_min_iff`: `L w = L wstar ↔ w = wstar`;
  `wstar_unique_min`: `w ≠ wstar → L wstar < L w`;
  `isMinOn_wstar`: `IsMinOn (L vp vx) univ (wstar vp vx)`.
* (2) `excess_loss`: `L w − L wstar = (w − wstar)² · (vp + vx)`.
  `excess_symm`: overshooting and undershooting by the same `d` cost the same,
  `L (wstar + d) − L wstar = L (wstar − d) − L wstar = d² · (vp + vx)`.
* (3) `min_value`: `L wstar = vp · vx / (vp + vx)`;
  `min_lt_prior`: `L wstar < vp`; `min_lt_obs`: `L wstar < vx`.
* (4) `wstar_strictMonoOn_prior`: for fixed `vx > 0`, `vp ↦ wstar vp vx` is strictly
  increasing on `(0, ∞)`; `wstar_strictAntiOn_obs`: for fixed `vp > 0`,
  `vx ↦ wstar vp vx` is strictly decreasing on `(0, ∞)`.
  Also `wstar_mem_Ioo`: `0 < wstar < 1`.

INTERPRETED (not formal content)
* `w > wstar` overweights the data: observation noise is read as structure.
* `w < wstar` overweights the prior: evidence is ignored.
* Calibration is choosing `w = wstar`; by `excess_loss` both directions of
  miscalibration cost exactly quadratically, with curvature `vp + vx`.
* Variances are taken as the primitive parameters `vp = σp²`, `vx = σx²`; monotonicity
  in (4) is monotonicity in these variances.
-/

namespace PrecisionDialB

open Finset

/-- Mean squared error of the weighted estimate (definition). -/
def L (vp vx w : ℝ) : ℝ := w ^ 2 * vx + (1 - w) ^ 2 * vp

/-- The precision-weighted optimal data weight. -/
noncomputable def wstar (vp vx : ℝ) : ℝ := vp / (vp + vx)

/-- Finite model: θ is the true value, the prior guess is `θ + a i`, the observation is
`θ + b j`, and `(i, j)` has joint weight `p i * q j` (independence). The mean squared error
of `w · observation + (1 − w) · prior` equals `L` with the two error variances. -/
theorem mse_finite_model {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (q : κ → ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1)
    (ha : ∑ i, p i * a i = 0) (hb : ∑ j, q j * b j = 0) (θ w : ℝ) :
    ∑ i, ∑ j, p i * q j * (w * (θ + b j) + (1 - w) * (θ + a i) - θ) ^ 2
      = L (∑ i, p i * a i ^ 2) (∑ j, q j * b j ^ 2) w := by
  have key : ∀ i j, p i * q j * (w * (θ + b j) + (1 - w) * (θ + a i) - θ) ^ 2
      = w ^ 2 * (p i * (q j * b j ^ 2)) + (1 - w) ^ 2 * (q j * (p i * a i ^ 2))
        + 2 * w * (1 - w) * ((p i * a i) * (q j * b j)) := by
    intro i j; ring
  simp_rw [key, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    ← Finset.mul_sum, hp, hq, ha, hb]
  unfold L
  ring

/-- (2) Exact quadratic excess loss. -/
theorem excess_loss {vp vx : ℝ} (hp : 0 < vp) (hx : 0 < vx) (w : ℝ) :
    L vp vx w - L vp vx (wstar vp vx) = (w - wstar vp vx) ^ 2 * (vp + vx) := by
  have hs : vp + vx ≠ 0 := by positivity
  unfold L wstar
  field_simp
  ring

/-- (2) Over- and under-weighting by the same amount cost the same. -/
theorem excess_symm {vp vx : ℝ} (hp : 0 < vp) (hx : 0 < vx) (d : ℝ) :
    L vp vx (wstar vp vx + d) - L vp vx (wstar vp vx) = d ^ 2 * (vp + vx) ∧
    L vp vx (wstar vp vx - d) - L vp vx (wstar vp vx) = d ^ 2 * (vp + vx) := by
  constructor
  · rw [excess_loss hp hx]; ring
  · rw [excess_loss hp hx]; ring

/-- (1) `wstar` is a minimizer. -/
theorem wstar_minimizes {vp vx : ℝ} (hp : 0 < vp) (hx : 0 < vx) (w : ℝ) :
    L vp vx (wstar vp vx) ≤ L vp vx w := by
  have h := excess_loss hp hx w
  have : 0 ≤ (w - wstar vp vx) ^ 2 * (vp + vx) := by positivity
  linarith

theorem isMinOn_wstar {vp vx : ℝ} (hp : 0 < vp) (hx : 0 < vx) :
    IsMinOn (L vp vx) Set.univ (wstar vp vx) :=
  fun w _ => wstar_minimizes hp hx w

/-- (1) Uniqueness of the minimizer. -/
theorem L_eq_min_iff {vp vx : ℝ} (hp : 0 < vp) (hx : 0 < vx) (w : ℝ) :
    L vp vx w = L vp vx (wstar vp vx) ↔ w = wstar vp vx := by
  have h := excess_loss hp hx w
  have hs : 0 < vp + vx := by positivity
  constructor
  · intro he
    have h0 : (w - wstar vp vx) ^ 2 * (vp + vx) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
    · exact absurd h1 hs.ne'
  · intro he; rw [he]

theorem wstar_unique_min {vp vx : ℝ} (hp : 0 < vp) (hx : 0 < vx) {w : ℝ}
    (hw : w ≠ wstar vp vx) : L vp vx (wstar vp vx) < L vp vx w := by
  have h := excess_loss hp hx w
  have hd : w - wstar vp vx ≠ 0 := sub_ne_zero.mpr hw
  have : 0 < (w - wstar vp vx) ^ 2 * (vp + vx) := by positivity
  linarith

/-- (3) Minimum value. -/
theorem min_value {vp vx : ℝ} (hp : 0 < vp) (hx : 0 < vx) :
    L vp vx (wstar vp vx) = vp * vx / (vp + vx) := by
  have hs : vp + vx ≠ 0 := by positivity
  unfold L wstar
  field_simp
  ring

theorem min_lt_prior {vp vx : ℝ} (hp : 0 < vp) (hx : 0 < vx) :
    L vp vx (wstar vp vx) < vp := by
  rw [min_value hp hx, div_lt_iff₀ (by positivity)]
  nlinarith

theorem min_lt_obs {vp vx : ℝ} (hp : 0 < vp) (hx : 0 < vx) :
    L vp vx (wstar vp vx) < vx := by
  rw [min_value hp hx, div_lt_iff₀ (by positivity)]
  nlinarith

theorem wstar_mem_Ioo {vp vx : ℝ} (hp : 0 < vp) (hx : 0 < vx) :
    0 < wstar vp vx ∧ wstar vp vx < 1 := by
  unfold wstar
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by positivity)]
  linarith

/-- (4) `wstar` is strictly increasing in the prior error variance. -/
theorem wstar_strictMonoOn_prior {vx : ℝ} (hx : 0 < vx) :
    StrictMonoOn (fun vp => wstar vp vx) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  show a / (a + vx) < b / (b + vx)
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- (4) `wstar` is strictly decreasing in the observation error variance. -/
theorem wstar_strictAntiOn_obs {vp : ℝ} (hp : 0 < vp) :
    StrictAntiOn (fun vx => wstar vp vx) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  show vp / (vp + b) < vp / (vp + a)
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end PrecisionDialB
