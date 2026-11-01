import Mathlib

/-!
# Lookahead (extragradient) stabilizes the bilinear game

Game: `f(x, y) = x * y`, `x` minimizes, `y` maximizes. State `w = x + i y ∈ ℂ`.

PROVED
* `partial_x`, `partial_y`: `∂f/∂x = y`, `∂f/∂y = x`.
* `gda_eq`: simultaneous GDA `x' = x - η y, y' = y + η x` is `w' = (1 + iη) w`.
* `norm_gda`: `‖w'‖ = √(1 + η²) ‖w‖`.
* `norm_gda_gt`: for `η > 0` and `w ≠ 0`, `‖w‖ < ‖w'‖`.
* `gda_iter`, `norm_gda_iter`, `norm_gda_iter_rpow`:
  `w_k = (1 + iη)^k w_0` and `‖w_k‖ = (1 + η²)^(k/2) ‖w_0‖` (real power `k/2`).
* `eg_eq`: extragradient
  `x_h = x - η y, y_h = y + η x, x' = x - η y_h, y' = y + η x_h` is `w' = (1 - η² + iη) w`.
* `normSq_eg_factor`: `‖1 - η² + iη‖² = 1 - η² + η⁴`.
* `norm_eg_factor_lt_one`: for `0 < η < 1`, `‖1 - η² + iη‖ < 1`.
* `norm_eg`: `‖w'‖ = √(1 - η² + η⁴) ‖w‖`.
* `norm_eg_lt`: for `0 < η < 1` and `w ≠ 0`, `‖w'‖ < ‖w‖`.
* `eg_iter`, `norm_eg_iter`, `eg_tendsto_zero`: `w_k = (1 - η² + iη)^k w_0`,
  `‖w_k‖ = (1 - η² + η⁴)^(k/2) ‖w_0‖`, and `w_k → 0` for `0 < η < 1`.
* `gda_fixed_iff`, `eg_fixed_iff`: for `η > 0`, `w` is a fixed point iff `w = 0`.
* `isSaddle_iff`: `(x, y)` is a saddle point (Nash equilibrium) of `f`,
  i.e. `f x y' ≤ f x y ≤ f x' y` for all `x', y'`, iff `x = 0 ∧ y = 0`.
* `fixed_iff_nash`: for `η > 0`, fixed points of either map are exactly the Nash equilibrium.

INTERPRETED
* The maps are written coordinatewise from the stated update rules, with the gradient
  components `∂f/∂x = y`, `∂f/∂y = x` (verified in `partial_x`, `partial_y`).
* "After k steps" is `Nat.iterate`; `(1+η²)^(k/2)` is the real power `(1+η²)^((k:ℝ)/2)`.
* Nash equilibrium of the zero-sum game = saddle point of `f`.
-/

namespace LookaheadStabilizesB

open Complex Filter Topology

/-- The bilinear payoff. -/
def f (x y : ℝ) : ℝ := x * y

theorem partial_x (x y : ℝ) : deriv (fun x' => f x' y) x = y := by
  simp [f]

theorem partial_y (x y : ℝ) : deriv (fun y' => f x y') y = x := by
  simp [f]

/-- Simultaneous gradient descent–ascent on `f`, state `w = x + i y`. -/
def gda (η : ℝ) (w : ℂ) : ℂ :=
  ⟨w.re - η * w.im, w.im + η * w.re⟩

/-- Extragradient: look ahead one step, update with the gradient at the look-ahead point. -/
def eg (η : ℝ) (w : ℂ) : ℂ :=
  let xh := w.re - η * w.im
  let yh := w.im + η * w.re
  ⟨w.re - η * yh, w.im + η * xh⟩

theorem gda_eq (η : ℝ) (w : ℂ) : gda η w = (1 + η * I) * w := by
  apply Complex.ext <;> simp [gda]

theorem eg_eq (η : ℝ) (w : ℂ) : eg η w = (1 - (η : ℂ) ^ 2 + η * I) * w := by
  apply Complex.ext <;> simp [eg, pow_two] <;> ring

theorem normSq_gda_factor (η : ℝ) : ‖(1 + η * I : ℂ)‖ ^ 2 = 1 + η ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem norm_gda_factor (η : ℝ) : ‖(1 + η * I : ℂ)‖ = Real.sqrt (1 + η ^ 2) := by
  rw [← normSq_gda_factor, Real.sqrt_sq (norm_nonneg _)]

theorem norm_gda (η : ℝ) (w : ℂ) : ‖gda η w‖ = Real.sqrt (1 + η ^ 2) * ‖w‖ := by
  rw [gda_eq, norm_mul, norm_gda_factor]

theorem norm_gda_gt {η : ℝ} (hη : 0 < η) {w : ℂ} (hw : w ≠ 0) : ‖w‖ < ‖gda η w‖ := by
  rw [norm_gda]
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have h1 : 1 < Real.sqrt (1 + η ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  nlinarith

theorem gda_iter (η : ℝ) (k : ℕ) (w : ℂ) : (gda η)^[k] w = (1 + η * I) ^ k * w := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, gda_eq, pow_succ]; ring

theorem norm_gda_iter (η : ℝ) (k : ℕ) (w : ℂ) :
    ‖(gda η)^[k] w‖ = Real.sqrt (1 + η ^ 2) ^ k * ‖w‖ := by
  rw [gda_iter, norm_mul, norm_pow, norm_gda_factor]

theorem sqrt_pow_eq_rpow {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    Real.sqrt a ^ k = a ^ ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha]
  congr 1
  ring

theorem norm_gda_iter_rpow (η : ℝ) (k : ℕ) (w : ℂ) :
    ‖(gda η)^[k] w‖ = (1 + η ^ 2) ^ ((k : ℝ) / 2) * ‖w‖ := by
  rw [norm_gda_iter, sqrt_pow_eq_rpow (by positivity)]

theorem normSq_eg_factor (η : ℝ) :
    ‖(1 - (η : ℂ) ^ 2 + η * I : ℂ)‖ ^ 2 = 1 - η ^ 2 + η ^ 4 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [pow_two]
  ring

theorem norm_eg_factor_lt_one {η : ℝ} (h0 : 0 < η) (h1 : η < 1) :
    ‖(1 - (η : ℂ) ^ 2 + η * I : ℂ)‖ < 1 := by
  have hsq : ‖(1 - (η : ℂ) ^ 2 + η * I : ℂ)‖ ^ 2 < 1 ^ 2 := by
    rw [normSq_eg_factor]
    have : η ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg η, pow_pos h0 2]
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

theorem norm_eg (η : ℝ) (w : ℂ) :
    ‖eg η w‖ = Real.sqrt (1 - η ^ 2 + η ^ 4) * ‖w‖ := by
  rw [eg_eq, norm_mul, ← normSq_eg_factor, Real.sqrt_sq (norm_nonneg _)]

theorem norm_eg_lt {η : ℝ} (h0 : 0 < η) (h1 : η < 1) {w : ℂ} (hw : w ≠ 0) :
    ‖eg η w‖ < ‖w‖ := by
  rw [eg_eq, norm_mul]
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have := norm_eg_factor_lt_one h0 h1
  nlinarith

theorem eg_iter (η : ℝ) (k : ℕ) (w : ℂ) :
    (eg η)^[k] w = (1 - (η : ℂ) ^ 2 + η * I) ^ k * w := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, eg_eq, pow_succ]; ring

theorem norm_eg_iter (η : ℝ) (k : ℕ) (w : ℂ) :
    ‖(eg η)^[k] w‖ = (1 - η ^ 2 + η ^ 4) ^ ((k : ℝ) / 2) * ‖w‖ := by
  have hnn : 0 ≤ 1 - η ^ 2 + η ^ 4 := by
    rw [← normSq_eg_factor]; positivity
  rw [eg_iter, norm_mul, norm_pow, ← sqrt_pow_eq_rpow hnn, ← normSq_eg_factor,
    Real.sqrt_sq (norm_nonneg _)]

theorem eg_tendsto_zero {η : ℝ} (h0 : 0 < η) (h1 : η < 1) (w : ℂ) :
    Tendsto (fun k : ℕ => (eg η)^[k] w) atTop (𝓝 0) := by
  simp_rw [eg_iter]
  have h := tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_eg_factor_lt_one h0 h1)
  simpa using h.mul_const w

theorem gda_fixed_iff {η : ℝ} (hη : 0 < η) (w : ℂ) : gda η w = w ↔ w = 0 := by
  constructor
  · intro h
    rw [gda_eq] at h
    have h' : (η * I) * w = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exfalso
      rcases mul_eq_zero.mp h'' with h3 | h3
      · exact hη.ne' (by exact_mod_cast h3)
      · exact I_ne_zero h3
    · exact h''
  · rintro rfl; simp [gda]; rfl

theorem eg_fixed_iff {η : ℝ} (hη : 0 < η) (w : ℂ) : eg η w = w ↔ w = 0 := by
  constructor
  · intro h
    rw [eg_eq] at h
    have h' : (-(η : ℂ) ^ 2 + η * I) * w = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exfalso
      have him := congrArg Complex.im h''
      simp [pow_two] at him
      exact hη.ne' him
    · exact h''
  · rintro rfl; simp [eg]; rfl

/-- Saddle point (Nash equilibrium) of the zero-sum game: `x` minimizes, `y` maximizes. -/
def IsSaddle (x y : ℝ) : Prop :=
  (∀ y', f x y' ≤ f x y) ∧ (∀ x', f x y ≤ f x' y)

theorem isSaddle_iff (x y : ℝ) : IsSaddle x y ↔ x = 0 ∧ y = 0 := by
  constructor
  · rintro ⟨hy, hx⟩
    simp only [f] at hy hx
    have hx0 : x = 0 := by
      by_contra hne
      have h1 := hy (y + 1 / x)
      have : x * (y + 1 / x) = x * y + 1 := by field_simp
      linarith
    subst hx0
    have hy0 : y = 0 := by
      by_contra hne
      have h1 := hx (-1 / y)
      have : -1 / y * y = -1 := by field_simp
      simp at h1
      linarith
    exact ⟨rfl, hy0⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨fun _ => by simp [f], fun _ => by simp [f]⟩

theorem fixed_iff_nash {η : ℝ} (hη : 0 < η) (w : ℂ) :
    (gda η w = w ↔ IsSaddle w.re w.im) ∧ (eg η w = w ↔ IsSaddle w.re w.im) := by
  have hz : w = 0 ↔ IsSaddle w.re w.im := by
    rw [isSaddle_iff]
    constructor
    · rintro rfl; simp
    · rintro ⟨h1, h2⟩; exact Complex.ext h1 h2
  exact ⟨(gda_fixed_iff hη w).trans hz, (eg_fixed_iff hη w).trans hz⟩

end LookaheadStabilizesB
