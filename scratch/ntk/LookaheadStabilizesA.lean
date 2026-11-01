import Mathlib

/-!
# Look-ahead stabilises gradient descent–ascent on the bilinear game

Game: `f(x, y) = x * y`, `x` minimises, `y` maximises. State `w = x + i y ∈ ℂ`.

PROVED
* `gda_eq`: simultaneous GDA `x' = x - η y, y' = y + η x` is `w' = (1 + iη) w`.
* `norm_gda`: `‖w'‖ = √(1 + η²) ‖w‖`; `norm_lt_norm_gda`: `‖w‖ < ‖w'‖` for `η > 0`, `w ≠ 0`.
* `norm_gda_iterate`: `‖w_k‖ = (1 + η²)^(k/2) ‖w_0‖` (real power `k/2`).
* `eg_eq`: extragradient is `w' = (1 - η² + iη) w`.
* `normSq_eg_coef`, `norm_sq_eg_coef`: `‖1 - η² + iη‖² = 1 - η² + η⁴`.
* `eg_coef_sq_lt_one`, `norm_eg_coef_lt_one`: this is `< 1` for `0 < η < 1`.
* `norm_eg_lt`: one extragradient step strictly contracts nonzero `w`.
* `eg_iterate_tendsto_zero`: `w_k → 0` for `0 < η < 1`.
* `gda_fixed_iff`, `eg_fixed_iff`: for `η > 0` the unique fixed point of each map is `w = 0`.
* `isSaddle_iff`: `(x, y)` is a Nash equilibrium (saddle point) of `f` iff `x = 0 ∧ y = 0`,
  i.e. iff `w = 0`.
* `hasDerivAt_f_x`, `hasDerivAt_f_y`: the partial derivatives of `f` are `∂ₓf = y`, `∂ᵧf = x`,
  so the maps below are exactly GDA and extragradient for `f`.

INTERPRETED
* "Spirals out" is read as `‖w'‖ > ‖w‖` for every `w ≠ 0` together with the closed form for `‖w_k‖`.
* "Contracts" is read as `‖w'‖ = ‖1 - η² + iη‖ ‖w‖` with `‖1 - η² + iη‖ < 1`.
* "Nash equilibrium" is read as a pure saddle point: `f(x, y') ≤ f(x, y) ≤ f(x', y)` for all `x', y'`.
-/

namespace LookaheadStabilizesA

open Complex Filter Topology

/-- The bilinear payoff. -/
def f (x y : ℝ) : ℝ := x * y

theorem hasDerivAt_f_x (x y : ℝ) : HasDerivAt (fun x => f x y) y x := by
  simpa [f] using (hasDerivAt_id x).mul_const y

theorem hasDerivAt_f_y (x y : ℝ) : HasDerivAt (fun y => f x y) x y := by
  simpa [f] using (hasDerivAt_id y).const_mul x

/-- Simultaneous gradient descent–ascent: `x' = x - η ∂ₓf`, `y' = y + η ∂ᵧf`. -/
def gda (η : ℝ) (w : ℂ) : ℂ := ⟨w.re - η * w.im, w.im + η * w.re⟩

/-- Extragradient: look ahead one GDA step, then update with the gradient at the look-ahead point. -/
def eg (η : ℝ) (w : ℂ) : ℂ :=
  let xh := w.re - η * w.im
  let yh := w.im + η * w.re
  ⟨w.re - η * yh, w.im + η * xh⟩

theorem gda_eq (η : ℝ) (w : ℂ) : gda η w = (1 + η * I) * w := by
  apply Complex.ext <;> simp [gda]

theorem norm_gda (η : ℝ) (w : ℂ) : ‖gda η w‖ = Real.sqrt (1 + η ^ 2) * ‖w‖ := by
  rw [gda_eq, norm_mul]
  congr 1
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply]
  ring

theorem norm_lt_norm_gda {η : ℝ} (hη : 0 < η) {w : ℂ} (hw : w ≠ 0) : ‖w‖ < ‖gda η w‖ := by
  rw [norm_gda]
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have : 1 < Real.sqrt (1 + η ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  nlinarith

theorem iterate_mul (c w : ℂ) (k : ℕ) : (fun z => c * z)^[k] w = c ^ k * w := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih]; ring

theorem gda_iterate (η : ℝ) (w : ℂ) (k : ℕ) : (gda η)^[k] w = (1 + η * I) ^ k * w := by
  have : gda η = fun z => (1 + η * I) * z := funext (gda_eq η)
  rw [this, iterate_mul]

theorem norm_gda_iterate (η : ℝ) (w : ℂ) (k : ℕ) :
    ‖(gda η)^[k] w‖ = (1 + η ^ 2) ^ ((k : ℝ) / 2) * ‖w‖ := by
  have h1 : ‖(1 : ℂ) + η * I‖ = Real.sqrt (1 + η ^ 2) := by
    have := norm_gda η 1
    rw [gda_eq, mul_one, norm_one, mul_one] at this
    exact this
  rw [gda_iterate, norm_mul, norm_pow, h1]
  congr 1
  have h0 : (0 : ℝ) ≤ 1 + η ^ 2 := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h0]
  congr 1
  ring

theorem eg_eq (η : ℝ) (w : ℂ) : eg η w = (1 - η ^ 2 + η * I) * w := by
  apply Complex.ext <;> simp [eg, pow_two] <;> ring

theorem normSq_eg_coef (η : ℝ) :
    Complex.normSq (1 - η ^ 2 + η * I) = 1 - η ^ 2 + η ^ 4 := by
  simp [Complex.normSq_apply, pow_two]
  ring

theorem norm_sq_eg_coef (η : ℝ) : ‖(1 : ℂ) - η ^ 2 + η * I‖ ^ 2 = 1 - η ^ 2 + η ^ 4 := by
  rw [Complex.sq_norm, normSq_eg_coef]

theorem eg_coef_sq_lt_one {η : ℝ} (h0 : 0 < η) (h1 : η < 1) : 1 - η ^ 2 + η ^ 4 < 1 := by
  have hη2 : 0 < η ^ 2 := by positivity
  have hη2' : η ^ 2 < 1 := by nlinarith
  nlinarith

theorem norm_eg_coef_lt_one {η : ℝ} (h0 : 0 < η) (h1 : η < 1) :
    ‖(1 : ℂ) - η ^ 2 + η * I‖ < 1 := by
  have h := eg_coef_sq_lt_one h0 h1
  rw [← norm_sq_eg_coef] at h
  have hn : 0 ≤ ‖(1 : ℂ) - η ^ 2 + η * I‖ := norm_nonneg _
  nlinarith

theorem norm_eg (η : ℝ) (w : ℂ) : ‖eg η w‖ = ‖(1 : ℂ) - η ^ 2 + η * I‖ * ‖w‖ := by
  rw [eg_eq, norm_mul]

theorem norm_eg_lt {η : ℝ} (h0 : 0 < η) (h1 : η < 1) {w : ℂ} (hw : w ≠ 0) :
    ‖eg η w‖ < ‖w‖ := by
  rw [norm_eg]
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have := norm_eg_coef_lt_one h0 h1
  nlinarith

theorem eg_iterate (η : ℝ) (w : ℂ) (k : ℕ) :
    (eg η)^[k] w = (1 - η ^ 2 + η * I) ^ k * w := by
  have : eg η = fun z => (1 - η ^ 2 + η * I) * z := funext (eg_eq η)
  rw [this, iterate_mul]

theorem eg_iterate_tendsto_zero {η : ℝ} (h0 : 0 < η) (h1 : η < 1) (w : ℂ) :
    Tendsto (fun k : ℕ => (eg η)^[k] w) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hc := norm_eg_coef_lt_one h0 h1
  have hp : Tendsto (fun k : ℕ => ‖(1 : ℂ) - η ^ 2 + η * I‖ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hc
  have := hp.mul_const ‖w‖
  rw [zero_mul] at this
  refine this.congr (fun k => ?_)
  rw [eg_iterate, norm_mul, norm_pow]

theorem gda_fixed_iff {η : ℝ} (hη : 0 < η) (w : ℂ) : gda η w = w ↔ w = 0 := by
  constructor
  · intro h
    rw [gda_eq] at h
    have h' : ((η : ℂ) * I) * w = 0 := by linear_combination h
    have hc : (η : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hη.ne') I_ne_zero
    exact (mul_eq_zero.mp h').resolve_left hc
  · rintro rfl; rw [gda_eq, mul_zero]

theorem eg_fixed_iff {η : ℝ} (hη : 0 < η) (w : ℂ) : eg η w = w ↔ w = 0 := by
  constructor
  · intro h
    rw [eg_eq] at h
    have h' : (-(η : ℂ) ^ 2 + η * I) * w = 0 := by linear_combination h
    have hc : -(η : ℂ) ^ 2 + η * I ≠ 0 := by
      intro hc
      have := congrArg Complex.im hc
      simp [pow_two] at this
      exact hη.ne' this
    exact (mul_eq_zero.mp h').resolve_left hc
  · rintro rfl; rw [eg_eq, mul_zero]

/-- Pure Nash equilibrium (saddle point) of `f`: `x` minimises given `y`, `y` maximises given `x`. -/
def IsSaddle (x y : ℝ) : Prop := (∀ y', f x y' ≤ f x y) ∧ (∀ x', f x y ≤ f x' y)

theorem isSaddle_iff (x y : ℝ) : IsSaddle x y ↔ x = 0 ∧ y = 0 := by
  constructor
  · rintro ⟨hy, hx⟩
    simp only [f] at hy hx
    have hx0 : x = 0 := by
      have a := hy (y + 1)
      have b := hy (y - 1)
      nlinarith
    have hy0 : y = 0 := by
      have a := hx (x + 1)
      have b := hx (x - 1)
      nlinarith
    exact ⟨hx0, hy0⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨fun _ => by simp [f], fun _ => by simp [f]⟩

/-- The Nash equilibrium, read in the encoding `w = x + i y`, is exactly `w = 0`. -/
theorem isSaddle_iff_w (w : ℂ) : IsSaddle w.re w.im ↔ w = 0 := by
  rw [isSaddle_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact Complex.ext h1 h2
  · rintro rfl; simp

theorem fixed_points_are_nash {η : ℝ} (hη : 0 < η) (w : ℂ) :
    (gda η w = w ↔ IsSaddle w.re w.im) ∧ (eg η w = w ↔ IsSaddle w.re w.im) := by
  rw [isSaddle_iff_w, gda_fixed_iff hη, eg_fixed_iff hη]
  exact ⟨Iff.rfl, Iff.rfl⟩

end LookaheadStabilizesA
