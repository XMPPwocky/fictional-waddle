import Mathlib

/-!
# Sharp signals need d ∈ {1, 3}; coupled oscillators are independent normal modes

**Huygens.** A spherical pulse `u = f(t − r) · r^(−k)` with `k = (d − 1)/2` (profile `f` carried undistorted, only
attenuated). Write `F0 = f(t − r)`, `F1 = f'`, `F2 = f''`. Then `u_t t = F2 r^(−k)`, `u_r = −F1 r^(−k) − k F0 r^(−k−1)` and
`u_rr = F2 r^(−k) + 2k F1 r^(−k−1) + k(k+1) F0 r^(−k−2)`.
* H1 `radial_residual`: the radial wave operator `u_tt − u_rr − (d−1)/r · u_r` equals `(d−1)(d−3)/4 · F0 · r^(−k−2)`.
* H2 `sharp_iff`: the residual vanishes for every profile iff `d = 1` or `d = 3`.
* H3 `sharp_and_stable_is_three`: with OnlyThree's finite-fluctuation condition `d > 2`, only `d = 3` remains.

**Normal modes.**
* N1 `normal_modes_decouple`: if the coupling is `K = U D Uᵀ` with `U` orthogonal (Mathlib's
  `Matrix.IsHermitian.spectral_theorem` supplies this for every symmetric `K`), then `a = −K x` iff `Uᵀa = −D(Uᵀx)`.
  With `D` diagonal, the coupled system `ẍ = −Kx` is exactly independent oscillators in the normal coordinates `Uᵀx`.
-/

open Matrix

namespace SignalsAndModes

/-- **H1.** The residual of an undistorted spherical pulse under the `d`-dimensional radial wave operator. -/
theorem radial_residual (d r F0 F1 F2 : ℝ) (hr : 0 < r) :
    F2 * r ^ (-((d - 1) / 2))
      - (F2 * r ^ (-((d - 1) / 2)) + 2 * ((d - 1) / 2) * F1 * r ^ (-((d - 1) / 2) - 1)
          + ((d - 1) / 2) * ((d - 1) / 2 + 1) * F0 * r ^ (-((d - 1) / 2) - 2))
      - (d - 1) / r * (-(F1 * r ^ (-((d - 1) / 2))) - ((d - 1) / 2) * F0 * r ^ (-((d - 1) / 2) - 1))
      = (d - 1) * (d - 3) / 4 * F0 * r ^ (-((d - 1) / 2) - 2) := by
  have h1 : r ^ (-((d - 1) / 2) - 1) = r ^ (-((d - 1) / 2)) / r := Real.rpow_sub_one hr.ne' _
  have h2 : r ^ (-((d - 1) / 2) - 2) = r ^ (-((d - 1) / 2)) / r / r := by
    rw [show -((d - 1) / 2) - 2 = (-((d - 1) / 2) - 1) - 1 by ring, Real.rpow_sub_one hr.ne', h1]
  rw [h1, h2]
  field_simp
  ring

/-- **H2.** Undistorted spherical pulses for every profile iff `d = 1` or `d = 3`. -/
theorem sharp_iff (d r : ℝ) (hr : 0 < r) :
    (∀ F0 : ℝ, (d - 1) * (d - 3) / 4 * F0 * r ^ (-((d - 1) / 2) - 2) = 0) ↔ (d = 1 ∨ d = 3) := by
  have hp : 0 < r ^ (-((d - 1) / 2) - 2) := Real.rpow_pos_of_pos hr _
  constructor
  · intro h
    have h1 := h 1
    have : (d - 1) * (d - 3) = 0 := by
      have : (d - 1) * (d - 3) / 4 * r ^ (-((d - 1) / 2) - 2) = 0 := by simpa using h1
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact absurd h hp.ne'
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  · rintro (h | h) F0 <;> subst h <;> ring

/-- **H3.** Sharp signals and finite thermal fluctuations (`d > 2`, OnlyThree D2): `d = 3`. -/
theorem sharp_and_stable_is_three (d : ℝ) (h2 : 2 < d) (hs : d = 1 ∨ d = 3) : d = 3 := by
  rcases hs with h | h
  · linarith
  · exact h

/-- **N1.** A symmetric coupling decouples into independent normal modes. -/
theorem normal_modes_decouple {n : ℕ} (K U D : Matrix (Fin n) (Fin n) ℝ) (hU1 : Uᵀ * U = 1) (hU2 : U * Uᵀ = 1)
    (hK : K = U * D * Uᵀ) (a x : Fin n → ℝ) :
    a = -(K *ᵥ x) ↔ Uᵀ *ᵥ a = -(D *ᵥ (Uᵀ *ᵥ x)) := by
  constructor
  · intro h
    rw [h, hK, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hU1, Matrix.one_mul]
  · intro h
    have : U *ᵥ (Uᵀ *ᵥ a) = U *ᵥ (-(D *ᵥ (Uᵀ *ᵥ x))) := by rw [h]
    rw [Matrix.mulVec_mulVec, hU2, Matrix.one_mulVec, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    rw [this, hK, Matrix.mul_assoc]

end SignalsAndModes
