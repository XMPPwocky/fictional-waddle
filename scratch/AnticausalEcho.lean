import Mathlib

/-!
# The anticausal echo of a selected event

Stationary linear-Gaussian dynamics `x_{t+1} = M x_t + noise`, stationary covariance `Σ` (named `C` in the code, since `Σ` is Lean's sum notation) (symmetric, invertible),
lag-one covariance `Cov(x_{t+1}, x_t) = M Σ`. Gaussian regression gives:
- FORWARD (what follows an observed state `a`): `E[x_{t+1} | x_t = a] = M a`;
- BACKWARD (the ECHO, what preceded a state selected at `a`): `E[x_{t−1} | x_t = a] = Σ Mᵀ Σ⁻¹ a`.

* A1 `echo_is_mirror_iff_detailed_balance`: the echo is the time-mirror of the relaxation (`Σ Mᵀ Σ⁻¹ = M`) iff
  `M Σ = Σ Mᵀ`, which is detailed balance (no rotation).
* A2 `rotation_echo_runs_backwards`: with `Σ = 1` and `M` orthogonal (a pure rotation), the echo is `Mᵀ = M⁻¹`: the
  past is recovered by UN-rotating. In time order the conditional path keeps its sense of rotation straight through
  the event, so the echo is NOT the mirror image of the relaxation (a mirror would reverse the rotation). (Docstring
  corrected before the toy ran; the theorem statement is unchanged.)
* A3 `echo_composes`: the k-step echo is `Σ (Mᵀ)^k Σ⁻¹`, the k-th power of the one-step echo. Its length is the
  relaxation time, which diverges at criticality (critical slowing down).
-/

namespace AnticausalEcho

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A1.** -/
theorem echo_is_mirror_iff_detailed_balance (M C : Matrix n n ℝ) (hC : IsUnit C.det) :
    C * Mᵀ * C⁻¹ = M ↔ M * C = C * Mᵀ := by
  constructor
  · intro h
    have : C * Mᵀ * C⁻¹ * C = M * C := by rw [h]
    rw [Matrix.mul_assoc (C * Mᵀ), Matrix.nonsing_inv_mul _ hC, Matrix.mul_one] at this
    exact this.symm
  · intro h
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hC, Matrix.mul_one]

/-- **A2.** -/
theorem rotation_echo_runs_backwards (M : Matrix n n ℝ) (hM : Mᵀ * M = 1) :
    (1 : Matrix n n ℝ) * Mᵀ * (1 : Matrix n n ℝ)⁻¹ = M⁻¹ := by
  rw [inv_one, Matrix.mul_one, Matrix.one_mul]
  exact (Matrix.inv_eq_left_inv hM).symm

/-- **A3.** -/
theorem echo_composes (M C : Matrix n n ℝ) (hC : IsUnit C.det) (k : ℕ) :
    (C * Mᵀ * C⁻¹) ^ k = C * (Mᵀ) ^ k * C⁻¹ := by
  induction k with
  | zero => simp [Matrix.mul_nonsing_inv _ hC]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc C⁻¹ C, Matrix.nonsing_inv_mul _ hC, Matrix.one_mul]

end AnticausalEcho
