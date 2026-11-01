import Mathlib

/-!
# Sources and states: when a boundary pins the bulk, for any (discretized) geometry

Discretize any bulk region. Interior values `u : n → ℝ`. The Dirichlet operator `M` is the graph Laplacian with the
boundary cells removed; their values move to the right-hand side as the SOURCE `f`.
- Euclidean (no phase): `(M + κ²) u = f`.
- Lorentzian (phase, frequency ω): `(M − ω²) u = f`.

* S1 `euclidean_always_pinned`: if `M` is positive definite (any connected Dirichlet Laplacian is), then for every
  `κ² ≥ 0` and every source `f` the bulk is unique. Unconditional holography.
* S2 `lorentzian_pinned_iff`: the bulk is unique for every source iff `det (M − ω²) ≠ 0`, i.e. iff ω² is not a
  normal-mode eigenvalue.
* S3 `bulk_is_source_plus_states`: given one solution `u₀`, every solution is `u₀ + v` with `(M − ω²) v = 0`. The
  sourceless modes `v` are the STATES; they are invisible to the boundary.
* S4 `two_dim_conformal_factor_drops`: in 2-D, for `g = Ω² · diag(1, −1)`, `√|det g| · g⁻¹ = diag(1, −1)`. So the
  massless wave operator `∂(√|g| g^{μν} ∂ φ)` does not see `Ω`. Global AdS₂ (`Ω = 1/sin σ`, `σ ∈ (0, π)`) is then
  the flat strip of width π.
* S5 `ads2_massless_spectrum`: the normalizable (Dirichlet) frequencies on that strip are `sin (ω π) = 0 ↔ ω ∈ ℤ`.
  This matches `ω = Δ + n` with `Δ = 1`, `n ≥ 0`, for the positive ones.
-/

namespace SourcesAndStates

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **S1.** -/
theorem euclidean_always_pinned (M : Matrix n n ℝ) (hM : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (M *ᵥ x)) (κ2 : ℝ)
    (hκ : 0 ≤ κ2) (f : n → ℝ) : ∃! u : n → ℝ, (M + κ2 • (1 : Matrix n n ℝ)) *ᵥ u = f := by
  set A := M + κ2 • (1 : Matrix n n ℝ)
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    by_contra hne
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hne
    have h0 : A *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have hA : A *ᵥ (x - y) = M *ᵥ (x - y) + κ2 • (x - y) := by
      simp [A, Matrix.add_mulVec, Matrix.smul_mulVec]
    have hpos := hM _ hz
    have hsq : 0 ≤ (x - y) ⬝ᵥ (x - y) := by
      simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have : (x - y) ⬝ᵥ (A *ᵥ (x - y)) = (x - y) ⬝ᵥ (M *ᵥ (x - y)) + κ2 * ((x - y) ⬝ᵥ (x - y)) := by
      rw [hA, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [h0, dotProduct_zero] at this
    nlinarith [mul_nonneg hκ hsq]
  have hbij : Function.Bijective A.mulVec :=
    ⟨hinj, Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)⟩
  exact (Function.bijective_iff_existsUnique _).mp hbij f

/-- **S2.** -/
theorem lorentzian_pinned_iff (M : Matrix n n ℝ) (ω2 : ℝ) :
    (∀ f : n → ℝ, ∃! u : n → ℝ, (M - ω2 • (1 : Matrix n n ℝ)) *ᵥ u = f) ↔
      (M - ω2 • (1 : Matrix n n ℝ)).det ≠ 0 := by
  rw [← Function.bijective_iff_existsUnique, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
  constructor
  · intro h; exact Matrix.mulVec_injective_iff_isUnit.mp h.1
  · intro h
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr h, Matrix.mulVec_surjective_iff_isUnit.mpr h⟩

/-- **S3.** -/
theorem bulk_is_source_plus_states (A : Matrix n n ℝ) (f u₀ : n → ℝ) (h₀ : A *ᵥ u₀ = f) (u : n → ℝ) :
    A *ᵥ u = f ↔ ∃ v : n → ℝ, A *ᵥ v = 0 ∧ u = u₀ + v := by
  constructor
  · intro h
    refine ⟨u - u₀, by rw [Matrix.mulVec_sub, h, h₀, sub_self], by abel⟩
  · rintro ⟨v, hv, rfl⟩
    rw [Matrix.mulVec_add, h₀, hv, add_zero]

/-- **S4.** -/
theorem two_dim_conformal_factor_drops (Ω : ℝ) (hΩ : Ω ≠ 0) :
    Real.sqrt |(!![Ω ^ 2, 0; 0, -Ω ^ 2] : Matrix (Fin 2) (Fin 2) ℝ).det| •
      (!![Ω ^ 2, 0; 0, -Ω ^ 2] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![1, 0; 0, -1] := by
  have h2 : Ω ^ 2 ≠ 0 := pow_ne_zero 2 hΩ
  have hdet : (!![Ω ^ 2, 0; 0, -Ω ^ 2] : Matrix (Fin 2) (Fin 2) ℝ).det = -(Ω ^ 2) ^ 2 := by
    rw [Matrix.det_fin_two_of]; ring
  have hinv : (!![Ω ^ 2, 0; 0, -Ω ^ 2] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![1 / Ω ^ 2, 0; 0, -(1 / Ω ^ 2)] := by
    apply Matrix.inv_eq_left_inv
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  rw [hinv, hdet, abs_neg, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp

/-- **S5.** -/
theorem ads2_massless_spectrum (ω : ℝ) : Real.sin (ω * Real.pi) = 0 ↔ ∃ k : ℤ, ω = k := by
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by have := Real.pi_pos; nlinarith [mul_right_cancel₀ this.ne' (hk.trans (by ring) : (k : ℝ) * Real.pi = ω * Real.pi)]⟩
  · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩

end SourcesAndStates
