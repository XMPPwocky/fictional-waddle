import Mathlib

/-!
# One gradient step of a linearly parametrised model, in NTK form

Setting: features `Φ : Matrix (Fin n) (Fin p) ℝ` (row `i` = feature vector of training
input `i`), parameters `θ : Fin p → ℝ`, outputs `f θ = Φ *ᵥ θ`, targets `y`,
loss `L θ = (1/2) ‖Φ θ - y‖²`, gradient `∇L θ = Φᵀ (Φ θ - y)`, one gradient step
`θ' = θ - η ∇L θ`, neural tangent kernel `Θ = Φ Φᵀ`.

PROVED
* `loss_expand` : `L (θ + d) = L θ + ∇L θ ⬝ d + (1/2) ‖Φ d‖²` exactly, so `Φᵀ (Φθ - y)`
  is the gradient of `L` (the remainder is quadratic in `d`).
* `outputs_step` (1) : `f θ' = f θ - η • Θ *ᵥ (f θ - y)`.
* `ntk_symm`, `ntk_quadForm`, `ntk_quadForm_sum_sq`, `ntk_quadForm_nonneg`,
  `ntk_posSemidef` (2) :
  `Θᵀ = Θ`, `v ⬝ Θ v = (Φᵀ v) ⬝ (Φᵀ v) = ∑ᵢ (Φᵀ v)ᵢ² ≥ 0`, and `Θ.PosSemidef`.
* `residual_step` (3) : `r' = (1 - η • Θ) *ᵥ r` with `r = f θ - y`, `r' = f θ' - y`.
* `eigen_factor_contracts` (4) : if `Θ v = λ v`, `0 < λ`, `0 < η < 2/λ`, then
  `|1 - η λ| < 1`; `step_on_eigvec` : `(1 - η • Θ) *ᵥ v = (1 - η λ) • v`;
  `eigen_component_step` : `v ⬝ r' = (1 - η λ) (v ⬝ r)` for any residual `r`
  (uses symmetry of `Θ`); `eigen_component_contracts` : hence
  `|v ⬝ r'| ≤ |v ⬝ r|`, strictly when `v ⬝ r ≠ 0`.

INTERPRETED
* `‖·‖²` is written as the dot product `w ⬝ᵥ w` of real vectors (equal to the squared
  Euclidean norm); "‖(1 - η λ)‖ < 1" is the absolute value `|1 - η λ| < 1`.
* "the component along `v`" is the coordinate `v ⬝ᵥ r`.
-/

namespace NTKLinearExactB

open Matrix

variable {n p : ℕ}

/-- Model outputs on the training inputs. -/
def outputs (Φ : Matrix (Fin n) (Fin p) ℝ) (θ : Fin p → ℝ) : Fin n → ℝ := Φ *ᵥ θ

/-- Squared-error loss `(1/2) ‖Φ θ - y‖²`. -/
noncomputable def loss (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (θ : Fin p → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ((Φ *ᵥ θ - y) ⬝ᵥ (Φ *ᵥ θ - y))

/-- Gradient `Φᵀ (Φ θ - y)`. -/
def grad (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (θ : Fin p → ℝ) : Fin p → ℝ :=
  Φᵀ *ᵥ (Φ *ᵥ θ - y)

/-- One gradient-descent step with learning rate `η`. -/
def step (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (η : ℝ) (θ : Fin p → ℝ) :
    Fin p → ℝ :=
  θ - η • grad Φ y θ

/-- Neural tangent kernel `Θ = Φ Φᵀ`. -/
def ntk (Φ : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin n) ℝ := Φ * Φᵀ

/-- Exact second-order expansion of the loss; identifies `grad` as the gradient. -/
theorem loss_expand (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (θ d : Fin p → ℝ) :
    loss Φ y (θ + d) = loss Φ y θ + grad Φ y θ ⬝ᵥ d
      + (1 / 2 : ℝ) * ((Φ *ᵥ d) ⬝ᵥ (Φ *ᵥ d)) := by
  unfold loss grad
  have h1 : Φ *ᵥ (θ + d) - y = (Φ *ᵥ θ - y) + Φ *ᵥ d := by
    rw [mulVec_add]; abel
  have h2 : (Φᵀ *ᵥ (Φ *ᵥ θ - y)) ⬝ᵥ d = (Φ *ᵥ θ - y) ⬝ᵥ (Φ *ᵥ d) := by
    rw [dotProduct_comm, dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  rw [h1, h2, add_dotProduct, dotProduct_add, dotProduct_add,
    dotProduct_comm (Φ *ᵥ d) (Φ *ᵥ θ - y)]
  ring

/-- (1) Outputs move by the NTK applied to the residual. -/
theorem outputs_step (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (θ : Fin p → ℝ) :
    outputs Φ (step Φ y η θ) = outputs Φ θ - η • (ntk Φ *ᵥ (outputs Φ θ - y)) := by
  unfold outputs step grad ntk
  rw [mulVec_sub, mulVec_smul, mulVec_mulVec]

/-- (2a) The NTK is symmetric. -/
theorem ntk_symm (Φ : Matrix (Fin n) (Fin p) ℝ) : (ntk Φ)ᵀ = ntk Φ := by
  unfold ntk
  rw [transpose_mul, transpose_transpose]

/-- (2b) Quadratic form of the NTK. -/
theorem ntk_quadForm (Φ : Matrix (Fin n) (Fin p) ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ (ntk Φ *ᵥ v) = (Φᵀ *ᵥ v) ⬝ᵥ (Φᵀ *ᵥ v) := by
  unfold ntk
  rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]

/-- (2b') The quadratic form is a sum of squares. -/
theorem ntk_quadForm_sum_sq (Φ : Matrix (Fin n) (Fin p) ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ (ntk Φ *ᵥ v) = ∑ j, (Φᵀ *ᵥ v) j ^ 2 := by
  rw [ntk_quadForm]
  simp [dotProduct, sq]

/-- (2c) Nonnegativity of the quadratic form. -/
theorem ntk_quadForm_nonneg (Φ : Matrix (Fin n) (Fin p) ℝ) (v : Fin n → ℝ) :
    0 ≤ v ⬝ᵥ (ntk Φ *ᵥ v) := by
  rw [ntk_quadForm_sum_sq]
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- (2d) The NTK is positive semidefinite (Mathlib's notion). -/
theorem ntk_posSemidef (Φ : Matrix (Fin n) (Fin p) ℝ) : (ntk Φ).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose Φ
  simpa [ntk, conjTranspose_eq_transpose_of_trivial] using h

/-- (3) Residual dynamics `r' = (1 - η Θ) r`. -/
theorem residual_step (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (θ : Fin p → ℝ) :
    outputs Φ (step Φ y η θ) - y = (1 - η • ntk Φ) *ᵥ (outputs Φ θ - y) := by
  rw [outputs_step, sub_mulVec, one_mulVec, smul_mulVec]
  abel

/-- (4a) The contraction factor on a positive eigenvalue. -/
theorem eigen_factor_contracts {lam η : ℝ} (hlam : 0 < lam) (hη : 0 < η)
    (hη2 : η < 2 / lam) : |1 - η * lam| < 1 := by
  have h1 : 0 < η * lam := mul_pos hη hlam
  have h2 : η * lam < 2 := by
    have := mul_lt_mul_of_pos_right hη2 hlam
    rwa [div_mul_cancel₀ 2 hlam.ne'] at this
  rw [abs_lt]
  constructor <;> linarith

/-- (4b) The step operator acts on an eigenvector by the scalar `1 - η λ`. -/
theorem step_on_eigvec (Φ : Matrix (Fin n) (Fin p) ℝ) (η lam : ℝ) (v : Fin n → ℝ)
    (hv : ntk Φ *ᵥ v = lam • v) :
    (1 - η • ntk Φ) *ᵥ v = (1 - η * lam) • v := by
  rw [sub_mulVec, one_mulVec, smul_mulVec, hv, smul_smul, sub_smul, one_smul]

/-- (4c) The component of the residual along an eigenvector is multiplied by `1 - η λ`. -/
theorem eigen_component_step (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (η lam : ℝ) (θ : Fin p → ℝ) (v : Fin n → ℝ) (hv : ntk Φ *ᵥ v = lam • v) :
    v ⬝ᵥ (outputs Φ (step Φ y η θ) - y) = (1 - η * lam) * (v ⬝ᵥ (outputs Φ θ - y)) := by
  rw [residual_step]
  set r := outputs Φ θ - y
  have hsymm : (1 - η • ntk Φ)ᵀ = 1 - η • ntk Φ := by
    rw [transpose_sub, transpose_one, transpose_smul, ntk_symm]
  calc v ⬝ᵥ ((1 - η • ntk Φ) *ᵥ r) = (v ᵥ* (1 - η • ntk Φ)) ⬝ᵥ r := dotProduct_mulVec _ _ _
    _ = ((1 - η • ntk Φ)ᵀ *ᵥ v) ⬝ᵥ r := by rw [mulVec_transpose]
    _ = ((1 - η * lam) • v) ⬝ᵥ r := by rw [hsymm, step_on_eigvec Φ η lam v hv]
    _ = (1 - η * lam) * (v ⬝ᵥ r) := smul_dotProduct _ _ _

/-- (4d) Under `0 < λ`, `0 < η < 2/λ`, the eigen-component of the residual contracts. -/
theorem eigen_component_contracts (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    {η lam : ℝ} (θ : Fin p → ℝ) (v : Fin n → ℝ) (hv : ntk Φ *ᵥ v = lam • v)
    (hlam : 0 < lam) (hη : 0 < η) (hη2 : η < 2 / lam) :
    |v ⬝ᵥ (outputs Φ (step Φ y η θ) - y)| ≤ |v ⬝ᵥ (outputs Φ θ - y)| ∧
    (v ⬝ᵥ (outputs Φ θ - y) ≠ 0 →
      |v ⬝ᵥ (outputs Φ (step Φ y η θ) - y)| < |v ⬝ᵥ (outputs Φ θ - y)|) := by
  rw [eigen_component_step Φ y η lam θ v hv, abs_mul]
  have hc := eigen_factor_contracts hlam hη hη2
  refine ⟨?_, fun h => ?_⟩
  · exact mul_le_of_le_one_left (abs_nonneg _) hc.le
  · exact mul_lt_of_lt_one_left (abs_pos.mpr h) hc

end NTKLinearExactB
