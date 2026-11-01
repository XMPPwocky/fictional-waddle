import Mathlib

/-!
# Exact NTK dynamics for a model linear in its parameters

Setting: features `Φ : Matrix (Fin n) (Fin p) ℝ` (row `i` is the feature vector of training
input `i`), parameters `θ : Fin p → ℝ`, outputs `f θ = Φ *ᵥ θ`, targets `y : Fin n → ℝ`,
loss `L θ = (1/2) ‖Φ θ - y‖²` (written as a dot product of the residual with itself),
gradient `Φᵀ (Φ θ - y)`, one gradient step `θ' = θ - η Φᵀ (Φ θ - y)`,
neural tangent kernel `Θ = Φ Φᵀ`.

PROVED
* `hasGradient_loss`: the stated gradient is the gradient: `L` has Fréchet derivative
  `h ↦ (Φᵀ (Φθ - y)) ⬝ᵥ h` at every `θ`.
* `outputs_step` (1): `Φ θ' = Φ θ - η Θ (Φ θ - y)`, exactly (no linearisation error).
* `ntk_symm`, `ntk_quadForm`, `ntk_quadForm_nonneg`, `ntk_posSemidef` (2):
  `Θᵀ = Θ`, `vᵀ Θ v = ‖Φᵀ v‖²` (as `(Φᵀ v) ⬝ᵥ (Φᵀ v)`), hence `vᵀ Θ v ≥ 0`, and
  `Θ` is positive semidefinite in Mathlib's sense (`Matrix.PosSemidef`).
* `residual_step` (3): with `r = Φ θ - y`, `r' = Φ θ' - y = (1 - η Θ) r`.
* `contraction_factor` (4): if `λ > 0` and `0 < η < 2/λ` then `|1 - η λ| < 1`.
* `residual_component_step`, `residual_component_contracts` (4): if `Θ v = λ v`, the
  component of the residual along `v` obeys `v ⬝ᵥ r' = (1 - η λ) (v ⬝ᵥ r)`, and for
  `λ > 0`, `0 < η < 2/λ` its absolute value strictly decreases whenever it is nonzero.
* `residual_iterate_component`: after `k` steps the component is `(1 - η λ)^k (v ⬝ᵥ r₀)`.

INTERPRETED
* `‖·‖²` on `Fin n → ℝ` is taken as the Euclidean square `x ⬝ᵥ x` (Mathlib's default norm on
  `Fin n → ℝ` is the sup norm, so the dot product is the faithful reading).
* "The component along `v`" is `v ⬝ᵥ r`; since `Θ` is symmetric, `v ⬝ᵥ (Θ r) = λ (v ⬝ᵥ r)`.
* "`1`" in `1 - η Θ` is the identity matrix.
-/

namespace NTKLinearExactA

open Matrix

noncomputable section

variable {n p : ℕ}

/-- Outputs of the linear model. -/
def outputs (Φ : Matrix (Fin n) (Fin p) ℝ) (θ : Fin p → ℝ) : Fin n → ℝ := Φ *ᵥ θ

/-- Squared-error loss `(1/2) ‖Φ θ - y‖²`. -/
def loss (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (θ : Fin p → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ((Φ *ᵥ θ - y) ⬝ᵥ (Φ *ᵥ θ - y))

/-- The gradient `Φᵀ (Φ θ - y)`. -/
def grad (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (θ : Fin p → ℝ) : Fin p → ℝ :=
  Φᵀ *ᵥ (Φ *ᵥ θ - y)

/-- One gradient-descent step with learning rate `η`. -/
def step (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (η : ℝ) (θ : Fin p → ℝ) :
    Fin p → ℝ :=
  θ - η • grad Φ y θ

/-- The neural tangent kernel `Θ = Φ Φᵀ`. -/
def ntk (Φ : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin n) ℝ := Φ * Φᵀ

/-- The continuous linear functional `h ↦ g ⬝ᵥ h`. -/
def dotCLM (g : Fin p → ℝ) : (Fin p → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h => g ⬝ᵥ h
      map_add' := fun a b => dotProduct_add g a b
      map_smul' := fun c a => by simp [dotProduct_smul] }

/-- The loss has Fréchet derivative `h ↦ grad ⬝ᵥ h`, i.e. `grad` is its gradient. -/
theorem hasGradient_loss (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (θ : Fin p → ℝ) :
    HasFDerivAt (loss Φ y) (dotCLM (grad Φ y θ)) θ := by
  set D : (Fin p → ℝ) →L[ℝ] (Fin n → ℝ) := LinearMap.toContinuousLinearMap (mulVecLin Φ)
  have hr : HasFDerivAt (fun θ => Φ *ᵥ θ - y) D θ := by
    have := (D.hasFDerivAt (x := θ)).sub_const y
    simpa [D] using this
  have hri : ∀ i : Fin n, HasFDerivAt (fun θ => (Φ *ᵥ θ - y) i)
      ((ContinuousLinearMap.proj i).comp D) θ := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt.comp θ hr
  have hsum := HasFDerivAt.sum (u := Finset.univ) (fun i _ => (hri i).mul (hri i))
  have hL := hsum.const_mul (1 / 2 : ℝ)
  convert hL using 1
  · funext θ
    simp [loss, dotProduct, Finset.sum_apply]
  ext h
  simp only [_root_.smul_apply, _root_.sum_apply,
    _root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, dotCLM, grad, D,
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk, mulVecLin_apply]
  rw [mulVec_transpose, ← dotProduct_mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- (1) Outputs move exactly by `f' = f - η Θ (f - y)`. -/
theorem outputs_step (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (θ : Fin p → ℝ) :
    outputs Φ (step Φ y η θ) = outputs Φ θ - η • (ntk Φ *ᵥ (outputs Φ θ - y)) := by
  simp only [outputs, step, grad, ntk]
  rw [mulVec_sub, mulVec_smul, mulVec_mulVec]

/-- (2a) `Θ` is symmetric. -/
theorem ntk_symm (Φ : Matrix (Fin n) (Fin p) ℝ) : (ntk Φ)ᵀ = ntk Φ := by
  simp [ntk, transpose_mul]

/-- (2b) `vᵀ Θ v = ‖Φᵀ v‖²`. -/
theorem ntk_quadForm (Φ : Matrix (Fin n) (Fin p) ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ (ntk Φ *ᵥ v) = (Φᵀ *ᵥ v) ⬝ᵥ (Φᵀ *ᵥ v) := by
  rw [ntk, ← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]

/-- (2c) `vᵀ Θ v ≥ 0`. -/
theorem ntk_quadForm_nonneg (Φ : Matrix (Fin n) (Fin p) ℝ) (v : Fin n → ℝ) :
    0 ≤ v ⬝ᵥ (ntk Φ *ᵥ v) := by
  rw [ntk_quadForm]
  exact dotProduct_self_star_nonneg _

/-- (2d) `Θ` is positive semidefinite. -/
theorem ntk_posSemidef (Φ : Matrix (Fin n) (Fin p) ℝ) : (ntk Φ).PosSemidef := by
  have := Matrix.posSemidef_self_mul_conjTranspose Φ
  simpa [ntk, conjTranspose_eq_transpose_of_trivial] using this

/-- (3) The residual evolves as `r' = (1 - η Θ) r`. -/
theorem residual_step (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (θ : Fin p → ℝ) :
    outputs Φ (step Φ y η θ) - y = (1 - η • ntk Φ) *ᵥ (outputs Φ θ - y) := by
  rw [outputs_step, sub_mulVec, one_mulVec, smul_mulVec]
  abel

/-- (4a) The contraction factor: `λ > 0`, `0 < η < 2/λ` give `|1 - η λ| < 1`. -/
theorem contraction_factor {η lam : ℝ} (hlam : 0 < lam) (hη : 0 < η) (hη2 : η < 2 / lam) :
    |1 - η * lam| < 1 := by
  have h1 : 0 < η * lam := mul_pos hη hlam
  have h2 : η * lam < 2 := by
    have := (lt_div_iff₀ hlam).1 hη2
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-- (4b) If `Θ v = λ v`, the component of the residual along `v` is multiplied by
`1 - η λ` in one step. -/
theorem residual_component_step (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (θ : Fin p → ℝ) (v : Fin n → ℝ) (lam : ℝ) (hv : ntk Φ *ᵥ v = lam • v) :
    v ⬝ᵥ (outputs Φ (step Φ y η θ) - y) = (1 - η * lam) * (v ⬝ᵥ (outputs Φ θ - y)) := by
  rw [residual_step]
  set r := outputs Φ θ - y
  have hsym : v ⬝ᵥ (ntk Φ *ᵥ r) = lam * (v ⬝ᵥ r) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, ntk_symm, hv, smul_dotProduct, smul_eq_mul]
  rw [sub_mulVec, one_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, hsym,
    smul_eq_mul]
  ring

/-- (4c) Under `λ > 0`, `0 < η < 2/λ`, a nonzero component along the eigenvector `v`
strictly shrinks in absolute value. -/
theorem residual_component_contracts (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    {η lam : ℝ} (θ : Fin p → ℝ) (v : Fin n → ℝ) (hv : ntk Φ *ᵥ v = lam • v)
    (hlam : 0 < lam) (hη : 0 < η) (hη2 : η < 2 / lam)
    (hne : v ⬝ᵥ (outputs Φ θ - y) ≠ 0) :
    |v ⬝ᵥ (outputs Φ (step Φ y η θ) - y)| < |v ⬝ᵥ (outputs Φ θ - y)| := by
  rw [residual_component_step Φ y η θ v lam hv, abs_mul]
  have hc := contraction_factor hlam hη hη2
  have hpos : 0 < |v ⬝ᵥ (outputs Φ θ - y)| := abs_pos.2 hne
  calc |1 - η * lam| * |v ⬝ᵥ (outputs Φ θ - y)|
      < 1 * |v ⬝ᵥ (outputs Φ θ - y)| := mul_lt_mul_of_pos_right hc hpos
    _ = _ := one_mul _

/-- After `k` steps the component along the eigenvector is `(1 - η λ)^k` times the initial
one. -/
theorem residual_iterate_component (Φ : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (θ : Fin p → ℝ) (v : Fin n → ℝ) (lam : ℝ) (hv : ntk Φ *ᵥ v = lam • v) (k : ℕ) :
    v ⬝ᵥ (outputs Φ ((step Φ y η)^[k] θ) - y)
      = (1 - η * lam) ^ k * (v ⬝ᵥ (outputs Φ θ - y)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', residual_component_step Φ y η _ v lam hv, ih, pow_succ]
    ring

end

end NTKLinearExactA
