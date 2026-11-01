import Mathlib

/-!
# E2: Fractional Kelly in the Gaussian (quadratic) approximation — proofs

Proofs of the statements in `E2_fractional_kelly.statements.lean` (statements identical).

Setup. `S : Matrix (Fin n) (Fin n) ℝ` is the covariance (`Σ` is a reserved token in
Lean, so it is spelled `S`), `e : Fin n → ℝ` is the edge vector, `f` is the vector of
bet fractions. The *quadratic growth approximation* is
`growth S e f = e ⬝ᵥ f - ½ · f ⬝ᵥ (S *ᵥ f)` and the *variance term* is
`variance S f = f ⬝ᵥ (S *ᵥ f)`. Full Kelly is `kelly S e = S⁻¹ *ᵥ e`.

Interpretation (NOT proved here): that `growth` approximates the expected log-growth
of wealth for small bets with mean excess return `e` and covariance `S` (second-order
Taylor expansion of `log (1 + f ⬝ r)`), and that `variance` is the per-period variance
of the portfolio return. Everything proved is an exact identity/inequality about the
quadratic model itself.

Second-agent audit: recompiled, statements re-checked identical to the
statements file, axioms re-checked. Added `risk_averse_fractional_kelly` (going up:
fractional Kelly `γ⁻¹ f*` is the exact unique maximiser of the risk-penalised objective
`e·f - (γ/2) fᵀSf`, i.e. full Kelly for covariance `γ S`) and a concrete correlated 2×2
example (`Sex = [[2,1],[1,2]]`, `e = (1,1)`: `f* = (1/3,1/3)`, `g* = 1/3`, half-Kelly
`1/4`) so the `PosDef` hypotheses are visibly satisfiable. No earlier statement changed.
-/

open Matrix

namespace E2FractionalKelly

variable {n : ℕ}

/-- Quadratic (Gaussian) approximation to log-growth: `g(f) = e·f - ½ fᵀ S f`. -/
noncomputable def growth (S : Matrix (Fin n) (Fin n) ℝ) (e f : Fin n → ℝ) : ℝ :=
  e ⬝ᵥ f - (1 / 2) * (f ⬝ᵥ (S *ᵥ f))

/-- The variance term `fᵀ S f`. -/
def variance (S : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) : ℝ :=
  f ⬝ᵥ (S *ᵥ f)

/-- Full Kelly fractions `f* = S⁻¹ e` (Mathlib's `⁻¹` is `Ring.inverse` of the matrix). -/
noncomputable def kelly (S : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) : Fin n → ℝ :=
  S⁻¹ *ᵥ e

/-! ## Algebraic core: needs only the first-order condition `S f* = e` -/

/-- PROVED. If `S f* = e` (no symmetry, no definiteness needed), then
`g(κ f*) = κ (2 - κ) g(f*)` for every real `κ`. -/
theorem fractional_growth_of_solves (S : Matrix (Fin n) (Fin n) ℝ) (e fstar : Fin n → ℝ)
    (h : S *ᵥ fstar = e) (κ : ℝ) :
    growth S e (κ • fstar) = κ * (2 - κ) * growth S e fstar := by
  have hc : fstar ⬝ᵥ e = e ⬝ᵥ fstar := dotProduct_comm _ _
  simp only [growth, mulVec_smul, smul_dotProduct, dotProduct_smul, h, hc, smul_eq_mul]
  ring

/-- PROVED. If `S f* = e` then `g(f*) = ½ e·f*`. -/
theorem growth_of_solves (S : Matrix (Fin n) (Fin n) ℝ) (e fstar : Fin n → ℝ)
    (h : S *ᵥ fstar = e) :
    growth S e fstar = (1 / 2) * (e ⬝ᵥ fstar) := by
  have hc : fstar ⬝ᵥ e = e ⬝ᵥ fstar := dotProduct_comm _ _
  simp only [growth, h, hc]
  ring

/-- PROVED. The variance term is a quadratic form: it scales as `κ²`. -/
theorem variance_smul (S : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) (κ : ℝ) :
    variance S (κ • f) = κ ^ 2 * variance S f := by
  simp only [variance, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- PROVED. Completing the square: for symmetric `S` with `S f* = e`,
`g(f) = g(f*) - ½ (f - f*)ᵀ S (f - f*)`. -/
theorem growth_eq_sub_variance {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.IsHermitian)
    {e fstar : Fin n → ℝ} (h : S *ᵥ fstar = e) (f : Fin n → ℝ) :
    growth S e f = growth S e fstar - (1 / 2) * variance S (f - fstar) := by
  have hT : Sᵀ = S := by
    have := hS.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  -- symmetry: f*ᵀ S f = (S f*)ᵀ f = e·f
  have h1 : fstar ⬝ᵥ (S *ᵥ f) = e ⬝ᵥ f := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hT, h]
  have h2 : f ⬝ᵥ (S *ᵥ fstar) = e ⬝ᵥ f := by rw [h, dotProduct_comm]
  have h3 : fstar ⬝ᵥ (S *ᵥ fstar) = e ⬝ᵥ fstar := by rw [h, dotProduct_comm]
  simp only [growth, variance, mulVec_sub, sub_dotProduct, dotProduct_sub, h1, h2, h3]
  ring

/-! ## Positive-definite covariance: `S⁻¹ e` is the unique maximiser -/

/-- PROVED. For positive-definite `S`, `S (S⁻¹ e) = e`. -/
theorem kelly_solves {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (e : Fin n → ℝ) :
    S *ᵥ kelly S e = e := by
  unfold kelly
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det S).mp hS.isUnit), one_mulVec]

/-- PROVED. `f* = S⁻¹ e` maximises `g`. -/
theorem growth_le_kelly {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (e f : Fin n → ℝ) :
    growth S e f ≤ growth S e (kelly S e) := by
  rw [growth_eq_sub_variance hS.isHermitian (kelly_solves hS e) f]
  have := hS.posSemidef.dotProduct_mulVec_nonneg (f - kelly S e)
  simp only [star_trivial] at this
  unfold variance
  linarith

/-- PROVED. The maximiser is unique (strict inequality off `f*`). -/
theorem growth_lt_kelly {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (e f : Fin n → ℝ)
    (hf : f ≠ kelly S e) :
    growth S e f < growth S e (kelly S e) := by
  rw [growth_eq_sub_variance hS.isHermitian (kelly_solves hS e) f]
  have := hS.dotProduct_mulVec_pos (sub_ne_zero.mpr hf)
  simp only [star_trivial] at this
  unfold variance
  linarith

/-- PROVED. The optimal growth is `g* = ½ eᵀ S⁻¹ e`. -/
theorem kelly_growth_value {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (e : Fin n → ℝ) :
    growth S e (kelly S e) = (1 / 2) * (e ⬝ᵥ (S⁻¹ *ᵥ e)) := by
  rw [growth_of_solves S e _ (kelly_solves hS e)]
  rfl

/-- PROVED. With a nonzero edge, the optimal growth is strictly positive. -/
theorem kelly_growth_pos {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {e : Fin n → ℝ}
    (he : e ≠ 0) :
    0 < growth S e (kelly S e) := by
  rw [kelly_growth_value hS]
  have := hS.inv.dotProduct_mulVec_pos he
  simp only [star_trivial] at this
  linarith

/-- PROVED. At full Kelly the variance term equals twice the growth: `f*ᵀ S f* = 2 g*`. -/
theorem kelly_variance {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (e : Fin n → ℝ) :
    variance S (kelly S e) = 2 * growth S e (kelly S e) := by
  rw [growth_of_solves S e _ (kelly_solves hS e)]
  simp only [variance, kelly_solves hS e, dotProduct_comm (kelly S e) e]
  ring

/-- PROVED. Fractional Kelly: `g(κ f*) = κ (2 - κ) g*`. -/
theorem fractional_growth {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (e : Fin n → ℝ)
    (κ : ℝ) :
    growth S e (κ • kelly S e) = κ * (2 - κ) * growth S e (kelly S e) := by
  exact fractional_growth_of_solves S e _ (kelly_solves hS e) κ

/-- PROVED. Half-Kelly keeps 3/4 of the optimal growth with 1/4 of the variance term. -/
theorem half_kelly {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (e : Fin n → ℝ) :
    growth S e ((1 / 2 : ℝ) • kelly S e) = (3 / 4) * growth S e (kelly S e) ∧
    variance S ((1 / 2 : ℝ) • kelly S e) = (1 / 4) * variance S (kelly S e) := by
  refine ⟨?_, ?_⟩
  · rw [fractional_growth hS]; ring
  · rw [variance_smul]; ring

/-- PROVED. Overbetting symmetry: `κ` and `2 - κ` give the same growth. -/
theorem overbet_symmetry {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (e : Fin n → ℝ)
    (κ : ℝ) :
    growth S e (κ • kelly S e) = growth S e ((2 - κ) • kelly S e) := by
  rw [fractional_growth hS, fractional_growth hS]
  ring

/-- PROVED. Overbetting: with a nonzero edge, betting more than twice Kelly (`κ > 2`)
gives strictly negative growth in the quadratic model (and `κ = 2` gives zero). -/
theorem overbet_negative {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {e : Fin n → ℝ}
    (he : e ≠ 0) :
    growth S e ((2 : ℝ) • kelly S e) = 0 ∧
    ∀ κ : ℝ, 2 < κ → growth S e (κ • kelly S e) < 0 := by
  have hg := kelly_growth_pos hS he
  refine ⟨?_, fun κ hκ => ?_⟩
  · rw [fractional_growth hS]; ring
  · rw [fractional_growth hS]
    have : κ * (2 - κ) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    exact mul_neg_of_neg_of_pos this hg

/-- PROVED. Growth/variance trade-off along the Kelly ray: for `κ ∈ (0,1)`, the
fraction of growth kept, `κ(2-κ)`, strictly exceeds the fraction of variance kept, `κ²`. -/
theorem fraction_growth_gt_variance {κ : ℝ} (h0 : 0 < κ) (h1 : κ < 1) :
    κ ^ 2 < κ * (2 - κ) := by
  nlinarith

/-! ## Scalar case (one asset, `σ² > 0`) -/

/-- PROVED. Scalar Kelly: `μ f - ½ σ² f² ≤ μ² / (2σ²)` with equality at `f = μ/σ²`. -/
theorem scalar_kelly {σ2 : ℝ} (hσ : 0 < σ2) (μ f : ℝ) :
    μ * f - (1 / 2) * σ2 * f ^ 2 ≤ μ ^ 2 / (2 * σ2) ∧
    μ * (μ / σ2) - (1 / 2) * σ2 * (μ / σ2) ^ 2 = μ ^ 2 / (2 * σ2) := by
  have hne : σ2 ≠ 0 := hσ.ne'
  refine ⟨?_, ?_⟩
  · -- μ²/(2σ²) - g(f) = σ²/2 · (f - μ/σ²)²
    have key : μ ^ 2 / (2 * σ2) - (μ * f - (1 / 2) * σ2 * f ^ 2)
        = (1 / 2) * σ2 * (f - μ / σ2) ^ 2 := by
      field_simp
      ring
    have : 0 ≤ (1 / 2) * σ2 * (f - μ / σ2) ^ 2 := by positivity
    linarith
  · field_simp
    ring

/-- PROVED. Scalar fractional Kelly: `g(κ μ/σ²) = κ(2-κ) μ²/(2σ²)` and the variance
`σ² f²` at `f = κ μ/σ²` is `κ²` times its full-Kelly value. -/
theorem scalar_fractional {σ2 : ℝ} (hσ : 0 < σ2) (μ κ : ℝ) :
    μ * (κ * (μ / σ2)) - (1 / 2) * σ2 * (κ * (μ / σ2)) ^ 2 = κ * (2 - κ) * (μ ^ 2 / (2 * σ2)) ∧
    σ2 * (κ * (μ / σ2)) ^ 2 = κ ^ 2 * (σ2 * (μ / σ2) ^ 2) := by
  have hne : σ2 ≠ 0 := hσ.ne'
  refine ⟨?_, ?_⟩
  · field_simp
  · ring

/-! ## Going up: fractional Kelly is *exact* Kelly for a risk-averse objective

(Added by the second agent.) -/

/-- PROVED. For risk aversion `γ > 0`, the penalised objective `e·f - (γ/2) fᵀ S f` is
maximised exactly at the fractional-Kelly bet `γ⁻¹ f*`, uniquely. So fractional Kelly with
`κ = 1/γ` is not an ad-hoc haircut: it is the optimum of the quadratic model with the risk
term inflated by `γ` (equivalently, full Kelly for covariance `γ S`). Half-Kelly is `γ = 2`.
Interpretation (NOT proved): reading `γ` as a mean-variance risk-aversion coefficient. -/
theorem risk_averse_fractional_kelly {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    (e : Fin n → ℝ) {γ : ℝ} (hγ : 0 < γ) (f : Fin n → ℝ) :
    (e ⬝ᵥ f - (γ / 2) * variance S f ≤
      e ⬝ᵥ (γ⁻¹ • kelly S e) - (γ / 2) * variance S (γ⁻¹ • kelly S e)) ∧
    (f ≠ γ⁻¹ • kelly S e →
      e ⬝ᵥ f - (γ / 2) * variance S f <
        e ⬝ᵥ (γ⁻¹ • kelly S e) - (γ / 2) * variance S (γ⁻¹ • kelly S e)) := by
  have hγS : (γ • S).PosDef := hS.smul hγ
  have hsol : (γ • S) *ᵥ (γ⁻¹ • kelly S e) = e := by
    rw [smul_mulVec, mulVec_smul, kelly_solves hS, smul_smul, mul_inv_cancel₀ hγ.ne', one_smul]
  -- the risk-averse objective is the quadratic growth for covariance `γ S`
  have hobj : ∀ g : Fin n → ℝ, e ⬝ᵥ g - (γ / 2) * variance S g = growth (γ • S) e g := by
    intro g
    simp only [growth, variance, smul_mulVec, dotProduct_smul, smul_eq_mul]
    ring
  have key := growth_eq_sub_variance hγS.isHermitian hsol f
  rw [hobj, hobj, key]
  refine ⟨?_, fun hf => ?_⟩
  · have := hγS.posSemidef.dotProduct_mulVec_nonneg (f - γ⁻¹ • kelly S e)
    simp only [star_trivial] at this
    unfold variance
    linarith
  · have := hγS.dotProduct_mulVec_pos (sub_ne_zero.mpr hf)
    simp only [star_trivial] at this
    unfold variance
    linarith

/-! ## Non-vacuity: a concrete correlated 2×2 example

(Added by the second agent.) `S = [[2,1],[1,2]]`, `e = (1,1)`. Then `S` is positive
definite, `f* = (1/3, 1/3)`, `g* = 1/3`, half-Kelly growth `= 1/4 = (3/4) g*`, and the
full-Kelly variance term is `2/3 = 2 g*`. This shows the `PosDef` hypotheses are
satisfiable by a non-diagonal matrix and the general theorems give the right numbers. -/

/-- The example covariance `[[2,1],[1,2]]`. -/
def Sex : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]

/-- PROVED. The example covariance is positive definite. -/
theorem Sex_posDef : Sex.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Sex]
  · intro x hx
    have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (by ext i; fin_cases i <;> simp [h.1, h.2])
    simp only [star_trivial, Sex, dotProduct, mulVec, Fin.sum_univ_two, of_apply, cons_val',
      cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    rcases hx' with h | h
    · have := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg (x 0 + x 1)]
    · have := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg (x 0 + x 1)]

/-- PROVED. In the example, `f* = S⁻¹ e = (1/3, 1/3)`. -/
theorem kelly_Sex : kelly Sex ![1, 1] = ![1/3, 1/3] := by
  have hsol : Sex *ᵥ ![1/3, 1/3] = ![1, 1] := by
    ext i; fin_cases i <;> simp [Sex, mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  have hu : IsUnit Sex.det := (isUnit_iff_isUnit_det Sex).mp Sex_posDef.isUnit
  unfold kelly
  rw [← hsol, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]

/-- PROVED. Example numbers: `g* = 1/3`, half-Kelly growth `= 1/4`, full-Kelly variance
term `= 2/3`. -/
theorem example_values : growth Sex ![1, 1] (kelly Sex ![1, 1]) = 1 / 3 ∧
    growth Sex ![1, 1] ((1 / 2 : ℝ) • kelly Sex ![1, 1]) = 1 / 4 ∧
    variance Sex (kelly Sex ![1, 1]) = 2 / 3 := by
  rw [kelly_Sex]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [growth, variance, Sex, mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

end E2FractionalKelly
