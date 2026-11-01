import Mathlib

/-!
# Agent identity, J-lens invariance, squaring as cooling

Source:
- analytic agents can't be mimics, smooth ones can;
- the J-lens mutual information is reparametrization-invariant (the Gaussian log-det form);
- squaring a distribution is cooling it.

Status (all unconditional, no `sorry`):
* I1 `analytic_agents_agree`: proved.
* I2 as first written (`ContDiff ℝ ⊤`) is FALSE: in this Mathlib `⊤ : WithTop ℕ∞` is `ω`, i.e.
  analytic, so I1 forbids such a mimic. `smooth_mimic_exists_as_written_is_false` proves the
  negation. The intended statement, with C^∞ = `((⊤ : ℕ∞) : WithTop ℕ∞)`, is proved as
  `smooth_mimic_exists_infty` (also in `scratch/I2.lean`).
* J1 `gaussian_mi_invariant`: proved.
* C1 `square_is_half_temperature`: proved (also in `scratch/ForwardBackward.lean`).
-/

open Matrix

namespace AgentIdentity

/-- **I1 (analytic agents can't be mimics).** Two policies analytic on all of ℂ that agree on a
neighbourhood of one point agree everywhere: local verification of identity suffices. -/
theorem analytic_agents_agree (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) (z₀ : ℂ) (h : f =ᶠ[nhds z₀] g) : f = g :=
  AnalyticOnNhd.eq_of_eventuallyEq hf hg h

/-- **I2 as first written is false.** `ContDiff ℝ ⊤` means analytic here, and an analytic
function that vanishes on [-1, 1] vanishes everywhere. -/
theorem smooth_mimic_exists_as_written_is_false :
    ¬ ∃ f : ℝ → ℝ, ContDiff ℝ ⊤ f ∧ (∀ x ∈ Set.Icc (-1 : ℝ) 1, f x = 0) ∧ f 2 ≠ 0 := by
  rintro ⟨f, hf, hzero, h2⟩
  have hA : AnalyticOnNhd ℝ f Set.univ := hf.analyticOnNhd
  have hev : f =ᶠ[nhds (0 : ℝ)] 0 := by
    filter_upwards [Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with x hx
    simpa using hzero x hx
  have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hev
  exact h2 (this (Set.mem_univ 2))

/-- **I2 (corrected: smooth agents can be mimics).** There is a C^∞ policy that matches the zero
policy on the whole observed region [-1, 1] and still differs off-path. -/
theorem smooth_mimic_exists_infty :
    ∃ f : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ (∀ x ∈ Set.Icc (-1 : ℝ) 1, f x = 0) ∧
      f 2 ≠ 0 := by
  refine ⟨fun x => expNegInvGlue (x - 1), ?_, ?_, ?_⟩
  · exact expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)
  · intro x hx
    exact expNegInvGlue.zero_of_nonpos (by linarith [hx.2])
  · norm_num

end AgentIdentity

namespace JLens

/-- **J1 (the Gaussian MI is invariant under invertible reparametrization of each side).**
For a joint covariance with blocks Σxx, Σxy, Σyy, the quantity det Σxx · det Σyy / det Σ
(whose ½·log is the mutual information) is unchanged by x ↦ A x, y ↦ B y with A, B invertible. -/
theorem gaussian_mi_invariant {n m : ℕ} (Sxx : Matrix (Fin n) (Fin n) ℝ) (Sxy : Matrix (Fin n) (Fin m) ℝ)
    (Syy : Matrix (Fin m) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) (hS : (fromBlocks Sxx Sxy Sxyᵀ Syy).det ≠ 0) :
    ((A * Sxx * Aᵀ).det * (B * Syy * Bᵀ).det) /
        (fromBlocks (A * Sxx * Aᵀ) (A * Sxy * Bᵀ) (B * Sxyᵀ * Aᵀ) (B * Syy * Bᵀ)).det
      = (Sxx.det * Syy.det) / (fromBlocks Sxx Sxy Sxyᵀ Syy).det := by
  have hfac : fromBlocks (A * Sxx * Aᵀ) (A * Sxy * Bᵀ) (B * Sxyᵀ * Aᵀ) (B * Syy * Bᵀ)
      = fromBlocks A 0 0 B * fromBlocks Sxx Sxy Sxyᵀ Syy * fromBlocks Aᵀ 0 0 Bᵀ := by
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_assoc]
  have hD : (fromBlocks A (0 : Matrix (Fin n) (Fin m) ℝ) 0 B).det = A.det * B.det :=
    det_fromBlocks_zero₂₁ _ _ _
  have hDt : (fromBlocks Aᵀ (0 : Matrix (Fin n) (Fin m) ℝ) 0 Bᵀ).det = A.det * B.det := by
    rw [det_fromBlocks_zero₂₁, det_transpose, det_transpose]
  rw [hfac, Matrix.det_mul (fromBlocks A 0 0 B * _), Matrix.det_mul (fromBlocks A 0 0 B), hD, hDt]
  simp only [det_mul, det_transpose]
  field_simp

end JLens

namespace Cooling

/-- **C1 (squaring is cooling).** Normalizing pᵢ² is the softmax of 2·log p: the Born-style
square of a distribution is the same distribution at half the temperature. -/
theorem square_is_half_temperature {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (i : Fin n) :
    p i ^ 2 / ∑ j, p j ^ 2 = Real.exp (2 * Real.log (p i)) / ∑ j, Real.exp (2 * Real.log (p j)) := by
  have h : ∀ k, Real.exp (2 * Real.log (p k)) = p k ^ 2 := by
    intro k
    rw [show (2 : ℝ) * Real.log (p k) = Real.log (p k) + Real.log (p k) by ring, Real.exp_add,
      Real.exp_log (hp k)]
    ring
  simp only [h]

end Cooling
