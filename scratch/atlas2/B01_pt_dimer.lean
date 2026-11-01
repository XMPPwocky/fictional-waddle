import Mathlib

/-!
# B01 — PT-symmetric gain/loss dimer (proofs)

`H = !![ω + iγ, κ; κ, ω - iγ]` over `ℂ` with `ω γ κ : ℝ`. Site 0 has gain `γ`, site 1 has
loss `γ`, and the coupling is `κ`. Theorem statements are textually identical to
`B01_pt_dimer.statements.lean`. Helper lemmas found only here: `det_formula`, `pseudoNorm_eq`,
`N_eq`, `re_im_of_sq`. The `example`s at the end are also found only here.

**Proved:**
1. `det (H - μ•1) = 0 ↔ (μ - ω)² = κ² - γ²` (`det_eq_zero_iff`).
2. Unbroken phase `γ² < κ²`: `ω ± √(κ² - γ²)` are distinct real roots, and *every* root
   has zero imaginary part (`unbroken`).
3. Broken phase `κ² < γ²`: `ω ± i√(γ² - κ²)` are roots with nonzero imaginary part, and
   *every* root is non-real (`broken`).
4. Exceptional point `γ² = κ²`, `κ ≠ 0`: `N = H - ω•1` satisfies `N * N = 0` and `N ≠ 0`
   (`ep_nilpotent`). `ω` is the only eigenvalue, and `ker N` is exactly the line spanned by
   `(κ, -iγ)` (`ep_eigenspace`). There is no invertible `P` with `P⁻¹ H P` diagonal
   (`ep_not_diagonalizable`).
5. With `P = !![0,1;1,0]`: `Hᴴ P = P H` (`pseudo_hermitian`). Hence
   `⟨Hψ, Pψ⟩ = ⟨ψ, P Hψ⟩` (`pseudo_identity`). Along any differentiable solution of
   `ψ' = -i H ψ`, the pseudo-norm `ψᴴ P ψ` has zero derivative and is constant
   (`pseudoNorm_conserved`).
6. (Added by second agent.) Non-vacuity of (5): `exp(-i t H) ψ₀` is such a solution for every
   `ψ₀` (`propagator_solves`), so it conserves the pseudo-norm (`propagator_conserves`).
   Here `exp` is `NormedSpace.exp` on matrices. The matrix norm (`linftyOp`) appears only
   inside the proof; the statement uses the default instances.
7. (Added by second agent: the one theorem "going up".) `Aᴴ P = P A` iff
   `A = !![ω + iγ, κ₁; κ₂, ω - iγ]` with all four parameters real (`pseudo_hermitian_iff`).
   The symmetric dimer is the slice `κ₁ = κ₂`.

**Second-agent audit:** the file compiles with no errors or warnings, and the statements match
the statements file. No original statement was changed. Items 6–7 and the examples were added
to both files (examples to this file only).

**Interpretation (not proved):** "PT symmetry" (parity = `P`, time reversal = complex
conjugation) is not formalised as an antilinear symmetry here. Only the matrix identity
`Hᴴ P = P H` (pseudo-Hermiticity) is. Calling the regimes "unbroken"/"broken" and the
`γ² = κ²` point an "exceptional point" (where eigenvalues *and* eigenvectors coalesce) is
the standard physics reading of items 2–4. The conserved quantity `ψᴴ P ψ = 2 Re(ψ̄₀ψ₁)` is
an indefinite form, not the norm `‖ψ‖²`. The norm is *not* conserved when `γ ≠ 0`, but this
file does not prove that. No claim is made about the case `κ = 0`.
-/

open Complex Matrix

namespace B01PTDimer

/-- The PT dimer Hamiltonian. -/
noncomputable def H (ω γ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(ω : ℂ) + γ * I, κ; κ, (ω : ℂ) - γ * I]

/-- The parity (site-swap) matrix. -/
def Pm : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The pseudo-norm `ψᴴ P ψ`. -/
def pseudoNorm (ψ : Fin 2 → ℂ) : ℂ := star ψ ⬝ᵥ (Pm *ᵥ ψ)

/-- Helper: `det (H - μ) = (μ - ω)² - (κ² - γ²)`. -/
theorem det_formula (ω γ κ : ℝ) (μ : ℂ) :
    (H ω γ κ - μ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det =
      (μ - ω) ^ 2 - ((κ : ℂ) ^ 2 - (γ : ℂ) ^ 2) := by
  rw [Matrix.det_fin_two]
  simp [H]
  linear_combination (-(γ : ℂ) ^ 2) * I_sq

/-- Helper: in coordinates, `ψᴴ P ψ = ψ̄₀ ψ₁ + ψ̄₁ ψ₀`. -/
theorem pseudoNorm_eq (v : Fin 2 → ℂ) :
    pseudoNorm v = star (v 0) * v 1 + star (v 1) * v 0 := by
  simp [pseudoNorm, Pm, dotProduct, mulVec, Fin.sum_univ_two]

/-- (5a) Pseudo-Hermiticity: `Hᴴ P = P H`. -/
theorem pseudo_hermitian (ω γ κ : ℝ) : (H ω γ κ)ᴴ * Pm = Pm * H ω γ κ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, Pm, conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]

/-- (5b) The algebraic conservation identity `⟨Hψ, Pψ⟩ = ⟨ψ, P Hψ⟩`. -/
theorem pseudo_identity (ω γ κ : ℝ) (ψ : Fin 2 → ℂ) :
    star (H ω γ κ *ᵥ ψ) ⬝ᵥ (Pm *ᵥ ψ) = star ψ ⬝ᵥ (Pm *ᵥ (H ω γ κ *ᵥ ψ)) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    pseudo_hermitian, ← Matrix.mulVec_mulVec]


/-- (1) Eigenvalue equation. -/
theorem det_eq_zero_iff (ω γ κ : ℝ) (μ : ℂ) :
    (H ω γ κ - μ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 ↔
      (μ - ω) ^ 2 = (κ : ℂ) ^ 2 - (γ : ℂ) ^ 2 := by
  rw [det_formula, sub_eq_zero]

/-- Real and imaginary parts of `(μ - ω)^2 = c` for real `c`. -/
theorem re_im_of_sq (ω c : ℝ) (μ : ℂ) (h : (μ - ω) ^ 2 = (c : ℂ)) :
    (μ.re - ω) * (μ.re - ω) - μ.im * μ.im = c ∧ (μ.re - ω) * μ.im = 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sq] at hre him
  refine ⟨hre, ?_⟩
  linarith

/-- (2) Unbroken phase: the two eigenvalues `ω ± √(κ² - γ²)` are real, distinct,
and every eigenvalue is real. -/
theorem unbroken (ω γ κ : ℝ) (h : γ ^ 2 < κ ^ 2) :
    (H ω γ κ - ((ω + Real.sqrt (κ ^ 2 - γ ^ 2) : ℝ) : ℂ) • 1).det = 0 ∧
    (H ω γ κ - ((ω - Real.sqrt (κ ^ 2 - γ ^ 2) : ℝ) : ℂ) • 1).det = 0 ∧
    ω + Real.sqrt (κ ^ 2 - γ ^ 2) ≠ ω - Real.sqrt (κ ^ 2 - γ ^ 2) ∧
    ∀ μ : ℂ, (H ω γ κ - μ • 1).det = 0 → μ.im = 0 := by
  have hpos : 0 < κ ^ 2 - γ ^ 2 := by linarith
  set s := Real.sqrt (κ ^ 2 - γ ^ 2) with hs_def
  have hsR : s ^ 2 = κ ^ 2 - γ ^ 2 := Real.sq_sqrt hpos.le
  have hs : (s : ℂ) ^ 2 = (κ : ℂ) ^ 2 - (γ : ℂ) ^ 2 := by exact_mod_cast hsR
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [det_formula]; push_cast; linear_combination hs
  · rw [det_formula]; push_cast; linear_combination hs
  · intro h'; linarith
  · intro μ hμ
    rw [det_eq_zero_iff] at hμ
    have hμ' : (μ - ω) ^ 2 = ((κ ^ 2 - γ ^ 2 : ℝ) : ℂ) := by rw [hμ]; push_cast; ring
    obtain ⟨hre, him⟩ := re_im_of_sq ω _ μ hμ'
    rcases mul_eq_zero.mp him with ha | hb
    · rw [ha] at hre; nlinarith [mul_self_nonneg μ.im]
    · exact hb

/-- (3) Broken phase: eigenvalues `ω ± i √(γ² - κ²)`, with nonzero imaginary part,
and every eigenvalue is non-real. -/
theorem broken (ω γ κ : ℝ) (h : κ ^ 2 < γ ^ 2) :
    (H ω γ κ - ((ω : ℂ) + Real.sqrt (γ ^ 2 - κ ^ 2) * I) • 1).det = 0 ∧
    (H ω γ κ - ((ω : ℂ) - Real.sqrt (γ ^ 2 - κ ^ 2) * I) • 1).det = 0 ∧
    ((ω : ℂ) + Real.sqrt (γ ^ 2 - κ ^ 2) * I).im ≠ 0 ∧
    ((ω : ℂ) - Real.sqrt (γ ^ 2 - κ ^ 2) * I).im ≠ 0 ∧
    ∀ μ : ℂ, (H ω γ κ - μ • 1).det = 0 → μ.im ≠ 0 := by
  have hpos : 0 < γ ^ 2 - κ ^ 2 := by linarith
  set s := Real.sqrt (γ ^ 2 - κ ^ 2) with hs_def
  have hsR : s ^ 2 = γ ^ 2 - κ ^ 2 := Real.sq_sqrt hpos.le
  have hs : (s : ℂ) ^ 2 = (γ : ℂ) ^ 2 - (κ : ℂ) ^ 2 := by exact_mod_cast hsR
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [det_formula]; linear_combination I ^ 2 * hs + ((γ : ℂ) ^ 2 - κ ^ 2) * I_sq
  · rw [det_formula]; linear_combination I ^ 2 * hs + ((γ : ℂ) ^ 2 - κ ^ 2) * I_sq
  · simp; exact hs0.ne'
  · simp; exact hs0.ne'
  · intro μ hμ him0
    rw [det_eq_zero_iff] at hμ
    have hμ' : (μ - ω) ^ 2 = ((κ ^ 2 - γ ^ 2 : ℝ) : ℂ) := by rw [hμ]; push_cast; ring
    obtain ⟨hre, -⟩ := re_im_of_sq ω _ μ hμ'
    rw [him0] at hre
    nlinarith [mul_self_nonneg (μ.re - ω)]

/-- Helper: `N = H - ω = !![iγ, κ; κ, -iγ]`. -/
theorem N_eq (ω γ κ : ℝ) :
    H ω γ κ - (ω : ℂ) • 1 = !![(γ : ℂ) * I, κ; κ, -((γ : ℂ) * I)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H]

/-- (4a) Exceptional point: `N = H - ω` is nonzero and squares to zero. -/
theorem ep_nilpotent (ω γ κ : ℝ) (h : γ ^ 2 = κ ^ 2) (hκ : κ ≠ 0) :
    (H ω γ κ - (ω : ℂ) • 1) * (H ω γ κ - (ω : ℂ) • 1) = 0 ∧
    H ω γ κ - (ω : ℂ) • 1 ≠ 0 := by
  have hC : (γ : ℂ) ^ 2 = (κ : ℂ) ^ 2 := by exact_mod_cast h
  rw [N_eq]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (γ : ℂ) ^ 2 * I_sq - hC
    · ring
    · ring
    · linear_combination (γ : ℂ) ^ 2 * I_sq - hC
  · intro hN
    have := congrFun (congrFun hN 0) 1
    simp at this
    exact hκ this

/-- (4b) Exceptional point: `ω` is the only eigenvalue and its eigenspace is the line
spanned by `(κ, -iγ)`. -/
theorem ep_eigenspace (ω γ κ : ℝ) (h : γ ^ 2 = κ ^ 2) (hκ : κ ≠ 0) :
    (∀ μ : ℂ, (H ω γ κ - μ • 1).det = 0 ↔ μ = ω) ∧
    (H ω γ κ - (ω : ℂ) • 1) *ᵥ ![(κ : ℂ), -(γ * I)] = 0 ∧
    ∀ v : Fin 2 → ℂ, (H ω γ κ - (ω : ℂ) • 1) *ᵥ v = 0 →
      ∃ c : ℂ, v = c • ![(κ : ℂ), -(γ * I)] := by
  have hC : (γ : ℂ) ^ 2 = (κ : ℂ) ^ 2 := by exact_mod_cast h
  have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  refine ⟨?_, ?_, ?_⟩
  · intro μ
    rw [det_eq_zero_iff, ← hC, sub_self, pow_eq_zero_iff two_ne_zero, sub_eq_zero]
  · rw [N_eq]
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]
    · ring
    · linear_combination (γ : ℂ) ^ 2 * I_sq - hC
  · intro v hv
    rw [N_eq] at hv
    have h0 := congrFun hv 0
    simp [mulVec, dotProduct, Fin.sum_univ_two] at h0
    refine ⟨v 0 / κ, ?_⟩
    ext i
    fin_cases i
    · simp; field_simp
    · simp
      field_simp
      linear_combination h0

/-- (4c) Exceptional point: `H` is not diagonalizable. -/
theorem ep_not_diagonalizable (ω γ κ : ℝ) (h : γ ^ 2 = κ ^ 2) (hκ : κ ≠ 0) :
    ¬ ∃ (P : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℂ),
      IsUnit P.det ∧ P⁻¹ * H ω γ κ * P = Matrix.diagonal d := by
  rintro ⟨P, d, hP, hD⟩
  obtain ⟨hNN, hN0⟩ := ep_nilpotent ω γ κ h hκ
  set N := H ω γ κ - (ω : ℂ) • 1 with hN_def
  have hPinvP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hPPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hDN : P⁻¹ * N * P = Matrix.diagonal (fun i => d i - ω) := by
    rw [hN_def, Matrix.mul_sub, Matrix.sub_mul, hD, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hPinvP]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal, hij]
  have hsq : (P⁻¹ * N * P) * (P⁻¹ * N * P) = 0 := by
    calc (P⁻¹ * N * P) * (P⁻¹ * N * P) = P⁻¹ * N * (P * P⁻¹) * N * P := by
          simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (N * N) * P := by rw [hPPinv]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 0 := by rw [hNN]; simp
  rw [hDN, Matrix.diagonal_mul_diagonal] at hsq
  have hzero : ∀ i, d i - ω = 0 := by
    intro i
    have := congrFun (congrFun hsq i) i
    simp at this
    exact this
  have hD0 : P⁻¹ * N * P = 0 := by
    rw [hDN]
    ext i j
    simp [Matrix.diagonal, hzero]
  apply hN0
  calc N = P * (P⁻¹ * N * P) * P⁻¹ := by
        simp only [← Matrix.mul_assoc, hPPinv, Matrix.one_mul]
        rw [Matrix.mul_assoc, hPPinv, Matrix.mul_one]
    _ = 0 := by rw [hD0]; simp

/-- (5c) Calculus version: along any solution of `ψ' = -i H ψ` the pseudo-norm has zero
derivative and is constant in time. -/
theorem pseudoNorm_conserved (ω γ κ : ℝ) (ψ : ℝ → Fin 2 → ℂ)
    (hψ : ∀ t, HasDerivAt ψ (-(I • (H ω γ κ *ᵥ ψ t))) t) :
    (∀ t, HasDerivAt (fun s => pseudoNorm (ψ s)) 0 t) ∧
    ∀ s t, pseudoNorm (ψ s) = pseudoNorm (ψ t) := by
  have hd : ∀ t, HasDerivAt (fun s => pseudoNorm (ψ s)) 0 t := by
    intro t
    have hc : ∀ i, HasDerivAt (fun s => ψ s i) ((-(I • (H ω γ κ *ᵥ ψ t))) i) t :=
      fun i => (hasDerivAt_pi.mp (hψ t)) i
    simp only [pseudoNorm_eq]
    have := (((hc 0).star.mul (hc 1)).add ((hc 1).star.mul (hc 0)))
    convert this using 1
    simp [H, dotProduct, Fin.sum_univ_two]
    ring
  refine ⟨hd, fun s t => ?_⟩
  have hdiff : Differentiable ℝ (fun s => pseudoNorm (ψ s)) :=
    fun x => (hd x).differentiableAt
  exact is_const_of_deriv_eq_zero hdiff (fun x => (hd x).deriv) s t



/-- (6a, added by second agent; non-vacuity of (5c)) The propagator `ψ(t) = exp(-i t H) ψ₀`
equals `ψ₀` at `t = 0` and satisfies `ψ' = -i H ψ` in exactly the `HasDerivAt` form that
`pseudoNorm_conserved` assumes. So that theorem's hypothesis holds for every initial state. -/
theorem propagator_solves (ω γ κ : ℝ) (ψ0 : Fin 2 → ℂ) :
    NormedSpace.exp ((0 : ℝ) • (-(I • H ω γ κ))) *ᵥ ψ0 = ψ0 ∧
    ∀ t : ℝ, HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (-(I • H ω γ κ))) *ᵥ ψ0)
       (-(I • (H ω γ κ *ᵥ (NormedSpace.exp (t • (-(I • H ω γ κ))) *ᵥ ψ0)))) t := by
  let _ : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
  refine ⟨by simp [NormedSpace.exp_zero], fun t => ?_⟩
  set A : Matrix (Fin 2) (Fin 2) ℂ := -(I • H ω γ κ)
  let L : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] (Fin 2 → ℂ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M *ᵥ ψ0
        map_add' := fun M N => Matrix.add_mulVec M N ψ0
        map_smul' := fun c M => by simp [Matrix.smul_mulVec] }
  have h1 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t
  have h3 : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) *ᵥ ψ0)
      (L (A * NormedSpace.exp (t • A))) t := L.hasFDerivAt.comp_hasDerivAt t h1
  convert h3 using 1
  show _ = (A * NormedSpace.exp (t • A)) *ᵥ ψ0
  rw [← Matrix.mulVec_mulVec]
  simp only [A, Matrix.neg_mulVec, Matrix.smul_mulVec]

/-- (6b, added by second agent) Corollary: `exp(-i t H) ψ₀` has the same pseudo-norm as
`ψ₀` for all `t`. -/
theorem propagator_conserves (ω γ κ : ℝ) (ψ0 : Fin 2 → ℂ) (t : ℝ) :
    pseudoNorm (NormedSpace.exp (t • (-(I • H ω γ κ))) *ᵥ ψ0) = pseudoNorm ψ0 := by
  have h := (pseudoNorm_conserved ω γ κ _ (propagator_solves ω γ κ ψ0).2).2 t 0
  rw [h, (propagator_solves ω γ κ ψ0).1]

/-- (7, added by second agent: the ONE theorem "going up") The general case. A complex
`2×2` matrix `A` satisfies `Aᴴ P = P A` iff it is a gain/loss dimer with possibly *unequal*
real couplings: `A = !![ω + iγ, κ₁; κ₂, ω - iγ]` with `ω γ κ₁ κ₂ : ℝ`. So the symmetric dimer
`H ω γ κ` is the slice `κ₁ = κ₂` of the full class of `Pm`-pseudo-Hermitian `2×2` matrices. -/
theorem pseudo_hermitian_iff (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Aᴴ * Pm = Pm * A ↔
      ∃ ω γ κ₁ κ₂ : ℝ, A = !![(ω : ℂ) + γ * I, κ₁; κ₂, (ω : ℂ) - γ * I] := by
  constructor
  · intro h
    have e : ∀ i j, (Aᴴ * Pm) i j = (Pm * A) i j := fun i j => by rw [h]
    have e00 := e 0 0
    have e01 := e 0 1
    have e10 := e 1 0
    have e11 := e 1 1
    simp [Pm, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply] at e00 e01 e10 e11
    refine ⟨(A 0 0).re, (A 0 0).im, (A 0 1).re, (A 1 0).re, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simp; exact (Complex.conj_eq_iff_re.mp e11).symm
    · simp; exact (Complex.conj_eq_iff_re.mp e00).symm
    · simp
      rw [← e01]
      apply Complex.ext <;> simp
  · rintro ⟨ω, γ, κ₁, κ₂, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Pm, conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]

/-! ### Concrete examples (non-vacuity of each regime; proof file only)
* unbroken, `ω=0, γ=1, κ=2`: `√3` is a real eigenvalue.
* broken, `ω=0, γ=2, κ=1`: `i√3` is an eigenvalue and is not real.
* exceptional point, `ω=0, γ=κ=1`: `H` is not diagonalizable.
* dynamics: starting from `(1,1)`, the pseudo-norm stays `2` for all `t`. -/

example : (H 0 1 2 - ((Real.sqrt 3 : ℝ) : ℂ) • 1).det = 0 := by
  have := (unbroken 0 1 2 (by norm_num)).1
  norm_num at this ⊢
  exact this

example : (H 0 2 1 - (Real.sqrt 3 * I) • 1).det = 0 ∧ (Real.sqrt 3 * I).im ≠ 0 := by
  have h := broken 0 2 1 (by norm_num)
  norm_num at h ⊢
  exact h.1

example : ¬ ∃ (P : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℂ),
    IsUnit P.det ∧ P⁻¹ * H 0 1 1 * P = Matrix.diagonal d :=
  ep_not_diagonalizable 0 1 1 (by norm_num) one_ne_zero

example (t : ℝ) : pseudoNorm (NormedSpace.exp (t • (-(I • H 0 1 2))) *ᵥ ![1, 1]) = 2 := by
  rw [propagator_conserves, pseudoNorm_eq]; norm_num

end B01PTDimer
