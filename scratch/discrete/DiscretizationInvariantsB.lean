import Mathlib

/-!
# Discretization invariants of the harmonic oscillator

Flow `q' = p, p' = -q`, conserving `q² + p²`. Step size `η > 0`.

* Explicit Euler:   `(q, p) ↦ (q + η p, p - η q)`.
* Implicit Euler:   `(q, p) ↦ ((q + η p)/(1 + η²), (p - η q)/(1 + η²))`, the unique solution of
  `q₁ = q + η p₁`, `p₁ = p - η q₁`.
* Symplectic Euler: `p₁ = p - η q`, `q₁ = q + η p₁`, i.e.
  `(q, p) ↦ ((1 - η²) q + η p, p - η q)`.

PROVED
* `explicitMatrix_det`, `implicitMatrix_det`, `symplecticMatrix_det`: the step matrices have
  determinants `1 + η²`, `1 / (1 + η²)` and `1`; the matrices act as the step maps
  (`explicitMatrix_mulVec`, `implicitMatrix_mulVec`, `symplecticMatrix_mulVec`).
* `implicit_solves`, `implicit_unique`: the closed form solves the implicit equations and is
  the only solution.
* `explicit_energy`, `implicit_energy`: one explicit step multiplies `q² + p²` by exactly
  `1 + η²`, one implicit step by exactly `1 / (1 + η²)`; `explicit_energy_iter`,
  `implicit_energy_iter` give the `n`-step factors `(1 + η²)^n` and `(1 + η²)^(-n)`.
* `symplectic_modified_conserved`: symplectic Euler exactly conserves
  `Q_η(q, p) = q² + p² - η q p` (coefficients `a = 1, b = -η, c = 1`; the sign of `b` is
  negative, so `q² + p² + η q p` is not conserved: `not_conserved_plus`).
  `symplectic_modified_conserved_iter`: conservation along every orbit.
* `symplectic_modified_unique`: for `η > 0`, any quadratic form `a q² + b q p + c p²`
  conserved by the symplectic step is a scalar multiple of `Q_η`, i.e. `b = -η a`, `c = a`.
* `modifiedForm_tendsto`: `Q_η(q, p) → q² + p²` as `η → 0`.
* `modifiedForm_posDef`, `modifiedForm_lower`: for `0 < η < 2`, `Q_η` is positive definite,
  with `(1 - η/2)(q² + p²) ≤ Q_η(q, p)`.
* `symplectic_bounded`: for `0 < η < 2`, every symplectic Euler orbit satisfies
  `q_n² + p_n² ≤ Q_η(q_0, p_0) / (1 - η/2)` for all `n` (`symplectic_bounded_exists`: some
  uniform bound exists).
* `modifiedForm_not_posDef`: for `η ≥ 2`, `Q_η` is not positive definite.

INTERPRETED
* "Reducing to `q² + p²` as `η → 0`" is formalized as pointwise convergence of the form,
  `modifiedForm_tendsto`, together with the coefficients being `(1, -η, 1)`.
* "Orbits stay bounded forever" is formalized as the uniform bound `symplectic_bounded` on
  `q² + p²` along the iterates of the step map.
-/

namespace DiscretizationInvariantsB

open Matrix Filter Topology

/-- Squared norm `q² + p²`. -/
def energy (x : ℝ × ℝ) : ℝ := x.1 ^ 2 + x.2 ^ 2

/-- Explicit Euler step. -/
def explicitStep (η : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (x.1 + η * x.2, x.2 - η * x.1)

/-- Implicit Euler step, closed form. -/
noncomputable def implicitStep (η : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ((x.1 + η * x.2) / (1 + η ^ 2), (x.2 - η * x.1) / (1 + η ^ 2))

/-- Symplectic Euler step: `p₁ = p - η q`, then `q₁ = q + η p₁`. -/
def symplecticStep (η : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  let p₁ := x.2 - η * x.1
  (x.1 + η * p₁, p₁)

/-- The modified quadratic form conserved by symplectic Euler. -/
def modifiedForm (η : ℝ) (x : ℝ × ℝ) : ℝ := x.1 ^ 2 + x.2 ^ 2 - η * x.1 * x.2

/-- General quadratic form `a q² + b q p + c p²`. -/
def quadForm (a b c : ℝ) (x : ℝ × ℝ) : ℝ := a * x.1 ^ 2 + b * x.1 * x.2 + c * x.2 ^ 2

/-! ### Matrices and determinants -/

/-- Explicit Euler matrix, acting on `(q, p)`. -/
def explicitMatrix (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, η; -η, 1]

/-- Implicit Euler matrix. -/
noncomputable def implicitMatrix (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / (1 + η ^ 2), η / (1 + η ^ 2); -η / (1 + η ^ 2), 1 / (1 + η ^ 2)]

/-- Symplectic Euler matrix. -/
def symplecticMatrix (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 - η ^ 2, η; -η, 1]

theorem explicitMatrix_mulVec (η q p : ℝ) :
    explicitMatrix η *ᵥ ![q, p] = ![(explicitStep η (q, p)).1, (explicitStep η (q, p)).2] := by
  ext i; fin_cases i
  · simp [explicitMatrix, explicitStep, mulVec, dotProduct, Fin.sum_univ_two]
  · simp [explicitMatrix, explicitStep, mulVec, dotProduct, Fin.sum_univ_two]; ring

theorem implicitMatrix_mulVec (η q p : ℝ) :
    implicitMatrix η *ᵥ ![q, p] = ![(implicitStep η (q, p)).1, (implicitStep η (q, p)).2] := by
  ext i; fin_cases i <;> simp [implicitMatrix, implicitStep, mulVec, dotProduct, Fin.sum_univ_two]
    <;> ring

theorem symplecticMatrix_mulVec (η q p : ℝ) :
    symplecticMatrix η *ᵥ ![q, p] =
      ![(symplecticStep η (q, p)).1, (symplecticStep η (q, p)).2] := by
  ext i; fin_cases i <;>
    simp [symplecticMatrix, symplecticStep, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem explicitMatrix_det (η : ℝ) : (explicitMatrix η).det = 1 + η ^ 2 := by
  rw [explicitMatrix, det_fin_two_of]; ring

theorem implicitMatrix_det (η : ℝ) : (implicitMatrix η).det = 1 / (1 + η ^ 2) := by
  have h : (1 + η ^ 2) ≠ 0 := by positivity
  rw [implicitMatrix, det_fin_two_of]
  field_simp
  ring

theorem symplecticMatrix_det (η : ℝ) : (symplecticMatrix η).det = 1 := by
  rw [symplecticMatrix, det_fin_two_of]; ring

/-! ### Implicit Euler is well defined -/

theorem implicit_solves (η q p : ℝ) :
    (implicitStep η (q, p)).1 = q + η * (implicitStep η (q, p)).2 ∧
    (implicitStep η (q, p)).2 = p - η * (implicitStep η (q, p)).1 := by
  have h : (1 + η ^ 2) ≠ 0 := by positivity
  simp only [implicitStep]
  constructor <;> field_simp <;> ring

theorem implicit_unique (η q p q₁ p₁ : ℝ) (h1 : q₁ = q + η * p₁) (h2 : p₁ = p - η * q₁) :
    (q₁, p₁) = implicitStep η (q, p) := by
  have h : (1 + η ^ 2) ≠ 0 := by positivity
  have hq : q₁ * (1 + η ^ 2) = q + η * p := by
    have : q₁ = q + η * (p - η * q₁) := by rw [← h2]; exact h1
    linear_combination this
  have hp : p₁ * (1 + η ^ 2) = p - η * q := by
    have : p₁ = p - η * (q + η * p₁) := by rw [← h1]; exact h2
    linear_combination this
  simp only [implicitStep, Prod.mk.injEq]
  constructor
  · rw [eq_div_iff h]; exact hq
  · rw [eq_div_iff h]; exact hp

/-! ### Energy growth and decay -/

theorem explicit_energy (η : ℝ) (x : ℝ × ℝ) :
    energy (explicitStep η x) = (1 + η ^ 2) * energy x := by
  simp only [energy, explicitStep]; ring

theorem implicit_energy (η : ℝ) (x : ℝ × ℝ) :
    energy (implicitStep η x) = energy x / (1 + η ^ 2) := by
  have h : (1 + η ^ 2) ≠ 0 := by positivity
  simp only [energy, implicitStep]
  field_simp
  ring

theorem explicit_energy_iter (η : ℝ) (x : ℝ × ℝ) (n : ℕ) :
    energy ((explicitStep η)^[n] x) = (1 + η ^ 2) ^ n * energy x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, explicit_energy, pow_succ]; ring

theorem implicit_energy_iter (η : ℝ) (x : ℝ × ℝ) (n : ℕ) :
    energy ((implicitStep η)^[n] x) = energy x / (1 + η ^ 2) ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, implicit_energy, div_div, ← pow_succ']

/-! ### Symplectic Euler: the modified invariant -/

theorem modifiedForm_eq_quadForm (η : ℝ) (x : ℝ × ℝ) :
    modifiedForm η x = quadForm 1 (-η) 1 x := by
  simp only [modifiedForm, quadForm]; ring

theorem symplectic_modified_conserved (η : ℝ) (x : ℝ × ℝ) :
    modifiedForm η (symplecticStep η x) = modifiedForm η x := by
  simp only [modifiedForm, symplecticStep]; ring

theorem symplectic_modified_conserved_iter (η : ℝ) (x : ℝ × ℝ) (n : ℕ) :
    modifiedForm η ((symplecticStep η)^[n] x) = modifiedForm η x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply, ih, symplectic_modified_conserved]

/-- The form `q² + p² + η q p` is not conserved by symplectic Euler for `η ≠ 0`. -/
theorem not_conserved_plus (η : ℝ) (hη : η ≠ 0) :
    ¬ ∀ x : ℝ × ℝ, quadForm 1 η 1 (symplecticStep η x) = quadForm 1 η 1 x := by
  intro h
  have h2 := h (0, 1)
  simp only [quadForm, symplecticStep] at h2
  have : η ^ 2 = 0 := by linear_combination h2 / 2
  exact hη (pow_eq_zero_iff (by norm_num) |>.mp this)

/-- Every conserved quadratic form is a multiple of `q² + p² - η q p`. -/
theorem symplectic_modified_unique (η : ℝ) (hη : 0 < η) (a b c : ℝ)
    (h : ∀ x : ℝ × ℝ, quadForm a b c (symplecticStep η x) = quadForm a b c x) :
    b = -η * a ∧ c = a := by
  have h1 := h (1, 0)
  have h2 := h (0, 1)
  have h3 := h (1, 1)
  simp only [quadForm, symplecticStep] at h1 h2 h3
  have e2 : η * (a * η + b) = 0 := by linear_combination h2
  have hb : b = -η * a := by
    have := (mul_eq_zero.mp e2).resolve_left hη.ne'
    linear_combination this
  subst hb
  have e1 : η ^ 2 * (c - a) = 0 := by linear_combination h1
  have hc : c - a = 0 := (mul_eq_zero.mp e1).resolve_left (by positivity)
  exact ⟨rfl, by linarith⟩

theorem modifiedForm_tendsto (x : ℝ × ℝ) :
    Tendsto (fun η : ℝ => modifiedForm η x) (𝓝[>] 0) (𝓝 (energy x)) := by
  have hc : Continuous (fun η : ℝ => modifiedForm η x) := by
    unfold modifiedForm; fun_prop
  have : modifiedForm 0 x = energy x := by simp [modifiedForm, energy]
  rw [← this]
  exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem modifiedForm_lower (η : ℝ) (hη : 0 ≤ η) (x : ℝ × ℝ) :
    (1 - η / 2) * energy x ≤ modifiedForm η x := by
  simp only [energy, modifiedForm]
  have h1 : 2 * (x.1 * x.2) ≤ x.1 ^ 2 + x.2 ^ 2 := by nlinarith [sq_nonneg (x.1 - x.2)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hη]

theorem modifiedForm_posDef (η : ℝ) (hη0 : 0 < η) (hη2 : η < 2) (x : ℝ × ℝ) (hx : x ≠ 0) :
    0 < modifiedForm η x := by
  have hE : 0 < energy x := by
    rcases x with ⟨q, p⟩
    simp only [energy]
    by_contra hle
    push Not at hle
    have hq : q = 0 := by nlinarith [sq_nonneg q, sq_nonneg p]
    have hp : p = 0 := by nlinarith [sq_nonneg q, sq_nonneg p]
    exact hx (by simp [hq, hp])
  have := modifiedForm_lower η hη0.le x
  have hk : 0 < 1 - η / 2 := by linarith
  nlinarith [mul_pos hk hE]

theorem modifiedForm_not_posDef (η : ℝ) (hη : 2 ≤ η) :
    ∃ x : ℝ × ℝ, x ≠ 0 ∧ modifiedForm η x ≤ 0 := by
  refine ⟨(1, 1), by simp, ?_⟩
  simp only [modifiedForm]; nlinarith

theorem symplectic_bounded (η : ℝ) (hη0 : 0 < η) (hη2 : η < 2) (x : ℝ × ℝ) (n : ℕ) :
    energy ((symplecticStep η)^[n] x) ≤ modifiedForm η x / (1 - η / 2) := by
  have hk : 0 < 1 - η / 2 := by linarith
  rw [le_div_iff₀ hk, ← symplectic_modified_conserved_iter η x n, mul_comm]
  exact modifiedForm_lower η hη0.le _

theorem symplectic_bounded_exists (η : ℝ) (hη0 : 0 < η) (hη2 : η < 2) (x : ℝ × ℝ) :
    ∃ C : ℝ, ∀ n : ℕ, energy ((symplecticStep η)^[n] x) ≤ C :=
  ⟨_, symplectic_bounded η hη0 hη2 x⟩

end DiscretizationInvariantsB
