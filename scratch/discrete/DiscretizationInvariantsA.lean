import Mathlib

/-!
# Discretization invariants for the rotation flow `q' = p, p' = -q`

The continuous flow conserves `q² + p²`. We study three one-step discretizations with step
size `η > 0`, acting on states `(q, p) : ℝ × ℝ`:

* explicit Euler   `(q, p) ↦ (q + η p, p - η q)`;
* implicit Euler   `(q, p) ↦ ((q + η p)/(1 + η²), (p - η q)/(1 + η²))`, the unique solution of
  `q₁ = q + η p₁`, `p₁ = p - η q₁`;
* symplectic Euler `p₁ = p - η q`, `q₁ = q + η p₁`.

PROVED
* `implicit_unique`, `implicitEuler_solves`: the implicit-Euler state is the unique solution of
  the implicit equations (for every real `η`).
* `explicit_eq_mulVec`, `implicit_eq_mulVec`, `symplectic_eq_mulVec`: each map is the linear map
  of the matrix `explicitMat η`, `implicitMat η`, `symplecticMat η`.
* `det_explicitMat : det = 1 + η²`, `det_implicitMat : det = 1/(1 + η²)`,
  `det_symplecticMat : det = 1`.
* `explicit_energy`, `implicit_energy`: one step multiplies `q² + p²` by exactly `1 + η²`,
  resp. `1/(1 + η²)`; `explicit_energy_iter`, `implicit_energy_iter`: after `n` steps by the
  `n`-th power; `explicit_energy_unbounded`: explicit-Euler energy is unbounded along every
  nonzero orbit when `η ≠ 0`.
* `symplectic_conserves`: `modForm η (q, p) = q² - η q p + p²` is exactly conserved by
  symplectic Euler (note the sign: `q² + p² + η q p` is NOT conserved, see
  `plus_form_not_conserved`). `symplectic_conserves_iter`: conserved along orbits.
* `conserved_form_iff`: for `η ≠ 0`, a quadratic form `a q² + b q p + c p²` is conserved by
  symplectic Euler iff `b = -η a` and `c = a`; so `modForm η` is the unique conserved quadratic
  form up to scaling.
* `modForm_tendsto`: `modForm η x → q² + p²` as `η → 0`.
* `modForm_posDef_iff`: for `η > 0`, `modForm η` is positive definite iff `η < 2`.
* `modForm_lower`: `(1 - η/2)(q² + p²) ≤ modForm η (q, p)` for `η ≥ 0`.
* `symplectic_bounded`: for `0 < η < 2`, every symplectic-Euler orbit satisfies
  `q_n² + p_n² ≤ modForm η x₀ / (1 - η/2)` for all `n`.

INTERPRETED
* "Orbit stays bounded forever" is stated as a uniform bound on `q_n² + p_n²` over all `n : ℕ`,
  with `n`-fold iteration `f^[n]`.
* "Reduces to `q² + p²` as `η → 0`" is stated as pointwise convergence of `modForm η x` along
  `𝓝 0`, plus the coefficients `(1, -η, 1) → (1, 0, 1)` being evident from the definition.
-/

namespace DiscretizationInvariantsA

open Matrix Filter Topology

/-- Explicit Euler step. -/
def explicitEuler (η : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (x.1 + η * x.2, x.2 - η * x.1)

/-- Implicit Euler step, in closed form. -/
noncomputable def implicitEuler (η : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ((x.1 + η * x.2) / (1 + η ^ 2), (x.2 - η * x.1) / (1 + η ^ 2))

/-- Symplectic Euler step: `p₁ = p - η q`, `q₁ = q + η p₁`. -/
def symplecticEuler (η : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 + η * (x.2 - η * x.1), x.2 - η * x.1)

/-- The conserved quantity of the continuous flow. -/
def energy (x : ℝ × ℝ) : ℝ := x.1 ^ 2 + x.2 ^ 2

/-- A general quadratic form `a q² + b q p + c p²`. -/
def quadForm (a b c : ℝ) (x : ℝ × ℝ) : ℝ := a * x.1 ^ 2 + b * x.1 * x.2 + c * x.2 ^ 2

/-- The modified quadratic form conserved by symplectic Euler: `q² - η q p + p²`. -/
def modForm (η : ℝ) (x : ℝ × ℝ) : ℝ := quadForm 1 (-η) 1 x

lemma one_add_sq_pos (η : ℝ) : 0 < 1 + η ^ 2 := by positivity

/-! ### Implicit Euler is the unique solution of the implicit equations -/

theorem implicitEuler_solves (η : ℝ) (x : ℝ × ℝ) :
    (implicitEuler η x).1 = x.1 + η * (implicitEuler η x).2 ∧
    (implicitEuler η x).2 = x.2 - η * (implicitEuler η x).1 := by
  have h := (one_add_sq_pos η).ne'
  simp only [implicitEuler]
  constructor <;> field_simp <;> ring

theorem implicit_unique (η : ℝ) (x y : ℝ × ℝ)
    (h1 : y.1 = x.1 + η * y.2) (h2 : y.2 = x.2 - η * y.1) : y = implicitEuler η x := by
  have h := (one_add_sq_pos η).ne'
  have e1 : y.1 * (1 + η ^ 2) = x.1 + η * x.2 := by
    linear_combination h1 + η * h2
  have e2 : y.2 * (1 + η ^ 2) = x.2 - η * x.1 := by
    linear_combination h2 - η * h1
  ext
  · simp only [implicitEuler]; field_simp; linarith
  · simp only [implicitEuler]; field_simp; linarith

/-! ### Matrices and determinants -/

def explicitMat (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, η; -η, 1]

noncomputable def implicitMat (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / (1 + η ^ 2), η / (1 + η ^ 2); -η / (1 + η ^ 2), 1 / (1 + η ^ 2)]

def symplecticMat (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 - η ^ 2, η; -η, 1]

/-- Coordinates of a state as a vector. -/
def toVec (x : ℝ × ℝ) : Fin 2 → ℝ := ![x.1, x.2]

theorem explicit_eq_mulVec (η : ℝ) (x : ℝ × ℝ) :
    toVec (explicitEuler η x) = explicitMat η *ᵥ toVec x := by
  ext i; fin_cases i <;>
    simp [toVec, explicitEuler, explicitMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  all_goals ring

theorem implicit_eq_mulVec (η : ℝ) (x : ℝ × ℝ) :
    toVec (implicitEuler η x) = implicitMat η *ᵥ toVec x := by
  ext i; fin_cases i <;>
    simp [toVec, implicitEuler, implicitMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  all_goals ring

theorem symplectic_eq_mulVec (η : ℝ) (x : ℝ × ℝ) :
    toVec (symplecticEuler η x) = symplecticMat η *ᵥ toVec x := by
  ext i; fin_cases i <;>
    simp [toVec, symplecticEuler, symplecticMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

theorem det_explicitMat (η : ℝ) : (explicitMat η).det = 1 + η ^ 2 := by
  simp [explicitMat, Matrix.det_fin_two]; ring

theorem det_implicitMat (η : ℝ) : (implicitMat η).det = 1 / (1 + η ^ 2) := by
  have h := (one_add_sq_pos η).ne'
  simp only [implicitMat, Matrix.det_fin_two_of]
  field_simp; ring

theorem det_symplecticMat (η : ℝ) : (symplecticMat η).det = 1 := by
  simp [symplecticMat, Matrix.det_fin_two]; ring

/-! ### Energy growth / decay of the Euler methods -/

theorem explicit_energy (η : ℝ) (x : ℝ × ℝ) :
    energy (explicitEuler η x) = (1 + η ^ 2) * energy x := by
  simp only [energy, explicitEuler]; ring

theorem implicit_energy (η : ℝ) (x : ℝ × ℝ) :
    energy (implicitEuler η x) = 1 / (1 + η ^ 2) * energy x := by
  have h := (one_add_sq_pos η).ne'
  simp only [energy, implicitEuler]
  field_simp; ring

theorem explicit_energy_iter (η : ℝ) (n : ℕ) (x : ℝ × ℝ) :
    energy ((explicitEuler η)^[n] x) = (1 + η ^ 2) ^ n * energy x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', explicit_energy, ih, pow_succ]; ring

theorem implicit_energy_iter (η : ℝ) (n : ℕ) (x : ℝ × ℝ) :
    energy ((implicitEuler η)^[n] x) = (1 / (1 + η ^ 2)) ^ n * energy x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', implicit_energy, ih, pow_succ]; ring

lemma energy_pos {x : ℝ × ℝ} (hx : x ≠ 0) : 0 < energy x := by
  simp only [energy]
  by_contra h
  rw [not_lt] at h
  have h1 : x.1 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have h2 : x.2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  exact hx (Prod.ext h1 h2)

theorem explicit_energy_unbounded {η : ℝ} (hη : η ≠ 0) {x : ℝ × ℝ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => energy ((explicitEuler η)^[n] x)) atTop atTop := by
  simp_rw [explicit_energy_iter]
  have h1 : 1 < 1 + η ^ 2 := by have := pow_pos (abs_pos.mpr hη) 2; rw [sq_abs] at this; linarith
  exact (tendsto_pow_atTop_atTop_of_one_lt h1).atTop_mul_const (energy_pos hx)

/-! ### The modified form conserved by symplectic Euler -/

theorem symplectic_conserves (η : ℝ) (x : ℝ × ℝ) :
    modForm η (symplecticEuler η x) = modForm η x := by
  simp only [modForm, quadForm, symplecticEuler]; ring

theorem symplectic_conserves_quadForm (η q p : ℝ) :
    let q₁ := q + η * (p - η * q)
    let p₁ := p - η * q
    1 * q₁ ^ 2 + (-η) * q₁ * p₁ + 1 * p₁ ^ 2 = 1 * q ^ 2 + (-η) * q * p + 1 * p ^ 2 := by
  intro q₁ p₁; simp only [q₁, p₁]; ring

theorem symplectic_conserves_iter (η : ℝ) (n : ℕ) (x : ℝ × ℝ) :
    modForm η ((symplecticEuler η)^[n] x) = modForm η x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', symplectic_conserves, ih]

/-- The naive guess `q² + p² + η q p` is not conserved for any `η ≠ 0`. -/
theorem plus_form_not_conserved {η : ℝ} (hη : η ≠ 0) :
    ∃ x : ℝ × ℝ, quadForm 1 η 1 (symplecticEuler η x) ≠ quadForm 1 η 1 x := by
  refine ⟨(0, 1), ?_⟩
  simp only [quadForm, symplecticEuler]
  intro h
  have : 2 * η ^ 2 = 0 := by nlinarith [h]
  exact hη (by simpa using this)

/-- For `η ≠ 0` the conserved quadratic forms are exactly the multiples of `modForm η`. -/
theorem conserved_form_iff {η : ℝ} (hη : η ≠ 0) (a b c : ℝ) :
    (∀ x : ℝ × ℝ, quadForm a b c (symplecticEuler η x) = quadForm a b c x) ↔
      b = -η * a ∧ c = a := by
  constructor
  · intro h
    have h01 := h (0, 1)
    have h10 := h (1, 0)
    simp only [quadForm, symplecticEuler] at h01 h10
    have hb : b = -η * a := by
      have : η * (a * η + b) = 0 := by linear_combination h01
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hη
      · linarith
    refine ⟨hb, ?_⟩
    subst hb
    have : η ^ 2 * (c - a) = 0 := by linear_combination h10
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h') hη
    · linarith
  · rintro ⟨rfl, rfl⟩ x
    simp only [quadForm, symplecticEuler]; ring

theorem modForm_tendsto (x : ℝ × ℝ) :
    Tendsto (fun η : ℝ => modForm η x) (𝓝 0) (𝓝 (energy x)) := by
  have hc : Continuous (fun η : ℝ => modForm η x) := by
    simp only [modForm, quadForm]; fun_prop
  have := hc.tendsto 0
  simpa [modForm, quadForm, energy] using this

/-! ### Positive definiteness and boundedness -/

theorem modForm_lower {η : ℝ} (hη : 0 ≤ η) (x : ℝ × ℝ) :
    (1 - η / 2) * energy x ≤ modForm η x := by
  simp only [modForm, quadForm, energy]
  nlinarith [mul_nonneg hη (sq_nonneg (x.1 - x.2))]

theorem modForm_posDef_iff {η : ℝ} (hη : 0 < η) :
    (∀ x : ℝ × ℝ, x ≠ 0 → 0 < modForm η x) ↔ η < 2 := by
  constructor
  · intro h
    have := h (1, 1) (by simp [Prod.ext_iff])
    simp only [modForm, quadForm] at this
    linarith
  · intro h2 x hx
    have hl := modForm_lower hη.le x
    have he := energy_pos hx
    nlinarith

theorem symplectic_bounded {η : ℝ} (hη : 0 < η) (h2 : η < 2) (x : ℝ × ℝ) (n : ℕ) :
    energy ((symplecticEuler η)^[n] x) ≤ modForm η x / (1 - η / 2) := by
  have hpos : 0 < 1 - η / 2 := by linarith
  rw [le_div_iff₀ hpos, ← symplectic_conserves_iter η n x, mul_comm]
  exact modForm_lower hη.le _

theorem symplectic_orbit_bounded {η : ℝ} (hη : 0 < η) (h2 : η < 2) (x : ℝ × ℝ) :
    ∃ C : ℝ, ∀ n : ℕ, energy ((symplecticEuler η)^[n] x) ≤ C :=
  ⟨_, symplectic_bounded hη h2 x⟩

end DiscretizationInvariantsA
