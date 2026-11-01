import Mathlib

/-!
# A02 — The learning pair's conserved imbalance (proofs)

**What is proved (formally).**
* (a) For `L(e,d) = (e d - c)^2/2`: the partials of `L`; along any `(e,d) : ℝ → ℝ` with
  `HasDerivAt` everywhere for the flow `ė = -(ed-c)d`, `ḋ = -(ed-c)e`, the map
  `t ↦ e t^2 - d t^2` has derivative `0` and is constant (global version, and an interval
  version on `[a,b]` with continuity on `[a,b]` and the ODE on `(a,b)`). Only differentiability
  is assumed, which is weaker than `C^1`. The flow vector has zero dot product with
  `(2e,-2d) = ∇(e^2-d^2)` and equals `-(ed-c) • (d,e)` where `(d,e) = ∇(ed)`.
  In `ℂ`: `(e + i d)^2 = (e^2-d^2) + i(2ed)`, with the stated real and imaginary parts.
* (b) For `E : m×n`, `D : n×m`, `R = DE - 1`, `gD = R C Eᵀ`, `gE = Dᵀ R C`:
  `gE Eᵀ + E gEᵀ - (gDᵀ D + Dᵀ gD) = 0`. A general form shows this holds for *any* `R`, `C`
  over any commutative ring (symmetry of `C` is not used). An entrywise calculus version:
  if every entry of `E`, `D` satisfies `Ė = -gE`, `Ḋ = -gD`, then `E Eᵀ - Dᵀ D` is constant.
* Added (adversarial pass): `matrix_balanced_preserved` — if `E Eᵀ = Dᵀ D` at one time then at
  all times. `logistic_hasDerivAt` — `x(t) = 1/√(1+e^{-2t})` solves `ẋ = -(x x - 1) x`, giving a
  non-constant global solution `e = d = x` (`c = 1`), so the flow hypotheses are not vacuous.
  `example`s instantiate the scalar theorem (stationary `e ≡ 2, d ≡ 3, c = 6`, imbalance `-5`;
  and the logistic solution, whose velocity at `0` is shown nonzero) and the matrix core
  (`E = [1 2]`, `D = [3;4]`, `C = 1`).

**Interpretation (not formalised).** `gD`, `gE` are the gradients of the reconstruction loss
`½ tr(R C Rᵀ)` with `C` the input covariance; that fact is *not* proved here, only used to
motivate the definitions. The conserved imbalance `E Eᵀ - Dᵀ D` (scalar: `e^2 - d^2`) is the
rescaling symmetry `(E, D) ↦ (G E, D G⁻¹)` showing up as a Noether-type invariant; the complex
identity says the loss only sees `Im (e+id)^2 / 2 = ed`, while flow preserves `Re (e+id)^2`.

-/

open Complex Matrix

namespace A02

/-! ## (a) Scalar pair -/

/-- The scalar loss `L(e,d) = (e d - c)^2 / 2`. -/
noncomputable def lossS (c e d : ℝ) : ℝ := (e * d - c) ^ 2 / 2

/-- `∂L/∂e = (e d - c) d`. -/
theorem lossS_hasDerivAt_e (c e d : ℝ) :
    HasDerivAt (fun x => lossS c x d) ((e * d - c) * d) e := by
  unfold lossS
  have h : HasDerivAt (fun x => x * d - c) d e := by
    simpa using ((hasDerivAt_id e).mul_const d).sub_const c
  convert (h.pow 2).div_const 2 using 1
  ring

/-- `∂L/∂d = (e d - c) e`. -/
theorem lossS_hasDerivAt_d (c e d : ℝ) :
    HasDerivAt (fun y => lossS c e y) ((e * d - c) * e) d := by
  unfold lossS
  have h : HasDerivAt (fun y => e * y - c) e d := by
    simpa using ((hasDerivAt_id d).const_mul e).sub_const c
  convert (h.pow 2).div_const 2 using 1
  ring

/-- Derivative of the imbalance along the flow is zero (pointwise form). -/
theorem scalar_imbalance_hasDerivAt_zero (c : ℝ) (e d : ℝ → ℝ) (t : ℝ)
    (he : HasDerivAt e (-(e t * d t - c) * d t) t)
    (hd : HasDerivAt d (-(e t * d t - c) * e t) t) :
    HasDerivAt (fun s => e s ^ 2 - d s ^ 2) 0 t := by
  convert (he.pow 2).sub (hd.pow 2) using 1
  push_cast
  ring

/-- Conservation along any everywhere-differentiable solution of the gradient flow. -/
theorem scalar_imbalance_conserved (c : ℝ) (e d : ℝ → ℝ)
    (he : ∀ t, HasDerivAt e (-(e t * d t - c) * d t) t)
    (hd : ∀ t, HasDerivAt d (-(e t * d t - c) * e t) t) :
    ∀ t s, e t ^ 2 - d t ^ 2 = e s ^ 2 - d s ^ 2 := by
  have hdiff : Differentiable ℝ (fun s => e s ^ 2 - d s ^ 2) := fun s =>
    (scalar_imbalance_hasDerivAt_zero c e d s (he s) (hd s)).differentiableAt
  have hderiv : ∀ s, deriv (fun s => e s ^ 2 - d s ^ 2) s = 0 := fun s =>
    (scalar_imbalance_hasDerivAt_zero c e d s (he s) (hd s)).deriv
  intro t s
  exact is_const_of_deriv_eq_zero hdiff hderiv t s

/-- Interval version: a solution on `[a,b]` (continuous on `[a,b]`, solving the ODE on `(a,b)`)
conserves the imbalance between the endpoints. -/
theorem scalar_imbalance_conserved_Icc (c a b : ℝ) (hab : a ≤ b) (e d : ℝ → ℝ)
    (hec : ContinuousOn e (Set.Icc a b)) (hdc : ContinuousOn d (Set.Icc a b))
    (he : ∀ t ∈ Set.Ioo a b, HasDerivAt e (-(e t * d t - c) * d t) t)
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt d (-(e t * d t - c) * e t) t) :
    e b ^ 2 - d b ^ 2 = e a ^ 2 - d a ^ 2 := by
  rcases hab.eq_or_lt with h | h
  · subst h; rfl
  have hcont : ContinuousOn (fun s => e s ^ 2 - d s ^ 2) (Set.Icc a b) :=
    (hec.pow 2).sub (hdc.pow 2)
  obtain ⟨x, hx, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => e s ^ 2 - d s ^ 2)
    (fun _ => (0 : ℝ)) h hcont
    (fun t ht => scalar_imbalance_hasDerivAt_zero c e d t (he t ht) (hd t ht))
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  have := hslope.symm
  rw [div_eq_zero_iff] at this
  rcases this with h1 | h1
  · linarith
  · exact absurd h1 hne

/-- Gradient of `e^2 - d^2` is `(2e, -2d)` (partial derivatives). -/
theorem imbalance_partials (e d : ℝ) :
    HasDerivAt (fun x => x ^ 2 - d ^ 2) (2 * e) e ∧
    HasDerivAt (fun y => e ^ 2 - y ^ 2) (-2 * d) d := by
  constructor
  · have h := ((hasDerivAt_id' e).pow 2).sub_const (d ^ 2)
    simp only [Nat.cast_ofNat, mul_one] at h
    convert h using 1; ring
  · have h := ((hasDerivAt_id' d).pow 2).const_sub (e ^ 2)
    simp only [Nat.cast_ofNat, mul_one] at h
    convert h using 1; ring

/-- Gradient of `e d` is `(d, e)` (partial derivatives). -/
theorem product_partials (e d : ℝ) :
    HasDerivAt (fun x => x * d) d e ∧ HasDerivAt (fun y => e * y) e d := by
  constructor
  · simpa using (hasDerivAt_id e).mul_const d
  · simpa using (hasDerivAt_id d).const_mul e

/-- The flow vector is orthogonal to `∇(e^2 - d^2) = (2e, -2d)`. -/
theorem flow_orth_grad_imbalance (c e d : ℝ) :
    (-(e * d - c) * d) * (2 * e) + (-(e * d - c) * e) * (-2 * d) = 0 := by ring

/-- The flow vector is parallel to `∇(e d) = (d, e)`: it equals `-(e d - c) • (d, e)`,
equivalently its 2D cross product with `(d, e)` vanishes. -/
theorem flow_parallel_grad_product (c e d : ℝ) :
    ((-(e * d - c) * d, -(e * d - c) * e) : ℝ × ℝ) = (-(e * d - c)) • ((d, e) : ℝ × ℝ) ∧
    (-(e * d - c) * d) * e - (-(e * d - c) * e) * d = 0 := by
  refine ⟨?_, by ring⟩
  ext <;> simp [smul_eq_mul]

/-- `(e + i d)^2 = (e^2 - d^2) + i (2 e d)`. -/
theorem complex_square (e d : ℝ) :
    ((e : ℂ) + I * d) ^ 2 = ((e ^ 2 - d ^ 2 : ℝ) : ℂ) + I * ((2 * e * d : ℝ) : ℂ) := by
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem complex_square_re (e d : ℝ) : (((e : ℂ) + I * d) ^ 2).re = e ^ 2 - d ^ 2 := by
  rw [complex_square]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

theorem complex_square_im (e d : ℝ) : (((e : ℂ) + I * d) ^ 2).im = 2 * e * d := by
  rw [complex_square]
  simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

/-! ## (b) Matrix pair -/

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Residual `R = D E - 1` (an `n × n` = `d × d` matrix). -/
def resid (E : Matrix m n ℝ) (D : Matrix n m ℝ) : Matrix n n ℝ := D * E - 1

/-- `gD = R C Eᵀ`. -/
def gradD (E : Matrix m n ℝ) (D : Matrix n m ℝ) (C : Matrix n n ℝ) : Matrix n m ℝ :=
  resid E D * C * Eᵀ

/-- `gE = Dᵀ R C`. -/
def gradE (E : Matrix m n ℝ) (D : Matrix n m ℝ) (C : Matrix n n ℝ) : Matrix m n ℝ :=
  Dᵀ * resid E D * C

/-- The algebraic core, as requested (symmetric `C`). -/
theorem matrix_core (E : Matrix m n ℝ) (D : Matrix n m ℝ) (C : Matrix n n ℝ) (_hC : Cᵀ = C) :
    gradE E D C * Eᵀ + E * (gradE E D C)ᵀ
      - ((gradD E D C)ᵀ * D + Dᵀ * gradD E D C) = 0 := by
  simp only [gradE, gradD, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  abel

/-- General form: the identity holds for any `R` and any `C` (no symmetry, no `R = DE - 1`),
over any commutative ring. -/
theorem matrix_core_general {α : Type*} [CommRing α] {m n : Type*} [Fintype n]
    (E : Matrix m n α) (D : Matrix n m α) (R C : Matrix n n α) :
    (Dᵀ * R * C) * Eᵀ + E * (Dᵀ * R * C)ᵀ
      - ((R * C * Eᵀ)ᵀ * D + Dᵀ * (R * C * Eᵀ)) = 0 := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  abel

/-- Calculus version (entrywise derivatives): along any solution of
`Ė = -gE`, `Ḋ = -gD`, the imbalance `E Eᵀ - Dᵀ D` is constant. No symmetry of `C` is needed. -/
theorem matrix_imbalance_conserved (C : Matrix n n ℝ) (E : ℝ → Matrix m n ℝ)
    (D : ℝ → Matrix n m ℝ)
    (hE : ∀ t i j, HasDerivAt (fun s => E s i j) (-(gradE (E t) (D t) C) i j) t)
    (hD : ∀ t i j, HasDerivAt (fun s => D s i j) (-(gradD (E t) (D t) C) i j) t) :
    ∀ t s, E t * (E t)ᵀ - (D t)ᵀ * D t = E s * (E s)ᵀ - (D s)ᵀ * D s := by
  -- entrywise derivative of the imbalance is zero
  have key : ∀ t i j, HasDerivAt (fun s => (E s * (E s)ᵀ - (D s)ᵀ * D s) i j) 0 t := by
    intro t i j
    set GE := gradE (E t) (D t) C with hGE
    set GD := gradD (E t) (D t) C with hGD
    have hEt : ∀ a b, HasDerivAt (fun s => E s a b) ((-GE) a b) t := fun a b => hE t a b
    have hDt : ∀ a b, HasDerivAt (fun s => D s a b) ((-GD) a b) t := fun a b => hD t a b
    have hz : (GE * (E t)ᵀ + E t * GEᵀ - (GDᵀ * D t + (D t)ᵀ * GD)) i j = 0 := by
      rw [hGE, hGD]; unfold gradE gradD; rw [matrix_core_general]; rfl
    clear_value GE GD
    have h1 : HasDerivAt (fun s => ∑ l, E s i l * E s j l)
        (∑ l, ((-GE) i l * E t j l + E t i l * (-GE) j l)) t :=
      HasDerivAt.fun_sum (fun l _ => (hEt i l).fun_mul (hEt j l))
    have h2 : HasDerivAt (fun s => ∑ l, D s l i * D s l j)
        (∑ l, ((-GD) l i * D t l j + D t l i * (-GD) l j)) t :=
      HasDerivAt.fun_sum (fun l _ => (hDt l i).fun_mul (hDt l j))
    have h3 := h1.sub h2
    convert h3 using 1
    · funext s
      simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
    · simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
        at hz
      simp only [Matrix.neg_apply, Finset.sum_add_distrib, neg_mul, mul_neg,
        Finset.sum_neg_distrib]
      linarith
  intro t s
  ext i j
  have hdiff : Differentiable ℝ (fun s => (E s * (E s)ᵀ - (D s)ᵀ * D s) i j) := fun s =>
    (key s i j).differentiableAt
  exact is_const_of_deriv_eq_zero hdiff (fun s => (key s i j).deriv) t s


/-! ## Added corollary (going down): balanced initialisation stays balanced -/

/-- If the pair starts balanced at some time `s` (`E Eᵀ = Dᵀ D`), it is balanced at every
time `t` along the (entrywise) gradient flow. -/
theorem matrix_balanced_preserved (C : Matrix n n ℝ) (E : ℝ → Matrix m n ℝ)
    (D : ℝ → Matrix n m ℝ)
    (hE : ∀ t i j, HasDerivAt (fun s => E s i j) (-(gradE (E t) (D t) C) i j) t)
    (hD : ∀ t i j, HasDerivAt (fun s => D s i j) (-(gradD (E t) (D t) C) i j) t)
    (s : ℝ) (h0 : E s * (E s)ᵀ = (D s)ᵀ * D s) :
    ∀ t, E t * (E t)ᵀ = (D t)ᵀ * D t := by
  intro t
  have h := matrix_imbalance_conserved C E D hE hD t s
  rw [h0, sub_self] at h
  exact sub_eq_zero.mp h

/-! ## Concrete instantiations (sanity checks) -/

/-- A stationary solution `e ≡ 2`, `d ≡ 3`, `c = 6`: the imbalance is `-5` at every time. -/
example : ∀ t s : ℝ, (fun _ : ℝ => (2 : ℝ)) t ^ 2 - (fun _ : ℝ => (3 : ℝ)) t ^ 2
    = (fun _ : ℝ => (2 : ℝ)) s ^ 2 - (fun _ : ℝ => (3 : ℝ)) s ^ 2 :=
  scalar_imbalance_conserved 6 (fun _ => 2) (fun _ => 3)
    (fun t => by convert hasDerivAt_const t (2 : ℝ) using 1; norm_num)
    (fun t => by convert hasDerivAt_const t (3 : ℝ) using 1; norm_num)

/-- The logistic-type curve `x(t) = 1/√(1+exp(-2t))` solves `ẋ = -(x·x - 1)·x`, so
`e = d = x` is a global solution of the flow with `c = 1` (non-constant: see the example
below, which shows its velocity at `0` is nonzero), so the hypotheses
of `scalar_imbalance_conserved` are satisfiable non-trivially. -/
theorem logistic_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => 1 / Real.sqrt (1 + Real.exp (-2 * s)))
      (-((1 / Real.sqrt (1 + Real.exp (-2 * t))) * (1 / Real.sqrt (1 + Real.exp (-2 * t))) - 1)
        * (1 / Real.sqrt (1 + Real.exp (-2 * t)))) t := by
  have hu : 0 < 1 + Real.exp (-2 * t) := by positivity
  have hexp : HasDerivAt (fun s => Real.exp (-2 * s)) (Real.exp (-2 * t) * (-2)) t := by
    have := ((hasDerivAt_id t).const_mul (-2)).exp
    simpa [mul_comm] using this
  have hU : HasDerivAt (fun s => 1 + Real.exp (-2 * s)) (Real.exp (-2 * t) * (-2)) t := by
    simpa using hexp.const_add 1
  have hS := hU.sqrt hu.ne'
  have hsq : 0 < Real.sqrt (1 + Real.exp (-2 * t)) := Real.sqrt_pos.mpr hu
  have hI := hS.inv hsq.ne'
  have hss : Real.sqrt (1 + Real.exp (-2 * t)) ^ 2 = 1 + Real.exp (-2 * t) :=
    Real.sq_sqrt hu.le
  convert hI using 1
  · funext s; simp [one_div]
  · field_simp
    rw [show -(2 * t) = -2 * t by ring, hss]
    ring

/-- Non-vacuity of `scalar_imbalance_conserved` with a non-constant solution:
`e = d = x` with `x` from `logistic_hasDerivAt`, `c = 1`. -/
example : ∀ t s : ℝ,
    (fun u => 1 / Real.sqrt (1 + Real.exp (-2 * u))) t ^ 2
      - (fun u => 1 / Real.sqrt (1 + Real.exp (-2 * u))) t ^ 2
    = (fun u => 1 / Real.sqrt (1 + Real.exp (-2 * u))) s ^ 2
      - (fun u => 1 / Real.sqrt (1 + Real.exp (-2 * u))) s ^ 2 :=
  scalar_imbalance_conserved 1 _ _ logistic_hasDerivAt logistic_hasDerivAt

/-- The logistic solution really moves: its velocity at `t = 0` is nonzero. -/
example : (-((1 / Real.sqrt (1 + Real.exp (-2 * 0))) * (1 / Real.sqrt (1 + Real.exp (-2 * 0)))
    - 1) * (1 / Real.sqrt (1 + Real.exp (-2 * 0)))) ≠ 0 := by
  have h2 : (1 : ℝ) + Real.exp (-2 * 0) = 2 := by norm_num
  rw [h2]
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := by positivity
  have : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 / 2 := by
    rw [div_mul_div_comm, one_mul, hs]
  rw [this]
  have : 0 < 1 / Real.sqrt 2 := by positivity
  nlinarith

/-- Concrete instance of the matrix core with `E = [1 2]` (1×2), `D = [3; 4]` (2×1), `C = 1`. -/
example :
    let E : Matrix (Fin 1) (Fin 2) ℝ := !![1, 2]
    let D : Matrix (Fin 2) (Fin 1) ℝ := !![3; 4]
    gradE E D 1 * Eᵀ + E * (gradE E D 1)ᵀ - ((gradD E D 1)ᵀ * D + Dᵀ * gradD E D 1) = 0 :=
  matrix_core _ _ _ Matrix.transpose_one

end A02
