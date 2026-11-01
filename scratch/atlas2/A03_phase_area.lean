import Mathlib

/-!
# A03 phase-space area

## What is proved (Lean facts, no interpretation)

Part (a), linear flows on `ℝ²`:
* `flow_hasDerivAt`: `u ↦ exp (u • A) *ᵥ x₀` has derivative `A *ᵥ (exp (t • A) *ᵥ x₀)`,
  i.e. `exp (t • A)` is the time-`t` map of `x' = A x`.
* `det_exp_smul`, `det_exp`: for every real `2 × 2` matrix, `det (exp (t • A)) = exp (t · tr A)`.
  (This is the `n = 2` case of the TODO in `Mathlib/Analysis/Normed/Algebra/MatrixExponential`.)
  Proof: entries of `exp (u • A)` are differentiable with derivative `A * exp (u • A)`;
  hence `d/du det = tr A · det` (a ring identity in the 2×2 entries); then
  `det (exp (u • A)) · exp (-u tr A)` has zero derivative and equals `1` at `u = 0`.
* `flow_scales_area`: Lebesgue measure on `EuclideanSpace ℝ (Fin 2)` of the image of any set
  `s` under the flow map is `exp (t · tr A) · volume s`.
* `flow_preserves_area_of_trace_zero`, `dampedOsc_trace`, `dampedOsc_area`.

Part (b), harmonic oscillator:
* `volume_energyEllipse`: `volume {p²/2 + ω² x²/2 ≤ E} = ofReal (2πE/ω)` for `ω > 0`, all `E`
  (for `E < 0` the set is empty and both sides are `0`). Route: the ellipse is the preimage of
  the closed disc of radius `√(2E)` under `diag(ω, 1)`; Mathlib gives the disc area `π r²`
  and the linear change-of-variables factor `|det|⁻¹ = 1/ω`.
* `area_energyEllipse`, `hasDerivAt_area_energyEllipse`: real area `2πE/ω`, derivative `2π/ω`.
* `harmOsc_period`: `exp ((2π/ω) • !![0,1;-ω²,0]) = 1` — the flow returns to the identity
  at time `2π/ω`. Proof: compare with the explicit cos/sin solution; their difference solves
  the same ODE from `0`, and conserved energy (positive definite for `ω > 0`) forces it to `0`.
* `energy_flow`, `flow_mapsTo_energyEllipse`: energy is conserved and each ellipse is invariant.

Second-agent additions:
* `hamiltonian_flow_preserves_area`: for symmetric `S`, the flow of `z' = J S z`
  (`J = !![0,1;-1,0]`) preserves Lebesgue measure; this proves "linear Hamiltonian ⇒ trace 0"
  for 2×2 instead of assuming it.
* Concrete `example`s: `harmOsc ω = J · diag(ω²,1)`; the damped flow with `ω = 1`, `γ = 1/2`
  sends `{H ≤ 1}` to a set of area `2π e^{-t}`; the dilation `exp (t • 1)` sends the unit disc to
  area `π e^{2t}`.

## Interpretation (not formalized)
`2π/ω` being both `d(area)/dE` and a period of the flow is the classical identity
`T = dJ/dE` (action `J` = enclosed phase area) for the harmonic oscillator. We prove the two
numbers separately; we do NOT prove `2π/ω` is the *minimal* period, nor any general
action–period theorem for nonlinear Hamiltonians. "Hamiltonian ⇒ trace 0" is used only as the
hypothesis `tr A = 0` in `flow_preserves_area_of_trace_zero`; `hamiltonian_flow_preserves_area`
covers 2×2 linear Hamiltonian fields `J S` with `S` symmetric. Nonlinear Hamiltonians are not covered.
-/

open MeasureTheory Real NormedSpace Matrix

noncomputable section

namespace A03

/-! ### Helpers: continuous linear evaluations of a matrix -/

/-- `M ↦ M *ᵥ x₀` as a linear map (helper). -/
def mulVecLin' (x₀ : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun M := M *ᵥ x₀
  map_add' M N := Matrix.add_mulVec M N x₀
  map_smul' c M := Matrix.smul_mulVec c M x₀

/-- `M ↦ M i j` as a linear map (helper). -/
def entryLin (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-! ### (a) Linear flows -/

set_option backward.isDefEq.respectTransparency false in
/-- The flow `x(t) = exp(tA) x₀` solves `x' = A x`. -/
theorem flow_hasDerivAt (A : Matrix (Fin 2) (Fin 2) ℝ) (x₀ : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => exp (u • A) *ᵥ x₀) (A *ᵥ (exp (t • A) *ᵥ x₀)) t := by
  open scoped Norms.Operator in
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t
  open scoped Norms.Operator in
  have hL := (LinearMap.toContinuousLinearMap (mulVecLin' x₀)).hasFDerivAt (x := exp (t • A))
  have := hL.comp_hasDerivAt t h
  convert this using 1
  · rfl
  · show _ = (A * exp (t • A)) *ᵥ x₀
    rw [Matrix.mulVec_mulVec]

set_option backward.isDefEq.respectTransparency false in
/-- Entry `(i,j)` of `exp (u • A)` has derivative `(A * exp (t • A)) i j` (helper). -/
theorem entry_hasDerivAt (A : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) (t : ℝ) :
    HasDerivAt (fun u : ℝ => exp (u • A) i j) ((A * exp (t • A)) i j) t := by
  open scoped Norms.Operator in
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t
  open scoped Norms.Operator in
  have hL := (LinearMap.toContinuousLinearMap (entryLin i j)).hasFDerivAt (x := exp (t • A))
  exact hL.comp_hasDerivAt t h

/-- Jacobi/Liouville ODE for 2×2: `d/dt det Φ = tr A · det Φ`, `Φ = exp (t • A)` (helper). -/
theorem det_hasDerivAt (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (exp (u • A)).det) (A.trace * (exp (t • A)).det) t := by
  have h00 := entry_hasDerivAt A 0 0 t
  have h01 := entry_hasDerivAt A 0 1 t
  have h10 := entry_hasDerivAt A 1 0 t
  have h11 := entry_hasDerivAt A 1 1 t
  have := (h00.mul h11).sub (h01.mul h10)
  simp only [Matrix.det_fin_two]
  convert this using 1
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Liouville / Jacobi for 2×2: `det (exp (t A)) = exp (t · tr A)`. -/
theorem det_exp_smul (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    (exp (t • A)).det = Real.exp (t * A.trace) := by
  set g : ℝ → ℝ := fun u => (exp (u • A)).det * Real.exp (-(u * A.trace)) with hg
  have hd : ∀ u, HasDerivAt g 0 u := by
    intro u
    have h1 := det_hasDerivAt A u
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-(u * A.trace)))
        (Real.exp (-(u * A.trace)) * (-(1 * A.trace))) u :=
      (((hasDerivAt_id u).mul_const A.trace).neg).exp
    convert h1.mul h2 using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t 0
  simp only [hg, zero_smul, NormedSpace.exp_zero, Matrix.det_one, zero_mul, neg_zero,
    Real.exp_zero, mul_one] at hc
  calc (exp (t • A)).det = (exp (t • A)).det * Real.exp (-(t * A.trace)) *
        Real.exp (t * A.trace) := by
          rw [mul_assoc, ← Real.exp_add]; simp
    _ = Real.exp (t * A.trace) := by rw [hc, one_mul]

theorem det_exp (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (exp A).det = Real.exp A.trace := by
  simpa using det_exp_smul A 1

/-- `LinearMap.det` of `toEuclideanLin M` is `M.det` (helper). -/
theorem det_toEuclideanLin (M : Matrix (Fin 2) (Fin 2) ℝ) :
    LinearMap.det (toEuclideanLin M) = M.det := by
  rw [toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]

/-- The time-`t` flow map scales Lebesgue area by `exp (t · tr A)`. -/
theorem flow_scales_area (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ)
    (s : Set (EuclideanSpace ℝ (Fin 2))) :
    volume (toEuclideanLin (exp (t • A)) '' s) =
      ENNReal.ofReal (Real.exp (t * A.trace)) * volume s := by
  rw [Measure.addHaar_image_linearMap, det_toEuclideanLin, det_exp_smul,
    abs_of_pos (Real.exp_pos _)]

/-- Trace-zero (e.g. Hamiltonian) linear flows preserve area. -/
theorem flow_preserves_area_of_trace_zero (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.trace = 0)
    (t : ℝ) (s : Set (EuclideanSpace ℝ (Fin 2))) :
    volume (toEuclideanLin (exp (t • A)) '' s) = volume s := by
  rw [flow_scales_area, hA]; simp

/-- Damped oscillator `x'' + 2γ x' + ω² x = 0` as a first-order system. -/
def dampedOsc (ω γ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -ω ^ 2, -2 * γ]

theorem dampedOsc_trace (ω γ : ℝ) : (dampedOsc ω γ).trace = -2 * γ := by
  simp [dampedOsc, Matrix.trace_fin_two]

theorem dampedOsc_area (ω γ t : ℝ) (s : Set (EuclideanSpace ℝ (Fin 2))) :
    volume (toEuclideanLin (exp (t • dampedOsc ω γ)) '' s) =
      ENNReal.ofReal (Real.exp (-2 * γ * t)) * volume s := by
  rw [flow_scales_area, dampedOsc_trace, mul_comm t]

/-! ### (b) Harmonic oscillator energy ellipse -/

/-- Harmonic oscillator energy `H(x,p) = p²/2 + ω² x²/2`, with `x = z 0`, `p = z 1`. -/
def energy (ω : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ := z 1 ^ 2 / 2 + ω ^ 2 * z 0 ^ 2 / 2

/-- The energy sublevel set (filled ellipse) `{H ≤ E}`. -/
def energyEllipse (ω E : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) := {z | energy ω z ≤ E}

/-- For `E ≥ 0` the ellipse is the preimage of the disc of radius `√(2E)` under
`diag(ω, 1)` (helper). -/
theorem energyEllipse_eq_preimage (ω E : ℝ) (hE : 0 ≤ E) :
    energyEllipse ω E =
      toEuclideanLin !![ω, 0; 0, 1] ⁻¹' Metric.closedBall 0 (√(2 * E)) := by
  ext z
  simp only [energyEllipse, energy, Set.mem_ofPred_eq, Set.mem_preimage,
    mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_le_sqrt_iff (by linarith)]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor <;> intro h <;> nlinarith

/-- Area of the energy ellipse is `2πE/ω` (as an `ENNReal`; `0` when `E < 0`). -/
theorem volume_energyEllipse (ω E : ℝ) (hω : 0 < ω) :
    volume (energyEllipse ω E) = ENNReal.ofReal (2 * π * E / ω) := by
  rcases lt_or_ge E 0 with hE | hE
  · have : energyEllipse ω E = ∅ := by
      ext z
      simp only [energyEllipse, energy, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_le]
      nlinarith [sq_nonneg (z 1), sq_nonneg (z 0), sq_nonneg ω]
    rw [this, measure_empty, ENNReal.ofReal_of_nonpos]
    have : 2 * π * E ≤ 0 := by nlinarith [Real.pi_pos]
    exact div_nonpos_of_nonpos_of_nonneg this hω.le
  · have hdet : LinearMap.det (toEuclideanLin !![ω, 0; 0, (1:ℝ)]) = ω := by
      rw [det_toEuclideanLin, Matrix.det_fin_two_of]; ring
    rw [energyEllipse_eq_preimage ω E hE,
      Measure.addHaar_preimage_linearMap _ (by rw [hdet]; exact hω.ne'),
      hdet, EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (by linarith), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (inv_pos.mpr hω)]
    congr 1
    field_simp

/-- Real-valued area, for `0 ≤ E`. -/
theorem area_energyEllipse (ω E : ℝ) (hω : 0 < ω) (hE : 0 ≤ E) :
    volume.real (energyEllipse ω E) = 2 * π * E / ω := by
  rw [measureReal_def, volume_energyEllipse ω E hω, ENNReal.toReal_ofReal (by positivity)]

/-- `d(area)/dE = 2π/ω` at every positive energy. -/
theorem hasDerivAt_area_energyEllipse (ω E : ℝ) (hω : 0 < ω) (hE : 0 < E) :
    HasDerivAt (fun E' => volume.real (energyEllipse ω E')) (2 * π / ω) E := by
  have h : HasDerivAt (fun E' : ℝ => 2 * π * E' / ω) (2 * π * 1 / ω) E :=
    ((hasDerivAt_id E).const_mul (2 * π)).div_const ω
  rw [mul_one] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hE] with E' hE'
  exact area_energyEllipse ω E' hω hE'.le

/-- The harmonic oscillator matrix. -/
def harmOsc (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -ω ^ 2, 0]

/-- Energy on plain vectors `Fin 2 → ℝ` (helper). -/
def energyV (ω : ℝ) (v : Fin 2 → ℝ) : ℝ := v 1 ^ 2 / 2 + ω ^ 2 * v 0 ^ 2 / 2

theorem harmOsc_mulVec (ω : ℝ) (v : Fin 2 → ℝ) :
    harmOsc ω *ᵥ v = ![v 1, -ω ^ 2 * v 0] := by
  ext i; fin_cases i <;> simp [harmOsc, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Any solution of `w' = harmOsc ω *ᵥ w` conserves energy (helper). -/
theorem energyV_const (ω : ℝ) (w : ℝ → Fin 2 → ℝ)
    (hw : ∀ u, HasDerivAt w (harmOsc ω *ᵥ w u) u) (s t : ℝ) :
    energyV ω (w s) = energyV ω (w t) := by
  have hd : ∀ u, HasDerivAt (fun u => energyV ω (w u)) 0 u := by
    intro u
    have h := hasDerivAt_pi.mp (hw u)
    rw [harmOsc_mulVec] at h
    have h0 := h 0
    have h1 := h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have := ((h1.pow 2).div_const 2).add (((h0.pow 2).const_mul (ω ^ 2)).div_const 2)
    convert this using 1
    · funext x; simp [energyV]
    · norm_num; ring
  exact is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) s t

/-- Explicit oscillator solution with initial condition `v` (helper). -/
def oscSol (ω : ℝ) (v : Fin 2 → ℝ) (u : ℝ) : Fin 2 → ℝ :=
  ![Real.cos (ω * u) * v 0 + Real.sin (ω * u) / ω * v 1,
    -ω * Real.sin (ω * u) * v 0 + Real.cos (ω * u) * v 1]

theorem oscSol_hasDerivAt (ω : ℝ) (hω : ω ≠ 0) (v : Fin 2 → ℝ) (u : ℝ) :
    HasDerivAt (oscSol ω v) (harmOsc ω *ᵥ oscSol ω v u) u := by
  rw [hasDerivAt_pi, harmOsc_mulVec]
  have hc : HasDerivAt (fun u => Real.cos (ω * u)) (-Real.sin (ω * u) * (ω * 1)) u :=
    ((hasDerivAt_id u).const_mul ω).cos
  have hs : HasDerivAt (fun u => Real.sin (ω * u)) (Real.cos (ω * u) * (ω * 1)) u :=
    ((hasDerivAt_id u).const_mul ω).sin
  intro i
  fin_cases i
  · have := (hc.mul_const (v 0)).add ((hs.div_const ω).mul_const (v 1))
    convert this using 1
    · funext x; simp [oscSol]
    · simp [oscSol]
      field_simp
  · have := ((hs.const_mul (-ω)).mul_const (v 0)).add (hc.mul_const (v 1))
    convert this using 1
    · funext x; simp [oscSol]
    · simp [oscSol]
      field_simp
      ring

/-- `2π/ω` is a period of the oscillator flow: `exp ((2π/ω) • harmOsc ω) = 1`.
(Not proved: that it is the minimal period.) -/
theorem harmOsc_period (ω : ℝ) (hω : 0 < ω) :
    exp ((2 * π / ω) • harmOsc ω) = 1 := by
  set T := 2 * π / ω with hT
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]
  set w : ℝ → Fin 2 → ℝ := fun u => exp (u • harmOsc ω) *ᵥ v - oscSol ω v u with hw
  have hdw : ∀ u, HasDerivAt w (harmOsc ω *ᵥ w u) u := by
    intro u
    have := (flow_hasDerivAt (harmOsc ω) v u).sub (oscSol_hasDerivAt ω hω.ne' v u)
    convert this using 1
    simp only [hw, Matrix.mulVec_sub]
  have h0 : w 0 = 0 := by
    ext i; fin_cases i <;> simp [hw, oscSol]
  have hE := energyV_const ω w hdw T 0
  rw [h0] at hE
  simp only [energyV, Pi.zero_apply] at hE
  have hw0 : w T 0 = 0 := by
    have : ω ^ 2 * w T 0 ^ 2 = 0 := by nlinarith [sq_nonneg (w T 1), sq_nonneg (ω * w T 0)]
    have hω2 : ω ^ 2 ≠ 0 := by positivity
    simpa [hω2] using this
  have hw1 : w T 1 = 0 := by nlinarith [sq_nonneg (w T 1), sq_nonneg (ω * w T 0)]
  have hwT : w T = 0 := by ext i; fin_cases i <;> simp [hw0, hw1]
  have hyT : oscSol ω v T = v := by
    have : ω * T = 2 * π := by rw [hT]; field_simp
    ext i; fin_cases i <;> simp [oscSol, this]
  have := congrArg (· + oscSol ω v T) hwT
  simp only [hw, sub_add_cancel, zero_add, hyT] at this
  exact this

/-- The oscillator flow conserves energy. -/
theorem energy_flow (ω t : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    energy ω (toEuclideanLin (exp (t • harmOsc ω)) z) = energy ω z := by
  have h := energyV_const ω (fun u => exp (u • harmOsc ω) *ᵥ z.ofLp)
    (fun u => flow_hasDerivAt (harmOsc ω) z.ofLp u) t 0
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec] at h
  simpa [energy, energyV] using h

/-- The oscillator flow maps each energy ellipse into itself. -/
theorem flow_mapsTo_energyEllipse (ω t E : ℝ) :
    Set.MapsTo (toEuclideanLin (exp (t • harmOsc ω))) (energyEllipse ω E)
      (energyEllipse ω E) := by
  intro z hz
  simp only [energyEllipse, Set.mem_ofPred_eq] at hz ⊢
  rwa [energy_flow]

/-! ### Second-agent additions -/

/-- The symplectic matrix `J = !![0,1;-1,0]` on `(x, p)`. -/
def symplJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- Generalisation of `flow_preserves_area_of_trace_zero` that discharges the
"Hamiltonian ⇒ trace 0" step: if `S` is symmetric, the linear Hamiltonian vector field
`z' = J S z` (Hamiltonian `H(z) = zᵀ S z / 2`, interpretation only) has a flow that preserves
the Lebesgue measure of every set. Proved: the Lean statement below, for any symmetric `S`. -/
theorem hamiltonian_flow_preserves_area (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.IsSymm)
    (t : ℝ) (s : Set (EuclideanSpace ℝ (Fin 2))) :
    volume (toEuclideanLin (exp (t • (symplJ * S))) '' s) = volume s := by
  apply flow_preserves_area_of_trace_zero
  have h10 : S 1 0 = S 0 1 := by simpa using congrFun (congrFun hS 0) 1
  simp [symplJ, Matrix.trace_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two, h10]

/-! ### Concrete instances (second agent) -/

/-- The oscillator matrix is Hamiltonian: `harmOsc ω = J · diag(ω², 1)`. -/
example (ω : ℝ) : harmOsc ω = symplJ * !![ω ^ 2, 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [harmOsc, symplJ]

/-- Instance of `dampedOsc_area` + `volume_energyEllipse`: with `ω = 1`, `γ = 1/2`, the
time-`t` damped flow maps the energy ellipse `{H ≤ 1}` to a set of area `2π · e^{-t}`. -/
example (t : ℝ) :
    volume (toEuclideanLin (exp (t • dampedOsc 1 (1 / 2))) '' energyEllipse 1 1) =
      ENNReal.ofReal (2 * π * Real.exp (-t)) := by
  rw [dampedOsc_area, volume_energyEllipse 1 1 one_pos, ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring_nf

/-- Instance of `flow_scales_area` on the unit disc with `A = 1` (pure dilation): area `π e^{2t}`. -/
example (t : ℝ) :
    volume (toEuclideanLin (exp (t • (1 : Matrix (Fin 2) (Fin 2) ℝ))) ''
        Metric.closedBall 0 1) = ENNReal.ofReal (Real.exp (2 * t)) * ENNReal.ofReal π := by
  rw [flow_scales_area, EuclideanSpace.volume_closedBall_fin_two]
  simp [mul_comm]

end A03
