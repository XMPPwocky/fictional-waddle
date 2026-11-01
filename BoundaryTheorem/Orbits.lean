import BoundaryTheorem.Potential
import BoundaryTheorem.Causal

/-!
# Part (C), the rotation clause: closed orbits when the Kantian condition fails

Source: `notes/BOOK_THEOREM.md` §1 box (C), last sentence of the scalar statement:
"If (ii) fails there is a bilinear reward for which `F_W` is a rotation with closed orbits", and the verifier's
gloss (`notes/BOOK_THEOREM_VERIFICATION.md` §2.3, *Rotation*): `R = x_{j,1}x_{i,2} − x_{j,2}x_{i,1}` gives
`(W_j − W_i)(θ₂, −θ₁)` for instances `i, j`, and "for an external `j = e` it is a rotation about a shifted centre;
orbits closed either way".

`Potential.lean` proves only that the field is not conservative when (ii) fails. This file proves the dynamics.

Setting: the plane `V = Fin 2 → ℝ` (the note's `ℝ²`; `d = 2` is the smallest dimension where (C) is nontrivial).

**The covector/vector identification.** `Potential.field` returns a covector `F_W(θ) : (Fin 2 → ℝ) →L[ℝ] ℝ`. The
training flow follows the vector `∇`, which needs an inner product. We use the standard Euclidean one, `dotProduct`:
`toVec L` is the unique vector with `⟪toVec L, h⟫ = L h` for all `h` (`toVec_dot`, `toVec_unique`), i.e. the
coordinates `(L e₀, L e₁)`. The training flow is the ODE `θ' = toVec (F_W(θ))`.

Main results:
* `hasDerivAt_rotSol`, `rotSol_periodic`, `rotSol_dot` — the explicit curve
  `rotSol λ c θ₀ t = c + cos(λt)(θ₀ − c) + sin(λt) J(θ₀ − c)`, `J(x, y) = (y, −x)`, solves `θ' = λ J(θ − c)`,
  has period `2π/|λ|`, and keeps the Euclidean distance to the centre `c` (`c = 0` is the task's `θ' = λ(y, −x)`);
* `rotSol_range` — for `λ ≠ 0` its orbit is the *whole* circle around `c` through `θ₀`;
* `rotSol_unique` — every solution of `θ' = λ J(θ − c)`, `θ(0) = θ₀`, is `rotSol λ c θ₀`
  (direct proof: `d/dt |θ − θ*|² = 0`);
* `toVec_field_rotFamily_instances`, `toVec_field_rotFamily_external` — the training field of the rotation reward
  `R = α(x_i)β(x_j) − β(x_i)α(x_j)`, `α = x₀`, `β = x₁`, is `(W_i − W_j) J θ` for two instances, and
  `W_e J(θ − (W_s/W_e) ξ_e)` for an external `e` and an instance `s`;
* `exists_rotation_of_not_isKantian` — if (ii) fails (and `S ≠ ∅`) some such reward makes the training field an
  affine rotation `λ J(θ − c)` with `λ ≠ 0`;
* `orbits_closed_of_not_isKantian` — hence, for that reward, every training orbit is a closed curve (periodic),
  and is exactly a circle;
* `not_conservative_of_periodic_orbit`, `rotation_not_conservative` — a field with a periodic non-stationary orbit
  has no potential (the potential would strictly increase along the orbit and return), so this file re-derives the
  non-conservativity of `Potential.lean` from the closed orbits.
-/

open Finset BoundaryTheorem.Potential

namespace BoundaryTheorem.Orbits

set_option linter.unusedSectionVars false

/-! ## The plane, the quarter turn `J`, and the Euclidean identification -/

/-- The quarter turn `J(x, y) = (y, −x)`, so that `λ • J` is the rotation field `λ(y, −x)` of the task statement. -/
def J (θ : Fin 2 → ℝ) : Fin 2 → ℝ := ![θ 1, -θ 0]

@[simp] theorem J_apply_zero (θ : Fin 2 → ℝ) : J θ 0 = θ 1 := rfl
@[simp] theorem J_apply_one (θ : Fin 2 → ℝ) : J θ 1 = -θ 0 := rfl

theorem J_J (θ : Fin 2 → ℝ) : J (J θ) = -θ := by
  ext m; fin_cases m <;> simp

theorem J_sub (x y : Fin 2 → ℝ) : J (x - y) = J x - J y := by
  ext m; fin_cases m <;> simp; ring

theorem J_smul (a : ℝ) (x : Fin 2 → ℝ) : J (a • x) = a • J x := by
  ext m; fin_cases m <;> simp

/-- `J` is skew for the dot product: `⟪x, J x⟫ = 0`. -/
theorem dot_J_self (x : Fin 2 → ℝ) : x ⬝ᵥ J x = 0 := by
  simp [dotProduct, Fin.sum_univ_two]; ring

theorem dot_J_J (x : Fin 2 → ℝ) : J x ⬝ᵥ J x = x ⬝ᵥ x := by
  simp [dotProduct, Fin.sum_univ_two]; ring

/-- **The Euclidean identification.** The vector of a covector `L` on `ℝ²`: `toVec L = (L e₀, L e₁)`. -/
def toVec (L : (Fin 2 → ℝ) →L[ℝ] ℝ) : Fin 2 → ℝ := fun m => L (Pi.single m 1)

/-- `⟪toVec L, h⟫ = L h`: `toVec L` represents `L` under the standard inner product. -/
theorem toVec_dot (L : (Fin 2 → ℝ) →L[ℝ] ℝ) (h : Fin 2 → ℝ) : toVec L ⬝ᵥ h = L h := by
  have hh : h = h 0 • Pi.single 0 1 + h 1 • Pi.single 1 1 := by
    ext m; fin_cases m <;> simp
  conv_rhs => rw [hh]
  simp [toVec, dotProduct, Fin.sum_univ_two, map_add, map_smul]
  ring

/-- The representing vector is unique. -/
theorem toVec_unique (L : (Fin 2 → ℝ) →L[ℝ] ℝ) (v : Fin 2 → ℝ) (hv : ∀ h, v ⬝ᵥ h = L h) : v = toVec L := by
  ext m
  have := hv (Pi.single m 1)
  show v m = L (Pi.single m 1)
  simpa [dotProduct, Pi.single_apply] using this

theorem toVec_smul (a : ℝ) (L : (Fin 2 → ℝ) →L[ℝ] ℝ) : toVec (a • L) = a • toVec L := by
  ext m; simp [toVec]

theorem toVec_sub (L M : (Fin 2 → ℝ) →L[ℝ] ℝ) : toVec (L - M) = toVec L - toVec M := by
  ext m; simp [toVec]

theorem toVec_add (L M : (Fin 2 → ℝ) →L[ℝ] ℝ) : toVec (L + M) = toVec L + toVec M := by
  ext m; simp [toVec]

@[simp] theorem toVec_proj0 : toVec (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) =
    Pi.single 0 1 := by
  ext m; fin_cases m <;> simp [toVec]

@[simp] theorem toVec_proj1 : toVec (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) =
    Pi.single 1 1 := by
  ext m; fin_cases m <;> simp [toVec]

/-! ## The rotation field and its explicit flow -/

/-- The affine rotation field `θ ↦ λ J(θ − c)`: angular speed `λ` (clockwise for `λ > 0`), centre `c`. With `c = 0`
this is `F(x, y) = λ(y, −x)`, the nonzero skew-symmetric linear field of the task statement. -/
def rot (l : ℝ) (c θ : Fin 2 → ℝ) : Fin 2 → ℝ := l • J (θ - c)

/-- `rot l 0` is a linear map, skew-symmetric for the dot product, and nonzero when `l ≠ 0`. -/
theorem rot_skew (l : ℝ) (x y : Fin 2 → ℝ) : rot l 0 x ⬝ᵥ y = -(x ⬝ᵥ rot l 0 y) := by
  simp [rot, dotProduct, Fin.sum_univ_two]; ring

theorem rot_ne_zero {l : ℝ} (hl : l ≠ 0) : rot l 0 ≠ 0 := by
  intro h
  have := congrFun (congrFun h (Pi.single 1 1)) 0
  simp [rot] at this
  exact hl this

/-- The explicit solution: `θ(t) = c + cos(λt)(θ₀ − c) + sin(λt) J(θ₀ − c)`. -/
noncomputable def rotSol (l : ℝ) (c θ₀ : Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  c + Real.cos (l * t) • (θ₀ - c) + Real.sin (l * t) • J (θ₀ - c)

@[simp] theorem rotSol_zero (l : ℝ) (c θ₀ : Fin 2 → ℝ) : rotSol l c θ₀ 0 = θ₀ := by
  simp [rotSol]

/-- **(1) The explicit curve solves the ODE** `θ' = rot l c θ = λ J(θ − c)`. -/
theorem hasDerivAt_rotSol (l : ℝ) (c θ₀ : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (rotSol l c θ₀) (rot l c (rotSol l c θ₀ t)) t := by
  have hc : HasDerivAt (fun t => Real.cos (l * t)) (-Real.sin (l * t) * (l * 1)) t :=
    (Real.hasDerivAt_cos (l * t)).comp t ((hasDerivAt_id t).const_mul l)
  have hs : HasDerivAt (fun t => Real.sin (l * t)) (Real.cos (l * t) * (l * 1)) t :=
    (Real.hasDerivAt_sin (l * t)).comp t ((hasDerivAt_id t).const_mul l)
  have h : HasDerivAt (rotSol l c θ₀)
      ((-Real.sin (l * t) * (l * 1)) • (θ₀ - c) + (Real.cos (l * t) * (l * 1)) • J (θ₀ - c)) t :=
    ((hc.smul_const (θ₀ - c)).const_add c).add (hs.smul_const (J (θ₀ - c)))
  have key : rot l c (rotSol l c θ₀ t) =
      (-Real.sin (l * t) * (l * 1)) • (θ₀ - c) + (Real.cos (l * t) * (l * 1)) • J (θ₀ - c) := by
    funext m; fin_cases m <;> simp [rot, rotSol] <;> ring
  rw [key]; exact h

/-- **(1) Periodicity** with period `2π/|λ|`. -/
theorem rotSol_periodic (l : ℝ) (c θ₀ : Fin 2 → ℝ) :
    Function.Periodic (rotSol l c θ₀) (2 * Real.pi / |l|) := by
  intro t
  rcases lt_trichotomy l 0 with hl | rfl | hl
  · have hl' : l ≠ 0 := hl.ne
    have : l * (t + 2 * Real.pi / |l|) = l * t - 2 * Real.pi := by
      rw [abs_of_neg hl]; field_simp; ring
    simp [rotSol, this, Real.cos_sub_two_pi, Real.sin_sub_two_pi]
  · simp [rotSol]
  · have hl' : l ≠ 0 := hl.ne'
    have : l * (t + 2 * Real.pi / |l|) = l * t + 2 * Real.pi := by
      rw [abs_of_pos hl]; field_simp
    simp [rotSol, this, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- **(1) Conservation of the Euclidean radius**: `|θ(t) − c|² = |θ₀ − c|²`. -/
theorem rotSol_dot (l : ℝ) (c θ₀ : Fin 2 → ℝ) (t : ℝ) :
    (rotSol l c θ₀ t - c) ⬝ᵥ (rotSol l c θ₀ t - c) = (θ₀ - c) ⬝ᵥ (θ₀ - c) := by
  simp only [rotSol, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    J_apply_zero, J_apply_one]
  linear_combination ((θ₀ 0 - c 0) ^ 2 + (θ₀ 1 - c 1) ^ 2) * Real.cos_sq_add_sin_sq (l * t)

/-- A point of the unit circle is `(cos s, sin s)` for some `s`. -/
theorem exists_cos_eq_sin_eq {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ s : ℝ, Real.cos s = a ∧ Real.sin s = b := by
  have hz : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
    have h2 : ‖(⟨a, b⟩ : ℂ)‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_mk]; nlinarith [h]
    nlinarith [norm_nonneg (⟨a, b⟩ : ℂ)]
  obtain ⟨s, hs⟩ := (Complex.norm_eq_one_iff _).1 hz
  refine ⟨s, ?_, ?_⟩
  · have := congrArg Complex.re hs
    simpa using this
  · have := congrArg Complex.im hs
    simpa using this

/-- **The orbit is the whole circle.** For `λ ≠ 0` the range of `rotSol` is the Euclidean circle around `c` through
`θ₀` (a point when `θ₀ = c`). -/
theorem rotSol_range {l : ℝ} (hl : l ≠ 0) (c θ₀ : Fin 2 → ℝ) :
    Set.range (rotSol l c θ₀) = {x | (x - c) ⬝ᵥ (x - c) = (θ₀ - c) ⬝ᵥ (θ₀ - c)} := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact rotSol_dot l c θ₀ t
  · intro hx
    have hx : (x - c) ⬝ᵥ (x - c) = (θ₀ - c) ⬝ᵥ (θ₀ - c) := hx
    set a := θ₀ - c with ha
    set y := x - c with hy
    have hx' : x = c + y := by simp [hy]
    have hθ : θ₀ = c + a := by simp [ha]
    by_cases hr : a ⬝ᵥ a = 0
    · have ha0 : a = 0 := dotProduct_self_eq_zero.1 hr
      have hy0 : y = 0 := dotProduct_self_eq_zero.1 (hx.trans hr)
      refine ⟨0, ?_⟩
      rw [rotSol_zero, hθ, hx', ha0, hy0]
    · set r := a ⬝ᵥ a with hr'
      have hcs : ((a ⬝ᵥ y) / r) ^ 2 + ((J a ⬝ᵥ y) / r) ^ 2 = 1 := by
        rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hr)]
        simp only [hr', dotProduct, Fin.sum_univ_two, J_apply_zero, J_apply_one] at hx ⊢
        linear_combination (a 0 ^ 2 + a 1 ^ 2) * hx
      obtain ⟨s, hcos, hsin⟩ := exists_cos_eq_sin_eq hcs
      refine ⟨s / l, ?_⟩
      have hls : l * (s / l) = s := mul_div_cancel₀ s hl
      rw [hx']
      simp only [rotSol, hls, hcos, hsin, ← ha]
      have hr0 : r ≠ 0 := hr
      ext m
      fin_cases m <;>
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue, Fin.mk_one,
          J_apply_zero, J_apply_one] <;>
        field_simp <;>
        simp only [hr', dotProduct, Fin.sum_univ_two, J_apply_zero, J_apply_one] <;>
        ring

/-- **(2) Uniqueness.** Every solution of `θ' = λ J(θ − c)` with `θ(0) = θ₀` is `rotSol λ c θ₀`.
Direct proof: `D(t) = |θ(t) − θ*(t)|²` has `D' = 2⟪θ − θ*, λ J(θ − θ*)⟫ = 0`, so `D ≡ D(0) = 0`. -/
theorem rotSol_unique (l : ℝ) (c θ₀ : Fin 2 → ℝ) (θ : ℝ → Fin 2 → ℝ)
    (hθ : ∀ t, HasDerivAt θ (rot l c (θ t)) t) (h0 : θ 0 = θ₀) : θ = rotSol l c θ₀ := by
  set d : ℝ → Fin 2 → ℝ := fun t => θ t - rotSol l c θ₀ t with hd
  have hd' : ∀ t, HasDerivAt d (l • J (d t)) t := by
    intro t
    have h := (hθ t).sub (hasDerivAt_rotSol l c θ₀ t)
    convert h using 1
    simp only [rot, hd]
    rw [← smul_sub, ← J_sub]
    congr 2
    abel
  set D : ℝ → ℝ := fun t => d t 0 ^ 2 + d t 1 ^ 2 with hD
  have hD' : ∀ t, HasDerivAt D 0 t := by
    intro t
    have h0' := hasDerivAt_pi.1 (hd' t) 0
    have h1' := hasDerivAt_pi.1 (hd' t) 1
    have h := (h0'.pow 2).add (h1'.pow 2)
    convert h using 1
    simp [Pi.smul_apply]
    ring
  have hconst : ∀ t, D t = D 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (hD' t).differentiableAt) (fun t => (hD' t).deriv) t 0
  have hD0 : D 0 = 0 := by simp [hD, hd, h0]
  funext t
  have ht : D t = 0 := (hconst t).trans hD0
  have h0t : d t 0 = 0 := by nlinarith [sq_nonneg (d t 0), sq_nonneg (d t 1)]
  have h1t : d t 1 = 0 := by nlinarith [sq_nonneg (d t 0), sq_nonneg (d t 1)]
  have : d t = 0 := by ext m; fin_cases m <;> assumption
  simpa [hd, sub_eq_zero] using this

/-- Existence and uniqueness together: the solutions of `θ' = λ J(θ − c)` through `θ₀` are exactly `rotSol`. -/
theorem solution_iff (l : ℝ) (c θ₀ : Fin 2 → ℝ) (θ : ℝ → Fin 2 → ℝ) :
    ((∀ t, HasDerivAt θ (rot l c (θ t)) t) ∧ θ 0 = θ₀) ↔ θ = rotSol l c θ₀ :=
  ⟨fun ⟨h, h0⟩ => rotSol_unique l c θ₀ θ h h0, fun h => h ▸ ⟨hasDerivAt_rotSol l c θ₀, rotSol_zero l c θ₀⟩⟩

/-! ## The rotation reward and its training field -/

section Field

variable {N K : Type*} [Fintype N] [DecidableEq N] [Fintype K] [DecidableEq K]

/-- `field` is additive in the reward family (pointwise differences), given differentiability. -/
theorem field_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (S : Finset N) (ξ : N → V)
    (W : N → K → ℝ) (R₁ R₂ : K → (N → V) → ℝ) (θ : V)
    (h₁ : ∀ k, DifferentiableAt ℝ (R₁ k) (embed S ξ θ)) (h₂ : ∀ k, DifferentiableAt ℝ (R₂ k) (embed S ξ θ)) :
    field S ξ W (fun k => R₁ k - R₂ k) θ = field S ξ W R₁ θ - field S ξ W R₂ θ := by
  simp only [field]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show R₁ k - R₂ k = fun x => R₁ k x - R₂ k x from rfl, fderiv_fun_sub (h₁ k) (h₂ k),
    ContinuousLinearMap.sub_comp, smul_sub]

/-- The rotation reward family: `R_{k₀}(x) = α(x_i)β(x_j) − β(x_i)α(x_j)` (the note's
`x_{j,1}x_{i,2} − x_{j,2}x_{i,1}` when `α = x₀`, `β = x₁`), other rewards zero. It is the difference of two of
`Potential.lean`'s bilinear test rewards, i.e. the quadratic reward with the antisymmetric off-diagonal block
`α ⊗ β − β ⊗ α`. -/
def rotFamily {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (k₀ : K) (i j : N) (α β : V →L[ℝ] ℝ) :
    K → (N → V) → ℝ :=
  fun k => testFamily k₀ i j α β k - testFamily k₀ i j β α k

theorem contDiff_rotFamily {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (k₀ : K) (i j : N)
    (α β : V →L[ℝ] ℝ) {n : WithTop ℕ∞} (k : K) : ContDiff ℝ n (rotFamily k₀ i j α β k) :=
  (contDiff_testFamily k₀ i j α β k).sub (contDiff_testFamily k₀ i j β α k)

theorem differentiable_testFamily {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (k₀ : K) (i j : N)
    (α β : V →L[ℝ] ℝ) (k : K) : Differentiable ℝ (testFamily k₀ i j α β k) :=
  (contDiff_testFamily (n := 1) k₀ i j α β k).differentiable one_ne_zero

/-- The field of the rotation reward, in general: `W_i (β(ι(θ)_j) α − α(ι(θ)_j) β) + W_j (α(ι(θ)_i) β − β(ι(θ)_i) α)`. -/
theorem field_rotFamily {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (S : Finset N) (ξ : N → V)
    (W : N → K → ℝ) (k₀ : K) (i j : N) (α β : V →L[ℝ] ℝ) (θ : V) :
    field S ξ W (rotFamily k₀ i j α β) θ =
      W i k₀ • (β (embed S ξ θ j) • α - α (embed S ξ θ j) • β) +
        W j k₀ • (α (embed S ξ θ i) • β - β (embed S ξ θ i) • α) := by
  unfold rotFamily
  rw [field_sub _ _ _ _ _ _ (fun k => (differentiable_testFamily k₀ i j α β k).differentiableAt)
    (fun k => (differentiable_testFamily k₀ i j β α k).differentiableAt), field_testFamily, field_testFamily]
  ext h
  simp
  ring

/-- Two instances `i, j ∈ S`: the field is `(W_i − W_j)(β(θ) α − α(θ) β)`. -/
theorem field_rotFamily_instances {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (S : Finset N)
    (ξ : N → V) (W : N → K → ℝ) (k₀ : K) {i j : N} (hi : i ∈ S) (hj : j ∈ S) (α β : V →L[ℝ] ℝ) (θ : V) :
    field S ξ W (rotFamily k₀ i j α β) θ = (W i k₀ - W j k₀) • (β θ • α - α θ • β) := by
  rw [field_rotFamily]
  ext h
  simp [embed, hi, hj]
  ring

/-- An external `e ∉ S` and an instance `s ∈ S`: the field is `W_e (β(θ) α − α(θ) β) + W_s (α(ξ_e) β − β(ξ_e) α)`,
affine in `θ`. -/
theorem field_rotFamily_external {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (S : Finset N)
    (ξ : N → V) (W : N → K → ℝ) (k₀ : K) {e s : N} (he : e ∉ S) (hs : s ∈ S) (α β : V →L[ℝ] ℝ) (θ : V) :
    field S ξ W (rotFamily k₀ e s α β) θ =
      W e k₀ • (β θ • α - α θ • β) + W s k₀ • (α (ξ e) • β - β (ξ e) • α) := by
  rw [field_rotFamily]
  simp [embed, he, hs]

/-- The coordinate rotation reward on `ℝ²`: `R_{k₀}(x) = x_{i,0} x_{j,1} − x_{i,1} x_{j,0}`. -/
noncomputable abbrev rotReward (k₀ : K) (i j : N) : K → (N → (Fin 2 → ℝ)) → ℝ :=
  rotFamily k₀ i j (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)

theorem toVec_rotCov (a b : ℝ) :
    toVec (a • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 -
      b • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) = ![a, -b] := by
  ext m; fin_cases m <;> simp [toVec]

/-- **(3) Two instances with weights `W_i, W_j`**: under the Euclidean identification the training field of the
rotation reward is the linear rotation `(W_i − W_j) J θ = (W_i − W_j)(θ₁, −θ₀)`, i.e. `rot (W_i − W_j) 0`. -/
theorem toVec_field_rotFamily_instances (S : Finset N) (ξ : N → (Fin 2 → ℝ)) (W : N → K → ℝ) (k₀ : K)
    {i j : N} (hi : i ∈ S) (hj : j ∈ S) (θ : Fin 2 → ℝ) :
    toVec (field S ξ W (rotReward k₀ i j) θ) = rot (W i k₀ - W j k₀) 0 θ := by
  rw [rotReward, field_rotFamily_instances S ξ W k₀ hi hj]
  ext m; fin_cases m <;> simp [toVec, rot]

/-- **(3) An external `e` with weight `W_e` and an instance `s`**: the training field is the affine rotation
`W_e J θ − W_s J ξ_e`; for `W_e ≠ 0` this is `rot W_e c` with centre `c = (W_s / W_e) ξ_e`. -/
theorem toVec_field_rotFamily_external (S : Finset N) (ξ : N → (Fin 2 → ℝ)) (W : N → K → ℝ) (k₀ : K)
    {e s : N} (he : e ∉ S) (hs : s ∈ S) (θ : Fin 2 → ℝ) :
    toVec (field S ξ W (rotReward k₀ e s) θ) = W e k₀ • J θ - W s k₀ • J (ξ e) := by
  rw [rotReward, field_rotFamily_external S ξ W k₀ he hs]
  ext m; fin_cases m <;> simp [toVec, sub_eq_add_neg]

theorem toVec_field_rotFamily_external_rot (S : Finset N) (ξ : N → (Fin 2 → ℝ)) (W : N → K → ℝ) (k₀ : K)
    {e s : N} (he : e ∉ S) (hs : s ∈ S) (hW : W e k₀ ≠ 0) (θ : Fin 2 → ℝ) :
    toVec (field S ξ W (rotReward k₀ e s) θ) = rot (W e k₀) ((W s k₀ / W e k₀) • ξ e) θ := by
  rw [toVec_field_rotFamily_external S ξ W k₀ he hs, rot, J_sub, J_smul, smul_sub, smul_smul,
    mul_div_cancel₀ _ hW]

/-- **If (ii) fails, a bilinear reward makes the training field a rotation.** For `S ≠ ∅` and `W` not Kantian there
are a reward slot `k₀` and slots `i, j` such that the training field of the coordinate rotation reward
`rotReward k₀ i j` is `λ J(θ − c)` with `λ ≠ 0` (between two instances `c = 0`; between an external and an instance
the centre is shifted). -/
theorem exists_rotation_of_not_isKantian (S : Finset N) (hS : S.Nonempty) (ξ : N → (Fin 2 → ℝ))
    (W : N → K → ℝ) (hW : ¬ IsKantian S W) :
    ∃ (k₀ : K) (i j : N) (l : ℝ) (c : Fin 2 → ℝ), l ≠ 0 ∧
      ∀ θ, toVec (field S ξ W (rotReward k₀ i j) θ) = rot l c θ := by
  obtain ⟨s₀, hs₀⟩ := hS
  simp only [IsKantian, not_exists, not_forall] at hW
  obtain ⟨j, k, hjk⟩ := hW (fun k => W s₀ k)
  by_cases hj : j ∈ S
  · simp only [hj, ite_true] at hjk
    exact ⟨k, j, s₀, W j k - W s₀ k, 0, sub_ne_zero.2 hjk,
      fun θ => toVec_field_rotFamily_instances S ξ W k hj hs₀ θ⟩
  · simp only [hj, ite_false] at hjk
    exact ⟨k, j, s₀, W j k, (W s₀ k / W j k) • ξ j, hjk,
      fun θ => toVec_field_rotFamily_external_rot S ξ W k hj hs₀ hjk θ⟩

/-- **Closed orbits.** For `S ≠ ∅` and `W` not Kantian there is a coordinate rotation reward such that every solution
`θ` of the training flow `θ' = toVec (F_W(θ))` (Euclidean identification) with `θ(0) = θ₀` is a closed curve: it is
periodic with period `2π/|λ|` for some `λ ≠ 0`, and its orbit is exactly a Euclidean circle (around some centre `c`,
through `θ₀`; a single point when `θ₀ = c`). Moreover such a solution exists for every `θ₀`. -/
theorem orbits_closed_of_not_isKantian (S : Finset N) (hS : S.Nonempty) (ξ : N → (Fin 2 → ℝ))
    (W : N → K → ℝ) (hW : ¬ IsKantian S W) :
    ∃ (k₀ : K) (i j : N) (l : ℝ) (c : Fin 2 → ℝ), l ≠ 0 ∧
      ∀ θ₀ : Fin 2 → ℝ,
        (∃ θ : ℝ → Fin 2 → ℝ, (∀ t, HasDerivAt θ (toVec (field S ξ W (rotReward k₀ i j) (θ t))) t) ∧ θ 0 = θ₀) ∧
        ∀ θ : ℝ → Fin 2 → ℝ, (∀ t, HasDerivAt θ (toVec (field S ξ W (rotReward k₀ i j) (θ t))) t) → θ 0 = θ₀ →
          θ = rotSol l c θ₀ ∧ Function.Periodic θ (2 * Real.pi / |l|) ∧
            Set.range θ = {x | (x - c) ⬝ᵥ (x - c) = (θ₀ - c) ⬝ᵥ (θ₀ - c)} := by
  obtain ⟨k₀, i, j, l, c, hl, hF⟩ := exists_rotation_of_not_isKantian S hS ξ W hW
  refine ⟨k₀, i, j, l, c, hl, fun θ₀ => ⟨⟨rotSol l c θ₀, fun t => ?_, rotSol_zero l c θ₀⟩, fun θ hθ h0 => ?_⟩⟩
  · rw [hF]; exact hasDerivAt_rotSol l c θ₀ t
  · have hθ' : ∀ t, HasDerivAt θ (rot l c (θ t)) t := fun t => by rw [← hF]; exact hθ t
    have heq := rotSol_unique l c θ₀ θ hθ' h0
    subst heq
    exact ⟨rfl, rotSol_periodic l c θ₀, rotSol_range hl c θ₀⟩

end Field

/-! ## (4) Closed orbits imply no potential -/

/-- **A periodic non-stationary orbit rules out a potential.** If `F` is conservative and `θ` solves
`θ' = toVec (F θ)` (so `d/dt φ(θ(t)) = F(θ)(θ') = |toVec (F θ)|² ≥ 0`), is periodic with period `T`, and is not
stationary at time `0`, we get a contradiction: `φ ∘ θ` is monotone and returns to its value, so it is constant near
`0`, yet its derivative there is `|toVec (F θ₀)|² > 0`. -/
theorem not_conservative_of_periodic_orbit (F : (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ) (θ : ℝ → Fin 2 → ℝ)
    (hθ : ∀ t, HasDerivAt θ (toVec (F (θ t))) t) {T : ℝ} (hT0 : T ≠ 0) (hT : Function.Periodic θ T)
    (hne : toVec (F (θ 0)) ≠ 0) : ¬ Conservative F := by
  rintro ⟨φ, hφ⟩
  -- the potential along the orbit
  set g : ℝ → ℝ := fun t => φ (θ t) with hg
  have hg' : ∀ t, HasDerivAt g (toVec (F (θ t)) ⬝ᵥ toVec (F (θ t))) t := by
    intro t
    have h := (hφ (θ t)).comp_hasDerivAt t (hθ t)
    rw [toVec_dot]
    exact h
  have hmono : Monotone g :=
    monotone_of_deriv_nonneg (fun t => (hg' t).differentiableAt)
      (fun t => by rw [(hg' t).deriv]; simpa using dotProduct_self_star_nonneg (toVec (F (θ t))))
  -- `g` is constant on `[-|T|, |T|]`, hence near `0`
  have hper : ∀ n : ℤ, g (n * T) = g 0 := fun n => by
    simp [hg, (hT.int_mul n).eq]
  have hconst : ∀ t, -|T| ≤ t → t ≤ |T| → g t = g 0 := by
    intro t h1 h2
    rcases le_or_gt 0 T with hT0 | hT0
    · rw [abs_of_nonneg hT0] at h1 h2
      refine le_antisymm ?_ ?_
      · calc g t ≤ g ((1 : ℤ) * T) := hmono (by simpa using h2)
          _ = g 0 := hper 1
      · calc g 0 = g ((-1 : ℤ) * T) := (hper (-1)).symm
          _ ≤ g t := hmono (by simpa using h1)
    · rw [abs_of_neg hT0] at h1 h2
      refine le_antisymm ?_ ?_
      · calc g t ≤ g ((-1 : ℤ) * T) := hmono (by simpa using h2)
          _ = g 0 := hper (-1)
      · calc g 0 = g ((1 : ℤ) * T) := (hper 1).symm
          _ ≤ g t := hmono (by simpa using h1)
  -- so its derivative at `0` is `0`, but it is `|toVec (F θ₀)|² > 0`
  have hTpos : 0 < |T| := abs_pos.2 hT0
  have hderiv0 : HasDerivAt g 0 0 := by
    have hev : g =ᶠ[nhds 0] fun _ => g 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hTpos] with t ht
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact hconst t (by linarith [abs_le.1 ht.le]) (by linarith [abs_le.1 ht.le])
    exact (hasDerivAt_const (0 : ℝ) (g 0)).congr_of_eventuallyEq hev
  have := (hg' 0).unique hderiv0
  exact hne (dotProduct_self_eq_zero.1 this)

/-- **A rotation field has no potential, by its closed orbits.** If `toVec ∘ F = rot l c` with `l ≠ 0`, the orbit
through `c + e₀` is a non-stationary closed curve, so `F` is not conservative. -/
theorem not_conservative_of_rot (F : (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ) {l : ℝ} (hl : l ≠ 0)
    (c : Fin 2 → ℝ) (hF : ∀ θ, toVec (F θ) = rot l c θ) : ¬ Conservative F := by
  set θ₀ : Fin 2 → ℝ := c + Pi.single 0 1 with hθ₀
  refine not_conservative_of_periodic_orbit F (rotSol l c θ₀) (fun t => ?_) (T := 2 * Real.pi / |l|) ?_
    (rotSol_periodic l c θ₀) ?_
  · rw [hF]; exact hasDerivAt_rotSol l c θ₀ t
  · exact div_ne_zero (by positivity) (abs_ne_zero.2 hl)
  · rw [rotSol_zero, hF]
    intro h
    have := congrFun h 1
    simp [rot, hθ₀] at this
    exact hl this

section Corollaries

variable {N K : Type*} [Fintype N] [DecidableEq N] [Fintype K] [DecidableEq K]

/-- **Non-conservativity re-derived from the closed orbits** (compare `Potential.cdt_not_conservative`, which uses the
symmetry of second derivatives): two instances with different weights, rotation reward, `V = ℝ²`. -/
theorem rotation_not_conservative (S : Finset N) (ξ : N → (Fin 2 → ℝ)) (W : N → K → ℝ) (k₀ : K) {i j : N}
    (hi : i ∈ S) (hj : j ∈ S) (hW : W i k₀ ≠ W j k₀) : ¬ Conservative (field S ξ W (rotReward k₀ i j)) :=
  not_conservative_of_rot _ (sub_ne_zero.2 hW) 0 (toVec_field_rotFamily_instances S ξ W k₀ hi hj)

/-- **(i) ⇒ (ii) of part (C) on `ℝ²`, via orbits.** If `S ≠ ∅` and `W` is not Kantian, some coordinate rotation
reward (a C^∞, indeed bilinear, family) has a non-conservative field. -/
theorem not_conservative_of_not_isKantian (S : Finset N) (hS : S.Nonempty) (ξ : N → (Fin 2 → ℝ))
    (W : N → K → ℝ) (hW : ¬ IsKantian S W) :
    ∃ (k₀ : K) (i j : N), ¬ Conservative (field S ξ W (rotReward k₀ i j)) := by
  obtain ⟨k₀, i, j, l, c, hl, hF⟩ := exists_rotation_of_not_isKantian S hS ξ W hW
  exact ⟨k₀, i, j, not_conservative_of_rot _ hl c hF⟩

/-- The same training field through `Causal.lean`'s dictionary (`field_eq_causalField`): the causal field with
response `r = 1_S`, base states `ξ` off `S`, and scalar credits `W` is the same rotation. -/
theorem toVec_causalField_rotReward (S : Finset N) (ξ : N → (Fin 2 → ℝ)) (W : N → K → ℝ) (k₀ : K)
    {i j : N} (hi : i ∈ S) (hj : j ∈ S) (θ : Fin 2 → ℝ) :
    toVec (Causal.causalField (Causal.linResp (fun j => if j ∈ S then 1 else 0) (fun j => if j ∈ S then 0 else ξ j))
      (Causal.scalarA W) (rotReward k₀ i j) θ) = rot (W i k₀ - W j k₀) 0 θ := by
  rw [← Causal.field_eq_causalField]
  exact toVec_field_rotFamily_instances S ξ W k₀ hi hj θ

end Corollaries

end BoundaryTheorem.Orbits
