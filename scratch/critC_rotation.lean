import BoundaryTheorem.Potential
/-!
Critic scratch (part C): the note's "rotation" clause, in the Lean dictionary.
The rotation reward `R(x) = α(x_i)β(x_j) − β(x_i)α(x_j)` (the note's `x_{j,1}x_{i,2} − x_{j,2}x_{i,1}`) has field
`(W_i − W_j)·(β(θ)α − α(θ)β)` for instances i, j, whose derivative is a NONZERO SKEW-SYMMETRIC bilinear form
(the Damascus field `(θ₂, −θ₁)` for `V = ℝ²`). Not the closed-orbit statement, only its infinitesimal form.
-/
open Finset BoundaryTheorem.Potential

namespace CritC

variable {N K V : Type*} [Fintype N] [DecidableEq N] [Fintype K] [DecidableEq K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `field` is linear in the reward family (pointwise differences), given differentiability. -/
theorem field_sub (S : Finset N) (ξ : N → V) (W : N → K → ℝ) (R₁ R₂ : K → (N → V) → ℝ) (θ : V)
    (h₁ : ∀ k, DifferentiableAt ℝ (R₁ k) (embed S ξ θ)) (h₂ : ∀ k, DifferentiableAt ℝ (R₂ k) (embed S ξ θ)) :
    field S ξ W (fun k => R₁ k - R₂ k) θ = field S ξ W R₁ θ - field S ξ W R₂ θ := by
  simp only [field]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show R₁ k - R₂ k = fun x => R₁ k x - R₂ k x from rfl, fderiv_fun_sub (h₁ k) (h₂ k),
    ContinuousLinearMap.sub_comp, smul_sub]

/-- The rotation family: `α(x_i)β(x_j) − β(x_i)α(x_j)` in reward slot `k₀`, zero elsewhere. -/
def rotFamily (k₀ : K) (i j : N) (α β : V →L[ℝ] ℝ) : K → (N → V) → ℝ :=
  fun k => testFamily k₀ i j α β k - testFamily k₀ i j β α k

theorem differentiable_testFamily (k₀ : K) (i j : N) (α β : V →L[ℝ] ℝ) (k : K) :
    Differentiable ℝ (testFamily k₀ i j α β k) :=
  (contDiff_testFamily (n := 2) k₀ i j α β k).differentiable (by norm_num)

/-- For two instances `i, j ∈ S` the field of the rotation reward is `(W_i − W_j)(β(θ)α − α(θ)β)`. -/
theorem field_rotFamily (S : Finset N) (ξ : N → V) (W : N → K → ℝ) (k₀ : K) {i j : N}
    (hi : i ∈ S) (hj : j ∈ S) (α β : V →L[ℝ] ℝ) (θ : V) :
    field S ξ W (rotFamily k₀ i j α β) θ = (W i k₀ - W j k₀) • (β θ • α - α θ • β) := by
  unfold rotFamily
  rw [field_sub _ _ _ _ _ _ (fun k => (differentiable_testFamily k₀ i j α β k).differentiableAt)
    (fun k => (differentiable_testFamily k₀ i j β α k).differentiableAt), field_testFamily, field_testFamily]
  ext h
  simp [embed, hi, hj]
  ring

/-- The derivative of that field is the bilinear form `(v, w) ↦ (W_i − W_j)(β v α w − α v β w)` ... -/
noncomputable def rotForm (α β : V →L[ℝ] ℝ) : V →L[ℝ] V →L[ℝ] ℝ := β.smulRight α - α.smulRight β

theorem hasFDerivAt_field_rotFamily (S : Finset N) (ξ : N → V) (W : N → K → ℝ) (k₀ : K) {i j : N}
    (hi : i ∈ S) (hj : j ∈ S) (α β : V →L[ℝ] ℝ) (θ : V) :
    HasFDerivAt (field S ξ W (rotFamily k₀ i j α β)) ((W i k₀ - W j k₀) • rotForm α β) θ := by
  have : field S ξ W (rotFamily k₀ i j α β) = fun θ => ((W i k₀ - W j k₀) • rotForm α β) θ := by
    funext θ; rw [field_rotFamily S ξ W k₀ hi hj]; ext h; simp [rotForm]
  rw [this]; exact ((W i k₀ - W j k₀) • rotForm α β).hasFDerivAt

/-- ... which is skew-symmetric, -/
theorem rotForm_skew (α β : V →L[ℝ] ℝ) (v w : V) : rotForm α β v w = - rotForm α β w v := by
  simp [rotForm]; ring

/-- ... and nonzero (hence `(W_i − W_j) • rotForm` is a nonzero skew map iff `W_i ≠ W_j`): on a dual pair it
sends `(u, v) ↦ −1`. -/
theorem rotForm_ne_zero {α β : V →L[ℝ] ℝ} {u v : V}
    (hαu : α u = 1) (hαv : α v = 0) (hβu : β u = 0) (hβv : β v = 1) : rotForm α β ≠ 0 := by
  intro h
  have := congrArg (fun T : V →L[ℝ] V →L[ℝ] ℝ => T u v) h
  simp [rotForm, hαu, hαv, hβu, hβv] at this

theorem rot_deriv_ne_zero_of_ne {α β : V →L[ℝ] ℝ} {u v : V}
    (hαu : α u = 1) (hαv : α v = 0) (hβu : β u = 0) (hβv : β v = 1) {a b : ℝ} (hab : a ≠ b) :
    (a - b) • rotForm α β ≠ 0 := by
  intro h
  have := congrArg (fun T : V →L[ℝ] V →L[ℝ] ℝ => T u v) h
  simp [rotForm, hαu, hαv, hβu, hβv, sub_eq_zero] at this
  exact hab this.symm

/-- The Damascus field in coordinates: `V = ℝ²`, `α = x₀`, `β = x₁`, CDT between instances `a ≠ t`:
`F(θ)(h) = θ₁ h₀ − θ₀ h₁`, i.e. the vector field `(θ₁, −θ₀)`. -/
theorem damascus_field (S : Finset N) (ξ : N → (Fin 2 → ℝ)) (k₀ : K) {a t : N} (ha : a ∈ S) (ht : t ∈ S)
    (hat : a ≠ t) (θ h : Fin 2 → ℝ) :
    field S ξ (fun j k => if j = a ∧ k = k₀ then (1:ℝ) else 0)
      (rotFamily k₀ a t (ContinuousLinearMap.proj 0) (ContinuousLinearMap.proj 1)) θ h
      = θ 1 * h 0 - θ 0 * h 1 := by
  rw [field_rotFamily S ξ _ k₀ ha ht]
  simp [hat.symm]

/-- Its linear map `θ ↦ (θ₁, −θ₀)` is skew for the dot product and nonzero. -/
theorem damascus_skew (θ θ' : Fin 2 → ℝ) :
    dotProduct ![θ 1, -θ 0] θ' = - dotProduct θ ![θ' 1, -θ' 0] := by
  simp [dotProduct, Fin.sum_univ_two]

theorem damascus_ne_zero : (fun θ : Fin 2 → ℝ => ![θ 1, -θ 0]) ≠ 0 := by
  intro h
  have := congrFun (congrFun h ![0, 1]) 0
  simp at this

end CritC

#print axioms CritC.hasFDerivAt_field_rotFamily
#print axioms CritC.rotForm_skew
#print axioms CritC.rot_deriv_ne_zero_of_ne
#print axioms CritC.damascus_field
