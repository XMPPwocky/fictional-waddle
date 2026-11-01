import BoundaryTheorem.Potential
open BoundaryTheorem.Potential

-- (a) `2 : WithTop ℕ∞` really is the natural number 2 (not ∞ or ω).
example : (2 : WithTop ℕ∞) = ((2 : ℕ) : ℕ∞) := rfl
example : (2 : WithTop ℕ∞) ≠ ⊤ := by decide
example : (2 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by decide

variable {N K V : Type*} [Fintype N] [DecidableEq N] [Fintype K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

-- (b) `field` applied to a direction h is Σ_{j,k} W_jk · DR_k(ι(θ))[h in slot j]: the slot-j partial derivative.
example (S : Finset N) (ξ : N → V) (W : N → K → ℝ) (R : K → (N → V) → ℝ) (θ h : V) :
    field S ξ W R θ h = ∑ j, ∑ k, W j k * fderiv ℝ (R k) (embed S ξ θ) (Pi.single j h) := by
  simp [field, ContinuousLinearMap.sum_apply]

-- (c) `embed`: θ in instance slots, ξ in external slots.
example (S : Finset N) (ξ : N → V) (θ : V) (j : N) (hj : j ∈ S) : embed S ξ θ j = θ := by simp [embed, hj]
example (S : Finset N) (ξ : N → V) (θ : V) (j : N) (hj : j ∉ S) : embed S ξ θ j = ξ j := by simp [embed, hj]

-- (d) `Conservative` gives a differentiable global potential whose Fréchet derivative is F everywhere.
example (F : V → V →L[ℝ] ℝ) (h : Conservative F) :
    ∃ φ : V → ℝ, Differentiable ℝ φ ∧ ∀ θ, fderiv ℝ φ θ = F θ := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ, fun θ => (hφ θ).differentiableAt, fun θ => (hφ θ).fderiv⟩

-- (e) (i) is satisfiable (the Kantian W with c = 1), so (i) ⇒ (ii) is not vacuous; and (i) fails for CDT.
example [FiniteDimensional ℝ V] (S : Finset N) (hS : S.Nonempty) (h2 : 2 ≤ Module.finrank ℝ V) (ξ : N → V) :
    ∀ R : K → (N → V) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) →
      Conservative (field S ξ (fun j (_ : K) => if j ∈ S then (1:ℝ) else 0) R) :=
  (potential_iff S hS h2 ξ _).2 ⟨fun _ => 1, fun _ _ => rfl⟩

-- (f) The CDT shear field θ ↦ β(θ)α is NOT skew-symmetric as a bilinear form (the task brief's parenthetical
-- is wrong about it): on a dual pair, B(v,u) = 1 but B(u,v) = 0.
example {α β : V →L[ℝ] ℝ} {u v : V} (hαu : α u = 1) (hαv : α v = 0) (hβu : β u = 0) (hβv : β v = 1) :
    ¬ (∀ x y, β x * α y = -(β y * α x)) := by
  intro h; have := h v u; simp [hαu, hαv, hβu, hβv] at this
