import BoundaryTheorem.ZeroBias
open MeasureTheory ZeroBias
-- critic sanity: the definitions are the note's objects, not degenerate ones
example {n d : ℕ} (j : Fin n) (α : Fin d) : unitVec j α j α = 1 := by simp [unitVec]
example {n d : ℕ} (j j' : Fin n) (α β : Fin d) (h : j ≠ j') : unitVec j α j' β = 0 := by simp [unitVec, h.symm]
example {n d : ℕ} (θ : Fin d → ℝ) (r : Fin n → ℝ) (ε : Fin d → ℝ) (η : Dice n d) (j : Fin n) (β : Fin d) :
    (iota (n := n) θ + delta r ε η) j β = θ β + (r j * ε β + η j β) := by simp [iota, delta]
-- partialD of the coordinate functional x ↦ x j α is 1 (so partialD is ∂_{x_j^α})
example {n d : ℕ} (j : Fin n) (α : Fin d) (x : Dice n d) :
    partialD (fun y : Dice n d => y j α) j α x = 1 := by
  unfold partialD
  let L : Dice n d →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) α).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin d → ℝ) j)
  have h : (fun y : Dice n d => y j α) = L := rfl
  rw [h, ContinuousLinearMap.fderiv]
  simp [L, unitVec]
example {n d : ℕ} (j j' : Fin n) (α : Fin d) (x : Dice n d) (h : j ≠ j') :
    partialD (fun y : Dice n d => y j' α) j α x = 0 := by
  unfold partialD
  let L : Dice n d →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) α).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin d → ℝ) j')
  have hh : (fun y : Dice n d => y j' α) = L := rfl
  rw [hh, ContinuousLinearMap.fderiv]
  simp [L, unitVec, h.symm]
example (P₀ : Measure ℝ) (σ2 : ℝ) {d : ℕ} (α : Fin d) :
    tiltedLaw P₀ σ2 α = Measure.pi (fun i => if i = α then zeroBias P₀ σ2 else P₀) := rfl
example (P₀ : Measure ℝ) (d : ℕ) : diceLaw P₀ d = Measure.pi (fun _ : Fin d => P₀) := rfl
example (P₀ : Measure ℝ) (t : ℝ) : kappa P₀ t = ∫ s in Set.Ioi t, s ∂P₀ := rfl
