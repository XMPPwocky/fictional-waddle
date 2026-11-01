import Mathlib

/-!
# Forking pasts, funnelled futures: ancestry is forward × backward

Forward: `M u = lam • u` (the population). Backward: `vᵀ M = lam • vᵀ` (reproductive value).
The lineage ("where did a type-i individual's parent come from") kernel is
`B i j = M i j * u j / (lam * u i)`. We prove it is a transition kernel and that its stationary
distribution is the product `u ∘ v`: ancestors are distributed as forward × backward
(Georgii & Baake 2003; Hermisson et al. 2002). With symmetric mutation the two coincide up to a
diagonal factor, so ancestry is a Born-style square, and squaring is cooling (C1, below).
-/

open Finset

namespace ForwardBackward

variable {n : ℕ}

/-- The lineage kernel is row-stochastic. -/
theorem lineage_rows_sum_one (M : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (lam : ℝ)
    (hlam : lam ≠ 0) (hu : ∀ i, u i ≠ 0) (hright : ∀ i, ∑ j, M i j * u j = lam * u i) (i : Fin n) :
    ∑ j, M i j * u j / (lam * u i) = 1 := by
  rw [← Finset.sum_div, hright i]
  field_simp [hu i]

/-- **Ancestry is forward × backward.** The product `u ∘ v` is stationary for the lineage kernel. -/
theorem ancestry_is_forward_times_backward (M : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) (lam : ℝ)
    (hlam : lam ≠ 0) (hu : ∀ i, u i ≠ 0)
    (hleft : ∀ j, ∑ i, v i * M i j = lam * v j) (j : Fin n) :
    ∑ i, (u i * v i) * (M i j * u j / (lam * u i)) = u j * v j := by
  calc ∑ i, (u i * v i) * (M i j * u j / (lam * u i))
      = ∑ i, (u j / lam) * (v i * M i j) := by
        apply Finset.sum_congr rfl; intro i _; field_simp [hu i]
    _ = (u j / lam) * ∑ i, v i * M i j := by rw [Finset.mul_sum]
    _ = u j * v j := by rw [hleft j]; field_simp

end ForwardBackward

namespace Cooling

/-- **C1 (squaring is cooling)**, statement copied verbatim from AgentIdentityStatements.lean. -/
theorem square_is_half_temperature {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (i : Fin n) :
    p i ^ 2 / ∑ j, p j ^ 2 = Real.exp (2 * Real.log (p i)) / ∑ j, Real.exp (2 * Real.log (p j)) := by
  have h : ∀ k, Real.exp (2 * Real.log (p k)) = p k ^ 2 := by
    intro k
    rw [show (2 : ℝ) * Real.log (p k) = Real.log (p k) + Real.log (p k) by ring, Real.exp_add,
      Real.exp_log (hp k)]
    ring
  simp only [h]

end Cooling

#print axioms ForwardBackward.lineage_rows_sum_one
#print axioms ForwardBackward.ancestry_is_forward_times_backward
#print axioms Cooling.square_is_half_temperature
