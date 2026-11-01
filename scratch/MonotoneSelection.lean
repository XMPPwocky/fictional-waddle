import Mathlib

/-!
# Monotone selection never climbs down (the core of Sourbut 2022, without radial symmetry)

Mutations come in antithetic pairs `±ε` with weights `w`. To first order, a mutation's fitness change is
`δ = ε · ∇f`. A selection rule `P` keeps a mutant with probability `P δ`, monotone nondecreasing in the fitness
change. The expected first-order progress of the kept step along the gradient is `∑ w δ (P δ − P (−δ))`.

* M1 `monotone_selection_never_climbs_down`: that progress is `≥ 0` for ANY weights, ANY mutation directions and ANY
  monotone selection rule. Radial symmetry (Sourbut's assumption 3) is not needed, only antithetic pairing.
* M2 `strict_selection_climbs`: if `P` is strictly increasing and some mutation with positive weight has `δ ≠ 0`,
  progress is strictly positive.
-/

namespace MonotoneSelection

/-- **M1.** -/
theorem monotone_selection_never_climbs_down {ι : Type*} [Fintype ι] (w δ : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (P : ℝ → ℝ) (hP : Monotone P) : 0 ≤ ∑ i, w i * δ i * (P (δ i) - P (-δ i)) := by
  have term : ∀ i, 0 ≤ δ i * (P (δ i) - P (-δ i)) := by
    intro i
    rcases le_total 0 (δ i) with h | h
    · exact mul_nonneg h (by linarith [hP (show -δ i ≤ δ i by linarith)])
    · exact mul_nonneg_of_nonpos_of_nonpos h (by linarith [hP (show δ i ≤ -δ i by linarith)])
  exact Finset.sum_nonneg (fun i _ => by rw [mul_assoc]; exact mul_nonneg (hw i) (term i))

/-- **M2.** -/
theorem strict_selection_climbs {ι : Type*} [Fintype ι] (w δ : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (P : ℝ → ℝ)
    (hP : StrictMono P) (j : ι) (hj : 0 < w j) (hδ : δ j ≠ 0) : 0 < ∑ i, w i * δ i * (P (δ i) - P (-δ i)) := by
  have term : ∀ i, 0 ≤ δ i * (P (δ i) - P (-δ i)) := by
    intro i
    rcases le_total 0 (δ i) with h | h
    · exact mul_nonneg h (by linarith [hP.monotone (show -δ i ≤ δ i by linarith)])
    · exact mul_nonneg_of_nonpos_of_nonpos h (by linarith [hP.monotone (show δ i ≤ -δ i by linarith)])
  have strict : 0 < δ j * (P (δ j) - P (-δ j)) := by
    rcases lt_or_gt_of_ne hδ with h | h
    · exact mul_pos_of_neg_of_neg h (by linarith [hP (show δ j < -δ j by linarith)])
    · exact mul_pos h (by linarith [hP (show -δ j < δ j by linarith)])
  calc 0 < w j * δ j * (P (δ j) - P (-δ j)) := by rw [mul_assoc]; exact mul_pos hj strict
    _ ≤ ∑ i, w i * δ i * (P (δ i) - P (-δ i)) :=
        Finset.single_le_sum (f := fun i => w i * δ i * (P (δ i) - P (-δ i)))
          (fun i _ => by rw [mul_assoc]; exact mul_nonneg (hw i) (term i)) (Finset.mem_univ j)

end MonotoneSelection
