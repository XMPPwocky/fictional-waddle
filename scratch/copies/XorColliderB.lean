import Mathlib

/-!
# XorColliderB

Sample space `Ω = Bool × Bool` with the explicit uniform measure
`μ = 4⁻¹ • ∑ ω, dirac ω`. Coordinates `X = fst`, `Y = snd`, and the collider
`Z = X xor Y`.

PROVED
* `μ_apply`: `μ A = 4⁻¹ * #A`, written as a sum of indicators.
* `μ_singleton`: every outcome has probability `1/4` (the measure is uniform).
* `μ_univ`, `isProbabilityMeasure_μ`: `μ` is a probability measure.
* `X_fair`, `Y_fair`, `Z_fair`: each of `X`, `Y`, `Z` takes each value with probability `1/2`.
* `indep_X_Y`: `X` and `Y` are independent under `μ`.
* `indep_X_Z`: `X` and `Z` are independent under `μ`.
* `indep_Y_Z`: `Y` and `Z` are independent under `μ`.
* `not_indep_XY_Z`: the pair `(X, Y)` is not independent of `Z`
  (pairwise independence without joint independence).
* `prob_Z_false`: `P(Z = 0) = 1/2`.
* `cond_X_eq_Y`: `P(X = Y | Z = 0) = 1`.
* `cond_X_ne_Y`: `P(X ≠ Y | Z = 0) = 0`.
* `ae_cond_Y_eq_X`: conditional on `Z = 0`, `Y = X` almost surely (X determines Y).
* `cond_X_eq_Y_of_Z_true`: `P(X = Y | Z = 1) = 0`.
* `not_indep_X_Y_cond`: conditional on `Z = 0`, `X` and `Y` are not independent.
* `collider`: the conjunction: `X ⟂ Y`, `X ⟂ Z`, `P(X = Y | Z = 0) = 1`, and
  `X`, `Y` dependent given `Z = 0`.

INTERPRETED
* "fair bit" is the uniform law on `Bool`; "Z = 0" is `Z = false`; "Z = 1" is `Z = true`.
* Conditioning is `ProbabilityTheory.cond` (`μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option linter.unusedSimpArgs false

namespace XorColliderB

abbrev Ω := Bool × Bool

/-- The uniform probability measure on `Bool × Bool`. -/
noncomputable def μ : Measure Ω := (4 : ℝ≥0∞)⁻¹ • ∑ ω : Ω, Measure.dirac ω

def X : Ω → Bool := Prod.fst
def Y : Ω → Bool := Prod.snd
def Z : Ω → Bool := fun ω => xor ω.1 ω.2

theorem μ_apply (A : Set Ω) :
    μ A = (4 : ℝ≥0∞)⁻¹ * ∑ ω : Ω, A.indicator 1 ω := by
  simp [μ, Measure.finsetSum_apply, Measure.dirac_apply]

theorem two_inv_sq : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ = 4⁻¹ := by
  rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  norm_num

theorem four_inv_mul_two : (4 : ℝ≥0∞)⁻¹ * 2 = 2⁻¹ := by
  rw [← two_inv_sq, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

theorem four_inv_mul_four : (4 : ℝ≥0∞)⁻¹ * 4 = 1 :=
  ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem one_add_one' : (1 : ℝ≥0∞) + 1 = 2 := one_add_one_eq_two

theorem two_add_two' : (2 : ℝ≥0∞) + 2 = 4 := by norm_num

theorem measurableSet_Ω (A : Set Ω) : MeasurableSet A := (Set.to_countable A).measurableSet

theorem μ_singleton (ω : Ω) : μ {ω} = 4⁻¹ := by
  obtain ⟨a, b⟩ := ω
  rw [μ_apply]
  cases a <;> cases b <;> simp [Fintype.sum_prod_type, Set.indicator_apply]

theorem μ_univ : μ Set.univ = 1 := by
  rw [μ_apply]
  simp [Fintype.sum_prod_type, one_add_one', two_add_two', four_inv_mul_four]

instance isProbabilityMeasure_μ : IsProbabilityMeasure μ := ⟨μ_univ⟩

theorem X_fair (b : Bool) : μ (X ⁻¹' {b}) = 2⁻¹ := by
  rw [μ_apply]
  cases b <;> simp [Fintype.sum_prod_type, Set.indicator_apply, X, one_add_one',
    four_inv_mul_two]

theorem Y_fair (b : Bool) : μ (Y ⁻¹' {b}) = 2⁻¹ := by
  rw [μ_apply]
  cases b <;> simp [Fintype.sum_prod_type, Set.indicator_apply, Y, one_add_one',
    four_inv_mul_two]

theorem Z_fair (b : Bool) : μ (Z ⁻¹' {b}) = 2⁻¹ := by
  rw [μ_apply]
  cases b <;> simp [Fintype.sum_prod_type, Set.indicator_apply, Z, one_add_one',
    four_inv_mul_two]

theorem indep_X_Y : X ⟂ᵢ[μ] Y := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  simp only [μ_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  by_cases h1 : true ∈ s <;> by_cases h2 : false ∈ s <;> by_cases h3 : true ∈ t <;>
    by_cases h4 : false ∈ t <;>
    simp [h1, h2, h3, h4, one_add_one', two_add_two', four_inv_mul_two, four_inv_mul_four,
      two_inv_sq, Set.indicator_apply, X, Y]

theorem indep_X_Z : X ⟂ᵢ[μ] Z := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  simp only [μ_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  by_cases h1 : true ∈ s <;> by_cases h2 : false ∈ s <;> by_cases h3 : true ∈ t <;>
    by_cases h4 : false ∈ t <;>
    simp [h1, h2, h3, h4, one_add_one', two_add_two', four_inv_mul_two, four_inv_mul_four,
      two_inv_sq, Set.indicator_apply, X, Z]

theorem indep_Y_Z : Y ⟂ᵢ[μ] Z := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  simp only [μ_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  by_cases h1 : true ∈ s <;> by_cases h2 : false ∈ s <;> by_cases h3 : true ∈ t <;>
    by_cases h4 : false ∈ t <;>
    simp [h1, h2, h3, h4, one_add_one', two_add_two', four_inv_mul_two, four_inv_mul_four,
      two_inv_sq, Set.indicator_apply, Y, Z]

theorem not_indep_XY_Z : ¬ (fun ω => (X ω, Y ω)) ⟂ᵢ[μ] Z := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro h
  have h' := h {(false, false)} {true} (measurableSet_Ω _) (Set.to_countable _).measurableSet
  have hl : (fun ω => (X ω, Y ω)) ⁻¹' {(false, false)} ∩ Z ⁻¹' {true} = ∅ := by
    ext ⟨a, b⟩; simp [X, Y, Z]
  have hr : (fun ω : Ω => (X ω, Y ω)) ⁻¹' {(false, false)} = {(false, false)} := by
    ext ⟨a, b⟩; simp [X, Y]
  rw [hl, hr, μ_singleton, Z_fair, measure_empty] at h'
  exact absurd h'.symm (mul_ne_zero (by simp) (by simp))

theorem prob_Z_false : μ (Z ⁻¹' {false}) = 2⁻¹ := Z_fair false

theorem cond_Z_false (t : Set Ω) :
    μ[t | Z ⁻¹' {false}] = 2 * μ (Z ⁻¹' {false} ∩ t) := by
  rw [cond_apply (measurableSet_Ω _), prob_Z_false, inv_inv]

theorem cond_X_eq_Y : μ[{ω | X ω = Y ω} | Z ⁻¹' {false}] = 1 := by
  have hs : Z ⁻¹' {false} ∩ {ω | X ω = Y ω} = Z ⁻¹' {false} := by
    ext ⟨a, b⟩; cases a <;> cases b <;> simp [X, Y, Z]
  rw [cond_Z_false, hs, prob_Z_false, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

theorem cond_X_ne_Y : μ[{ω | X ω ≠ Y ω} | Z ⁻¹' {false}] = 0 := by
  have hs : Z ⁻¹' {false} ∩ {ω | X ω ≠ Y ω} = ∅ := by
    ext ⟨a, b⟩; cases a <;> cases b <;> simp [X, Y, Z]
  rw [cond_Z_false, hs, measure_empty, mul_zero]

theorem ae_cond_Y_eq_X : ∀ᵐ ω ∂(μ[|Z ⁻¹' {false}]), Y ω = X ω := by
  rw [ae_iff]
  have : {ω | ¬ Y ω = X ω} = {ω | X ω ≠ Y ω} := by
    ext ω; simp [eq_comm]
  rw [this, cond_X_ne_Y]

theorem cond_X_eq_Y_of_Z_true : μ[{ω | X ω = Y ω} | Z ⁻¹' {true}] = 0 := by
  have hs : Z ⁻¹' {true} ∩ {ω | X ω = Y ω} = ∅ := by
    ext ⟨a, b⟩; cases a <;> cases b <;> simp [X, Y, Z]
  rw [cond_apply (measurableSet_Ω _), hs, measure_empty, mul_zero]

theorem not_indep_X_Y_cond : ¬ X ⟂ᵢ[μ[|Z ⁻¹' {false}]] Y := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro h
  have h' := h {true} {false} (Set.to_countable _).measurableSet
    (Set.to_countable _).measurableSet
  have e0 : Z ⁻¹' {false} ∩ (X ⁻¹' {true} ∩ Y ⁻¹' {false}) = ∅ := by
    ext ⟨a, b⟩; cases a <;> cases b <;> simp [X, Y, Z]
  have e1 : Z ⁻¹' {false} ∩ X ⁻¹' {true} = {(true, true)} := by
    ext ⟨a, b⟩; cases a <;> cases b <;> simp [X, Z]
  have e2 : Z ⁻¹' {false} ∩ Y ⁻¹' {false} = {(false, false)} := by
    ext ⟨a, b⟩; cases a <;> cases b <;> simp [Y, Z]
  rw [cond_Z_false, cond_Z_false, cond_Z_false, e0, e1, e2, μ_singleton, μ_singleton,
    measure_empty, mul_zero] at h'
  exact absurd h'.symm (mul_ne_zero (mul_ne_zero (by simp) (by simp))
    (mul_ne_zero (by simp) (by simp)))

theorem collider :
    X ⟂ᵢ[μ] Y ∧ X ⟂ᵢ[μ] Z ∧ μ[{ω | X ω = Y ω} | Z ⁻¹' {false}] = 1 ∧
      ¬ X ⟂ᵢ[μ[|Z ⁻¹' {false}]] Y :=
  ⟨indep_X_Y, indep_X_Z, cond_X_eq_Y, not_indep_X_Y_cond⟩

end XorColliderB
