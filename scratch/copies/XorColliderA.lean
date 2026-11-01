import Mathlib

/-!
# XOR collider

Sample space `Bool × Bool` with the explicit uniform measure `μ` (mass `1/4` on each of the
four points, written as a sum of Dirac masses). `X ω = ω.1`, `Y ω = ω.2`, `Z ω = X ω xor Y ω`.

PROVED
* `isProbabilityMeasure_μ` : `μ` is a probability measure.
* `μ_singleton` : every outcome has probability `1/4`.
* `prob_X`, `prob_Y`, `prob_Z` : `X`, `Y` and `Z` are each fair bits (each value has probability `1/2`).
* `indep_X_Y` : `X` and `Y` are independent (`ProbabilityTheory.IndepFun`).
* `indep_X_Z` : `X` and `Z` are independent.
* `indep_Y_Z` : `Y` and `Z` are independent.
* `prob_X_eq_Y` : unconditionally, `P(X = Y) = 1/2`.
* `cond_X_eq_Y_given_Z_false` : `P(X = Y | Z = 0) = 1`; conditional on `Z = 0`, `X` determines `Y`.
* `cond_X_ne_Y_given_Z_true` : `P(X ≠ Y | Z = 1) = 1`.
* `cond_Y_given_X_Z_false` : `P(Y = b | X = a, Z = 0)` is `1` if `b = a` and `0` otherwise.
* `not_indep_X_Y_given_Z_false` : `X` and `Y` are NOT independent under `μ[|Z = 0]`
  (conditioning on the collider `Z` induces dependence between independent causes).
* `not_condIndep_X_Y_given_Z_false_explicit` : the explicit witness
  `P(X = 1, Y = 0 | Z = 0) = 0 ≠ 1/4 = P(X = 1 | Z = 0) · P(Y = 0 | Z = 0)`.
-/

namespace XorColliderA

open MeasureTheory ProbabilityTheory ENNReal
open scoped Classical

/-- Weight of a single outcome, `1/4 = 2⁻¹ * 2⁻¹`. -/
noncomputable def q : ℝ≥0∞ := 2⁻¹ * 2⁻¹

/-- The uniform measure on `Bool × Bool`. -/
noncomputable def μ : Measure (Bool × Bool) := ∑ ω : Bool × Bool, q • Measure.dirac ω

/-- First cause. -/
def X (ω : Bool × Bool) : Bool := ω.1
/-- Second cause. -/
def Y (ω : Bool × Bool) : Bool := ω.2
/-- Common effect. -/
def Z (ω : Bool × Bool) : Bool := xor (X ω) (Y ω)

lemma q_add_q : q + q = 2⁻¹ := by
  unfold q
  rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

lemma two_inv_mul_two_inv : (2⁻¹ : ℝ≥0∞) * 2⁻¹ = q := rfl

lemma μ_apply (s : Set (Bool × Bool)) :
    μ s = s.indicator (fun _ => q) (false, false) + s.indicator (fun _ => q) (false, true) +
      (s.indicator (fun _ => q) (true, false) + s.indicator (fun _ => q) (true, true)) := by
  unfold μ
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp only [Set.indicator, Pi.one_apply]
  split_ifs <;> simp <;> ring

lemma μ_singleton (ω : Bool × Bool) : μ {ω} = 4⁻¹ := by
  have h4 : (4 : ℝ≥0∞)⁻¹ = q := by
    unfold q
    rw [← ENNReal.mul_inv (by simp) (by simp)]
    norm_num
  rw [h4, μ_apply]
  rcases ω with ⟨a, b⟩
  cases a <;> cases b <;> simp [Set.indicator]

lemma q_four : q + q + (q + q) = 1 := by
  rw [q_add_q, ENNReal.inv_two_add_inv_two]

instance isProbabilityMeasure_μ : IsProbabilityMeasure μ :=
  ⟨by rw [μ_apply]; simp [q_four]⟩

lemma prob_X (a : Bool) : μ (X ⁻¹' {a}) = 2⁻¹ := by
  rw [μ_apply]; cases a <;> simp [Set.indicator, X, q_add_q]

lemma prob_Y (b : Bool) : μ (Y ⁻¹' {b}) = 2⁻¹ := by
  rw [μ_apply]; cases b <;> simp [Set.indicator, Y, q_add_q]

lemma prob_Z (c : Bool) : μ (Z ⁻¹' {c}) = 2⁻¹ := by
  rw [μ_apply]; cases c <;> simp [Set.indicator, Z, X, Y, q_add_q]

lemma prob_X_set (s : Set Bool) :
    μ (X ⁻¹' s) = (if false ∈ s then (2⁻¹ : ℝ≥0∞) else 0) + (if true ∈ s then 2⁻¹ else 0) := by
  rw [μ_apply]
  by_cases h1 : false ∈ s <;> by_cases h2 : true ∈ s <;>
    simp [X, h1, h2, q_add_q]

lemma prob_Y_set (s : Set Bool) :
    μ (Y ⁻¹' s) = (if false ∈ s then (2⁻¹ : ℝ≥0∞) else 0) + (if true ∈ s then 2⁻¹ else 0) := by
  rw [μ_apply]
  by_cases h1 : false ∈ s <;> by_cases h2 : true ∈ s <;>
    simp [Y, h1, h2, q_add_q]

lemma prob_Z_set (s : Set Bool) :
    μ (Z ⁻¹' s) = (if false ∈ s then (2⁻¹ : ℝ≥0∞) else 0) + (if true ∈ s then 2⁻¹ else 0) := by
  rw [μ_apply]
  by_cases h1 : false ∈ s <;> by_cases h2 : true ∈ s <;>
    simp [Z, X, Y, h1, h2, q_add_q]

/-- Reduce independence of two `Bool`-valued maps to a check over all pairs of subsets of `Bool`. -/
lemma indep_of_forall (f g : Bool × Bool → Bool)
    (h : ∀ s t : Set Bool, μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t)) :
    IndepFun f g μ :=
  (indepFun_iff_measure_inter_preimage_eq_mul).2 fun s t _ _ => h s t

theorem indep_X_Y : IndepFun X Y μ := by
  refine indep_of_forall X Y fun s t => ?_
  rw [prob_X_set, prob_Y_set, μ_apply]
  by_cases h1 : false ∈ s <;> by_cases h2 : true ∈ s <;> by_cases h3 : false ∈ t <;>
    by_cases h4 : true ∈ t <;>
    simp [X, Y, h1, h2, h3, h4] <;> unfold q <;> ring

theorem indep_X_Z : IndepFun X Z μ := by
  refine indep_of_forall X Z fun s t => ?_
  rw [prob_X_set, prob_Z_set, μ_apply]
  by_cases h1 : false ∈ s <;> by_cases h2 : true ∈ s <;> by_cases h3 : false ∈ t <;>
    by_cases h4 : true ∈ t <;>
    simp [X, Y, Z, h1, h2, h3, h4] <;> unfold q <;> ring

theorem indep_Y_Z : IndepFun Y Z μ := by
  refine indep_of_forall Y Z fun s t => ?_
  rw [prob_Y_set, prob_Z_set, μ_apply]
  by_cases h1 : false ∈ s <;> by_cases h2 : true ∈ s <;> by_cases h3 : false ∈ t <;>
    by_cases h4 : true ∈ t <;>
    simp [X, Y, Z, h1, h2, h3, h4] <;> unfold q <;> ring

theorem prob_X_eq_Y : μ {ω | X ω = Y ω} = 2⁻¹ := by
  rw [μ_apply]; simp [Set.indicator, X, Y, q_add_q]

lemma ms {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α] (s : Set α) :
    MeasurableSet s :=
  (Set.toFinite s).measurableSet

lemma two_mul_two_inv : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)

theorem cond_X_eq_Y_given_Z_false : μ[|Z ⁻¹' {false}] {ω | X ω = Y ω} = 1 := by
  rw [cond_apply (ms _), prob_Z, μ_apply]
  simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_ofPred_eq, X, Y, Z]
  simp [q_add_q, two_mul_two_inv]

theorem cond_X_ne_Y_given_Z_true : μ[|Z ⁻¹' {true}] {ω | X ω ≠ Y ω} = 1 := by
  rw [cond_apply (ms _), prob_Z, μ_apply]
  simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_ofPred_eq, X, Y, Z]
  simp [q_add_q, two_mul_two_inv]

theorem cond_Y_given_X_Z_false (a b : Bool) :
    μ[|X ⁻¹' {a} ∩ Z ⁻¹' {false}] (Y ⁻¹' {b}) = if b = a then 1 else 0 := by
  have hden : μ (X ⁻¹' {a} ∩ Z ⁻¹' {false}) = q := by
    rw [μ_apply]; cases a <;> simp [Set.indicator, X, Y, Z]
  have hq0 : q ≠ 0 := by unfold q; simp
  have hqt : q ≠ ⊤ := by unfold q; exact ENNReal.mul_ne_top (by simp) (by simp)
  rw [cond_apply (ms _), hden, μ_apply]
  cases a <;> cases b <;> simp [Set.indicator, X, Y, Z, ENNReal.inv_mul_cancel hq0 hqt]

lemma cond_Z_false_apply (s : Set (Bool × Bool)) :
    μ[|Z ⁻¹' {false}] s = 2 * (s.indicator (fun _ => q) (false, false) +
      s.indicator (fun _ => q) (true, true)) := by
  rw [cond_apply (ms _), prob_Z, inv_inv, μ_apply]
  congr 1
  simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, X, Y, Z]
  split_ifs <;> simp_all

theorem not_condIndep_X_Y_given_Z_false_explicit :
    μ[|Z ⁻¹' {false}] (X ⁻¹' {true} ∩ Y ⁻¹' {false}) = 0 ∧
    μ[|Z ⁻¹' {false}] (X ⁻¹' {true}) = 2⁻¹ ∧
    μ[|Z ⁻¹' {false}] (Y ⁻¹' {false}) = 2⁻¹ ∧
    μ[|Z ⁻¹' {false}] (X ⁻¹' {true}) * μ[|Z ⁻¹' {false}] (Y ⁻¹' {false}) = 4⁻¹ := by
  have h2q : 2 * q = 2⁻¹ := by
    unfold q; rw [← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
  have hX : μ[|Z ⁻¹' {false}] (X ⁻¹' {true}) = 2⁻¹ := by
    rw [cond_Z_false_apply]; simp [Set.indicator, X, h2q]
  have hY : μ[|Z ⁻¹' {false}] (Y ⁻¹' {false}) = 2⁻¹ := by
    rw [cond_Z_false_apply]; simp [Set.indicator, Y, h2q]
  refine ⟨?_, hX, hY, ?_⟩
  · rw [cond_Z_false_apply]; simp [Set.indicator, X, Y]
  · rw [hX, hY, ← ENNReal.mul_inv (by simp) (by simp)]; norm_num

theorem not_indep_X_Y_given_Z_false : ¬ IndepFun X Y (μ[|Z ⁻¹' {false}]) := by
  intro h
  obtain ⟨h0, -, -, hprod⟩ := not_condIndep_X_Y_given_Z_false_explicit
  have := (indepFun_iff_measure_inter_preimage_eq_mul.1 h) {true} {false} (ms _) (ms _)
  rw [h0, hprod] at this
  exact absurd this.symm (by simp)

end XorColliderA
