import Mathlib

/-!
# Randomised execution makes decision-market prices causal

Finite model: binary confounder `U ∈ Fin 2`, binary policy `A ∈ Fin 2`, outcome `Y = y ω`
with `ω` ranging over a finite outcome space `Ω`. The joint law is
`P(u,a,ω) = P(u) * P(a|u) * P(ω|u,a)`. The evidential price `E[Y | A = a]` is defined from
the joint law as a ratio of sums; the causal value is `V(a) = ∑_u P(u) * m(u,a)` with
`m(u,a) = E[Y | U = u, A = a]`.

PROVED
* `probA_eq`, `probA_pos`: `P(A=a) = ∑_u P(u) P(a|u)` and it is positive.
* `postU_eq`, `postU_sum`: the posterior `P(U=u|A=a)` equals `P(u)P(a|u)/P(A=a)` and the
  posteriors sum to one.
* `evPrice_eq`: `E[Y|A=a] = ∑_u P(U=u|A=a) * m(u,a)` (the evidential price computed from the
  joint law equals the posterior-weighted conditional means).
* `bias_formula` (claim 2): `E[Y|A=a] - V(a) = (P(U=1|A=a) - P(U=1)) * (m(1,a) - m(0,a))`.
* `evPrice_eq_causal_iff` (claim 2): `E[Y|A=a] = V(a)` iff `P(U=1|A=a) = P(U=1)` or
  `m(1,a) = m(0,a)`.
* `postU_eq_prior_iff`: under positivity, `P(U=1|A=a) = P(U=1)` iff `P(a|U=1) = P(a|U=0)`.
* `evPrice_eq_causal_iff_independent`: `E[Y|A=a] = V(a)` iff `P(a|U=1) = P(a|U=0)` or
  `m(1,a) = m(0,a)`.
* `evPrice_eq_causal_of_independent`: if the policy law does not depend on `U`
  (`P(a|u) = c(a)` for all `u`), then `E[Y|A=a] = V(a)` for every `a`.
* `fair_coin` (claim 1): if `P(a|u) = 1/2` for all `a, u`, then `E[Y|A=a] = V(a)` for both `a`.
* `reversal` (claim 3): the explicit model `P(U=1)=1/2`, `P(A=1|U=1)=9/10`,
  `P(A=1|U=0)=1/10`, `Y = U - A/4` deterministically, satisfies all positivity conditions
  (it is a `Model`), and has `E[Y|A=1] = 13/20`, `E[Y|A=0] = 1/10`, `V(1) = 1/4`,
  `V(0) = 1/2`; hence `E[Y|A=1] > E[Y|A=0]` while `V(1) < V(0)`.

INTERPRETED (not formalized)
* That a decision market's price for policy `a` equals the evidential price `E[Y|A=a]`
  under the market's information, and that "the market picks" the policy with the larger price.
-/

namespace DecisionMarketRandomisedExecution

open Finset

/-- A finite confounded decision model. `pA u a = P(A = a | U = u)`,
`pY u a ω = P(Y = y ω | U = u, A = a)`. -/
structure Model (Ω : Type*) [Fintype Ω] where
  pU : Fin 2 → ℝ
  pA : Fin 2 → Fin 2 → ℝ
  pY : Fin 2 → Fin 2 → Ω → ℝ
  y : Ω → ℝ
  pU_pos : ∀ u, 0 < pU u
  pU_sum : pU 0 + pU 1 = 1
  pA_pos : ∀ u a, 0 < pA u a
  pA_lt_one : ∀ u a, pA u a < 1
  pA_sum : ∀ u, pA u 0 + pA u 1 = 1
  pY_nonneg : ∀ u a ω, 0 ≤ pY u a ω
  pY_sum : ∀ u a, ∑ ω, pY u a ω = 1

variable {Ω : Type*} [Fintype Ω] (M : Model Ω)

namespace Model

/-- Joint law `P(U = u, A = a, outcome = ω)`. -/
def joint (u a : Fin 2) (ω : Ω) : ℝ := M.pU u * M.pA u a * M.pY u a ω

/-- Conditional mean `m(u,a) = E[Y | U = u, A = a]`. -/
def m (u a : Fin 2) : ℝ := ∑ ω, M.pY u a ω * M.y ω

/-- Marginal `P(A = a)` from the joint law. -/
def probA (a : Fin 2) : ℝ := ∑ u, ∑ ω, M.joint u a ω

/-- Posterior `P(U = u | A = a)` from the joint law. -/
noncomputable def postU (u a : Fin 2) : ℝ := (∑ ω, M.joint u a ω) / M.probA a

/-- Evidential price `E[Y | A = a]` from the joint law. -/
noncomputable def evPrice (a : Fin 2) : ℝ := (∑ u, ∑ ω, M.joint u a ω * M.y ω) / M.probA a

/-- Causal value `V(a) = ∑_u P(u) m(u,a)`. -/
def causalValue (a : Fin 2) : ℝ := ∑ u, M.pU u * M.m u a

lemma sum_joint (u a : Fin 2) : ∑ ω, M.joint u a ω = M.pU u * M.pA u a := by
  simp only [joint, ← mul_sum, M.pY_sum, mul_one]

lemma sum_joint_y (u a : Fin 2) :
    ∑ ω, M.joint u a ω * M.y ω = M.pU u * M.pA u a * M.m u a := by
  simp only [joint, m, mul_sum, mul_assoc]

theorem probA_eq (a : Fin 2) : M.probA a = ∑ u, M.pU u * M.pA u a := by
  simp only [probA, sum_joint]

theorem probA_pos (a : Fin 2) : 0 < M.probA a := by
  rw [probA_eq, Fin.sum_univ_two]
  have h0 := mul_pos (M.pU_pos 0) (M.pA_pos 0 a)
  have h1 := mul_pos (M.pU_pos 1) (M.pA_pos 1 a)
  linarith

theorem postU_eq (u a : Fin 2) : M.postU u a = M.pU u * M.pA u a / M.probA a := by
  simp only [postU, sum_joint]

theorem postU_sum (a : Fin 2) : M.postU 0 a + M.postU 1 a = 1 := by
  have hp := (M.probA_pos a).ne'
  rw [postU_eq, postU_eq, ← add_div, div_eq_one_iff_eq hp, probA_eq, Fin.sum_univ_two]

theorem evPrice_eq (a : Fin 2) : M.evPrice a = ∑ u, M.postU u a * M.m u a := by
  have hp := (M.probA_pos a).ne'
  simp only [evPrice, sum_joint_y, postU_eq, Fin.sum_univ_two]
  field_simp

/-- Claim (2): the evidential bias formula. -/
theorem bias_formula (a : Fin 2) :
    M.evPrice a - M.causalValue a = (M.postU 1 a - M.pU 1) * (M.m 1 a - M.m 0 a) := by
  rw [evPrice_eq, causalValue, Fin.sum_univ_two, Fin.sum_univ_two]
  have h1 := M.postU_sum a
  have h2 := M.pU_sum
  have e1 : M.postU 0 a = 1 - M.postU 1 a := by linarith
  have e2 : M.pU 0 = 1 - M.pU 1 := by linarith
  rw [e1, e2]
  ring

/-- Claim (2): characterisation of when the evidential price is causal. -/
theorem evPrice_eq_causal_iff (a : Fin 2) :
    M.evPrice a = M.causalValue a ↔ M.postU 1 a = M.pU 1 ∨ M.m 1 a = M.m 0 a := by
  rw [← sub_eq_zero, bias_formula, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- Under positivity, the posterior equals the prior iff the policy law of `a` does not
depend on `U`. -/
theorem postU_eq_prior_iff (a : Fin 2) :
    M.postU 1 a = M.pU 1 ↔ M.pA 1 a = M.pA 0 a := by
  have hp := M.probA_pos a
  have h0 := M.pU_pos 0
  have h1 := M.pU_pos 1
  have hs := M.pU_sum
  rw [postU_eq, div_eq_iff hp.ne', probA_eq, Fin.sum_univ_two]
  constructor
  · intro h
    have h' : M.pU 1 * (M.pU 0 * (M.pA 1 a - M.pA 0 a)) = 0 := by
      have e : M.pU 0 = 1 - M.pU 1 := by linarith
      rw [e] at h ⊢
      linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' h1.ne'
    · rcases mul_eq_zero.mp h'' with h3 | h3
      · exact absurd h3 h0.ne'
      · linarith
  · intro h
    rw [h]
    have e : M.pU 0 = 1 - M.pU 1 := by linarith
    rw [e]
    ring

theorem evPrice_eq_causal_iff_independent (a : Fin 2) :
    M.evPrice a = M.causalValue a ↔ M.pA 1 a = M.pA 0 a ∨ M.m 1 a = M.m 0 a := by
  rw [evPrice_eq_causal_iff, postU_eq_prior_iff]

/-- Any execution randomisation independent of `U` gives causal prices. -/
theorem evPrice_eq_causal_of_independent (c : Fin 2 → ℝ) (hc : ∀ u a, M.pA u a = c a)
    (a : Fin 2) : M.evPrice a = M.causalValue a := by
  rw [evPrice_eq_causal_iff_independent]
  left
  rw [hc, hc]

/-- Claim (1): a fair coin independent of `U` makes evidential prices causal. -/
theorem fair_coin (h : ∀ u a, M.pA u a = 1 / 2) (a : Fin 2) :
    M.evPrice a = M.causalValue a :=
  M.evPrice_eq_causal_of_independent (fun _ => 1 / 2) h a

end Model

/-- The reversal instance: outcome space `Fin 2 × Fin 2` recording `(U, A)`, with
`Y = U - A/4` deterministically. -/
noncomputable def reversalModel : Model (Fin 2 × Fin 2) where
  pU := fun _ => 1 / 2
  pA := fun u a => if u = 1 then (if a = 1 then 9 / 10 else 1 / 10)
    else (if a = 1 then 1 / 10 else 9 / 10)
  pY := fun u a ω => if ω = (u, a) then 1 else 0
  y := fun ω => (ω.1 : ℝ) - (ω.2 : ℝ) / 4
  pU_pos := fun _ => by norm_num
  pU_sum := by norm_num
  pA_pos := fun u a => by fin_cases u <;> fin_cases a <;> norm_num
  pA_lt_one := fun u a => by fin_cases u <;> fin_cases a <;> norm_num
  pA_sum := fun u => by fin_cases u <;> norm_num
  pY_nonneg := fun u a ω => by split_ifs <;> norm_num
  pY_sum := fun u a => by simp

lemma reversal_m (u a : Fin 2) :
    reversalModel.m u a = (u : ℝ) - (a : ℝ) / 4 := by
  simp [Model.m, reversalModel]

lemma reversal_pA_1_1 : reversalModel.pA 1 1 = 9 / 10 := by simp [reversalModel]
lemma reversal_pA_0_1 : reversalModel.pA 0 1 = 1 / 10 := by simp [reversalModel]
lemma reversal_pA_1_0 : reversalModel.pA 1 0 = 1 / 10 := by simp [reversalModel]
lemma reversal_pA_0_0 : reversalModel.pA 0 0 = 9 / 10 := by simp [reversalModel]

theorem reversal_evPrice_one : reversalModel.evPrice 1 = 13 / 20 := by
  rw [Model.evPrice_eq, Fin.sum_univ_two, Model.postU_eq, Model.postU_eq, Model.probA_eq,
    Fin.sum_univ_two, reversal_m, reversal_m, reversal_pA_0_1, reversal_pA_1_1]
  norm_num [reversalModel]

theorem reversal_evPrice_zero : reversalModel.evPrice 0 = 1 / 10 := by
  rw [Model.evPrice_eq, Fin.sum_univ_two, Model.postU_eq, Model.postU_eq, Model.probA_eq,
    Fin.sum_univ_two, reversal_m, reversal_m, reversal_pA_0_0, reversal_pA_1_0]
  norm_num [reversalModel]

theorem reversal_causal_one : reversalModel.causalValue 1 = 1 / 4 := by
  rw [Model.causalValue, Fin.sum_univ_two, reversal_m, reversal_m]
  norm_num [reversalModel]

theorem reversal_causal_zero : reversalModel.causalValue 0 = 1 / 2 := by
  rw [Model.causalValue, Fin.sum_univ_two, reversal_m, reversal_m]
  norm_num [reversalModel]

/-- Claim (3): in the reversal instance the evidential ranking of policies is the opposite
of the causal ranking. -/
theorem reversal :
    reversalModel.evPrice 1 = 13 / 20 ∧ reversalModel.evPrice 0 = 1 / 10 ∧
    reversalModel.causalValue 1 = 1 / 4 ∧ reversalModel.causalValue 0 = 1 / 2 ∧
    reversalModel.evPrice 0 < reversalModel.evPrice 1 ∧
    reversalModel.causalValue 1 < reversalModel.causalValue 0 := by
  refine ⟨reversal_evPrice_one, reversal_evPrice_zero, reversal_causal_one,
    reversal_causal_zero, ?_, ?_⟩
  · rw [reversal_evPrice_one, reversal_evPrice_zero]; norm_num
  · rw [reversal_causal_one, reversal_causal_zero]; norm_num

end DecisionMarketRandomisedExecution
