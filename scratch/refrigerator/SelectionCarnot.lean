import Mathlib

/-!
# The fuel bound for selection, and the selection that attains it

A population with frequencies `q` passes through a survival filter: type `i` survives with probability `s i ∈ [0, 1]`.
The fraction that survives is `S = Σ q s`, and the survivors have frequencies `q' = q s / S`. The selection "spent"
`log (1/S)` nats: the log of the number of individuals that had to exist per survivor. It moved the population by the
Kullback–Leibler divergence `D(q' ‖ q)`.

PROVED:
* `selection_fuel_bound`: `D(q' ‖ q) ≤ log (1/S)`. No survival filter moves a population further, in KL divergence, than
  the log of its own death toll.
* `truncation_attains`: if every type either surely survives or surely dies (`s i ∈ {0, 1}`), the bound is an equality.
* `soft_selection_wastes`: if some type with positive frequency survives with probability strictly between 0 and 1, the
  inequality is strict: probabilistic survival pays for deaths that move the population nowhere.
INTERPRETED (not formalized): selection as a refrigerator for programs it does not own, deaths as its fuel, and
truncation as the Carnot cycle that wastes none of it.
-/

namespace SelectionCarnot
open Finset Real

variable {ι : Type*} [Fintype ι]

noncomputable def S (q s : ι → ℝ) : ℝ := ∑ i, q i * s i
noncomputable def post (q s : ι → ℝ) (i : ι) : ℝ := q i * s i / S q s
noncomputable def KL (q s : ι → ℝ) : ℝ := ∑ i, post q s i * log (post q s i / q i)

lemma term_eq (q s : ι → ℝ) (hq : ∀ i, 0 < q i) (hS : 0 < S q s) (i : ι) :
    post q s i * log (post q s i / q i) = post q s i * (log (s i) - log (S q s)) := by
  unfold post
  by_cases h : s i = 0
  · simp [h]
  · have hqi := (hq i).ne'
    rw [show q i * s i / S q s / q i = s i / S q s by field_simp, log_div h hS.ne']

lemma KL_eq (q s : ι → ℝ) (hq : ∀ i, 0 < q i) (hS : 0 < S q s) :
    KL q s = ∑ i, post q s i * log (s i) - log (S q s) := by
  unfold KL
  simp only [term_eq q s hq hS, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have : ∑ i, post q s i = 1 := by
    unfold post; rw [← Finset.sum_div]; exact div_self hS.ne'
  rw [this, one_mul]

theorem selection_fuel_bound (q s : ι → ℝ) (hq : ∀ i, 0 < q i) (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1)
    (hS : 0 < S q s) : KL q s ≤ log (1 / S q s) := by
  rw [KL_eq q s hq hS, one_div, log_inv]
  have : ∑ i, post q s i * log (s i) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (mul_nonneg (hq i).le (hs0 i)) hS.le) (log_nonpos (hs0 i) (hs1 i)))
  linarith

theorem truncation_attains (q s : ι → ℝ) (hq : ∀ i, 0 < q i) (hs : ∀ i, s i = 0 ∨ s i = 1) (hS : 0 < S q s) :
    KL q s = log (1 / S q s) := by
  rw [KL_eq q s hq hS, one_div, log_inv]
  have : ∑ i, post q s i * log (s i) = 0 :=
    Finset.sum_eq_zero (fun i _ => by rcases hs i with h | h <;> simp [h])
  rw [this]; ring

theorem soft_selection_wastes (q s : ι → ℝ) (hq : ∀ i, 0 < q i) (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1)
    (hS : 0 < S q s) (j : ι) (hj0 : 0 < s j) (hj1 : s j < 1) : KL q s < log (1 / S q s) := by
  rw [KL_eq q s hq hS, one_div, log_inv]
  have hneg : post q s j * log (s j) < 0 :=
    mul_neg_of_pos_of_neg (div_pos (mul_pos (hq j) hj0) hS) (log_neg hj0 hj1)
  have hle : ∀ i ∈ univ, post q s i * log (s i) ≤ 0 := fun i _ => mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (mul_nonneg (hq i).le (hs0 i)) hS.le) (log_nonpos (hs0 i) (hs1 i))
  have : ∑ i, post q s i * log (s i) < 0 :=
    Finset.sum_neg' (fun i hi => hle i hi) ⟨j, mem_univ j, hneg⟩ |>.trans_le' le_rfl
  linarith

end SelectionCarnot
