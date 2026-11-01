import Mathlib

/-!
# Evaporative cooling of a group

Members carry weights `p i ≥ 0` and squared distances `v i ≥ 0` from the group's centre. The members who stay are
those within the tolerance, `v i ≤ W`; the rest leave.

PROVED:
* `evaporation_cools`: the weighted mean squared distance of those who stay is at most that of the whole group.
  Removing the members furthest out can only lower the spread around the old centre (and the spread around the new
  centre is lower still). That is the "cooling".
* `stayers_mean_le_tolerance`: the stayers' mean squared distance is at most `W`, whatever the group looked like.
INTERPRETED (not formalized): the shift of every trait's mean when members leave is the Price covariance with staying
(`SelectionUniversal.postselection_is_selection` in the atlas); departure cascades, where one exit moves the centre
and pushes the next member out, are the interaction term of `HessianCredit.interaction_credit`.
-/

namespace EvaporativeCooling
open Finset

variable {ι : Type*} [Fintype ι]

theorem evaporation_cools (p v : ι → ℝ) (W : ℝ) (hp : ∀ i, 0 ≤ p i)
    (hin : 0 < ∑ i ∈ univ.filter (fun i => v i ≤ W), p i) :
    (∑ i ∈ univ.filter (fun i => v i ≤ W), p i * v i) / (∑ i ∈ univ.filter (fun i => v i ≤ W), p i)
      ≤ (∑ i, p i * v i) / (∑ i, p i) := by
  set a := ∑ i ∈ univ.filter (fun i => v i ≤ W), p i
  set A := ∑ i ∈ univ.filter (fun i => v i ≤ W), p i * v i
  set b := ∑ i ∈ univ.filter (fun i => ¬ v i ≤ W), p i
  set B := ∑ i ∈ univ.filter (fun i => ¬ v i ≤ W), p i * v i
  have hsumP : ∑ i, p i = a + b := (sum_filter_add_sum_filter_not univ (fun i => v i ≤ W) p).symm
  have hsumV : ∑ i, p i * v i = A + B :=
    (sum_filter_add_sum_filter_not univ (fun i => v i ≤ W) (fun i => p i * v i)).symm
  have hb : 0 ≤ b := sum_nonneg (fun i _ => hp i)
  have hA : A ≤ W * a := by
    rw [mul_sum]; exact sum_le_sum (fun i hi => by
      have := (mem_filter.mp hi).2; nlinarith [hp i])
  have hB : W * b ≤ B := by
    rw [mul_sum]; exact sum_le_sum (fun i hi => by
      have := (mem_filter.mp hi).2; push Not at this; nlinarith [hp i])
  rw [hsumP, hsumV, div_le_div_iff₀ hin (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right hA hb, mul_le_mul_of_nonneg_right hB hin.le]

theorem stayers_mean_le_tolerance (p v : ι → ℝ) (W : ℝ) (hp : ∀ i, 0 ≤ p i)
    (hin : 0 < ∑ i ∈ univ.filter (fun i => v i ≤ W), p i) :
    (∑ i ∈ univ.filter (fun i => v i ≤ W), p i * v i) / (∑ i ∈ univ.filter (fun i => v i ≤ W), p i) ≤ W := by
  rw [div_le_iff₀ hin, mul_sum]
  exact sum_le_sum (fun i hi => by have := (mem_filter.mp hi).2; nlinarith [hp i])

end EvaporativeCooling
