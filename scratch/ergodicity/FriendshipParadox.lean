/-
# Your friends have more friends than you do, on average

PROVED
1. `size_biased_ge_mean`: for nonnegative numbers f over a finite nonempty population with positive
   total, the size-biased mean ∑ f² / ∑ f (pick a unit of f at random, report its owner's f) is at least
   the plain mean ∑ f / n.
2. `size_biased_gap`: the gap equals ∑ (f − mean)² / ∑ f, i.e. variance divided by mean (times n / n):
   the Price/Robertson selection differential with f as both trait and weight.
3. `size_biased_eq_iff`: the two means are equal exactly when f is constant.
4. `friend_degree_sum`: in any finite simple graph, summing the friend counts of everyone's friends
   gives ∑ (degree)².
5. `friendship_paradox`: so in any finite graph with at least one edge, the average friend count of a
   friend (averaged over all (person, friend) pairs) is at least the average friend count of a person,
   with equality exactly when every person has the same number of friends (`friendship_paradox_eq_iff`).
6. `star_example`: in a star with one centre and 4 leaves, a person has 8/5 friends on average and a
   friend has 5/2.

CITED
- Feld, "Why your friends have more friends than you do" (1991).
-/

import Mathlib

namespace FriendshipParadox

open Finset

section SizeBiased

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem size_biased_ge_mean (f : ι → ℝ) (hpos : 0 < ∑ i, f i) :
    (∑ i, f i) / Fintype.card ι ≤ (∑ i, f i ^ 2) / ∑ i, f i := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ hn hpos]
  have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := f)
  rw [card_univ] at this
  nlinarith [this]

theorem size_biased_gap (f : ι → ℝ) (hpos : 0 < ∑ i, f i) :
    (∑ i, f i ^ 2) / ∑ i, f i - (∑ i, f i) / Fintype.card ι =
      (∑ i, (f i - (∑ j, f j) / Fintype.card ι) ^ 2) / ∑ i, f i := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  set m := (∑ j, f j) / Fintype.card ι
  have hm : (Fintype.card ι : ℝ) * m = ∑ j, f j := by simp only [m]; field_simp
  have hexp : ∑ i, (f i - m) ^ 2 = ∑ i, f i ^ 2 - 2 * m * ∑ i, f i + Fintype.card ι * m ^ 2 := by
    have : ∀ i, (f i - m) ^ 2 = f i ^ 2 - 2 * m * f i + m ^ 2 := fun i => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, card_univ, nsmul_eq_mul]
  rw [hexp]
  have hsum : (∑ i, f i) ≠ 0 := hpos.ne'
  field_simp
  rw [← hm]
  ring

theorem size_biased_eq_iff (f : ι → ℝ) (hpos : 0 < ∑ i, f i) :
    (∑ i, f i ^ 2) / ∑ i, f i = (∑ i, f i) / Fintype.card ι ↔
      ∀ i, f i = (∑ j, f j) / Fintype.card ι := by
  rw [← sub_eq_zero, size_biased_gap f hpos, div_eq_zero_iff, or_iff_left hpos.ne',
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  simp [sub_eq_zero]

end SizeBiased

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem friend_degree_sum :
    ∑ v, ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) = ∑ u, (G.degree u : ℝ) ^ 2 := by
  have h1 : ∀ v, ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) =
      ∑ u, if G.Adj v u then (G.degree u : ℝ) else 0 := by
    intro v
    rw [G.neighborFinset_eq_filter, Finset.sum_filter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, sq]
  congr 1
  have : (univ.filter fun v => G.Adj v u) = G.neighborFinset u := by
    rw [G.neighborFinset_eq_filter]
    ext v
    simp [G.adj_comm]
  rw [this, G.card_neighborFinset_eq_degree]

theorem friendship_paradox [Nonempty V] (hpos : 0 < ∑ v, (G.degree v : ℝ)) :
    (∑ v, (G.degree v : ℝ)) / Fintype.card V ≤
      (∑ v, ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ)) / ∑ v, (G.degree v : ℝ) := by
  rw [friend_degree_sum]
  exact size_biased_ge_mean _ hpos

theorem friendship_paradox_eq_iff [Nonempty V] (hpos : 0 < ∑ v, (G.degree v : ℝ)) :
    (∑ v, ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ)) / ∑ v, (G.degree v : ℝ) =
        (∑ v, (G.degree v : ℝ)) / Fintype.card V ↔
      ∀ v, (G.degree v : ℝ) = (∑ w, (G.degree w : ℝ)) / Fintype.card V := by
  rw [friend_degree_sum]
  exact size_biased_eq_iff _ hpos

end Graph

/-- One centre (vertex 0) joined to four leaves. -/
def star : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun a _ => a = 0

instance : DecidableRel star.Adj := fun a b =>
  decidable_of_iff (a ≠ b ∧ (a = 0 ∨ b = 0)) (by simp [star, SimpleGraph.fromRel_adj])

theorem star_example :
    (∑ v, (star.degree v : ℝ)) / 5 = 8 / 5 ∧ (∑ v, (star.degree v : ℝ) ^ 2) / ∑ v, (star.degree v : ℝ) = 5 / 2 := by
  have hdeg : ∀ v, star.degree v = if v = 0 then 4 else 1 := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    fin_cases v <;> simp [star, SimpleGraph.fromRel_adj] <;> decide
  simp only [hdeg, Fin.sum_univ_five]
  norm_num

end FriendshipParadox

#print axioms FriendshipParadox.size_biased_ge_mean
#print axioms FriendshipParadox.size_biased_gap
#print axioms FriendshipParadox.size_biased_eq_iff
#print axioms FriendshipParadox.friend_degree_sum
#print axioms FriendshipParadox.friendship_paradox
#print axioms FriendshipParadox.friendship_paradox_eq_iff
#print axioms FriendshipParadox.star_example
