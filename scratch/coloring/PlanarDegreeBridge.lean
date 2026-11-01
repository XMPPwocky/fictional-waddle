import Mathlib

/-!
# Edge bound to minimum degree

PROVED:
* `PlanarDegreeBridge.exists_degree_le_of_two_mul_card_lt`: in a finite simple graph on a
  nonempty vertex type, if `2E < (d + 1) V` then some vertex has degree at most `d`.
* `PlanarDegreeBridge.exists_degree_le_five`: a finite simple graph with `V ≥ 3` vertices and
  `E ≤ 3V - 6` edges has a vertex of degree at most 5.
* `PlanarDegreeBridge.minDegree_le_five`: under the same hypotheses, the minimum degree is at
  most 5.
* `PlanarDegreeBridge.induce_exists_degree_le_five`: if every induced subgraph on at least 3
  vertices satisfies `E ≤ 3V - 6`, then every nonempty vertex subset contains a vertex with at
  most 5 neighbours inside that subset (the 5-degeneracy condition). Subsets with 1 or 2
  vertices are handled directly.
-/

namespace PlanarDegreeBridge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem exists_degree_le_of_two_mul_card_lt [Nonempty V] (d : ℕ)
    (h : 2 * G.edgeFinset.card < (d + 1) * Fintype.card V) :
    ∃ v, G.degree v ≤ d := by
  by_contra hne
  push Not at hne
  have hsum : ∑ v, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hge : ∑ _v : V, (d + 1) ≤ ∑ v, G.degree v :=
    Finset.sum_le_sum fun v _ => hne v
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hge
  rw [Nat.mul_comm] at hge
  omega

omit [DecidableEq V] in
theorem exists_degree_le_five (hV : 3 ≤ Fintype.card V)
    (hE : G.edgeFinset.card ≤ 3 * Fintype.card V - 6) :
    ∃ v, G.degree v ≤ 5 := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact exists_degree_le_of_two_mul_card_lt G 5 (by omega)

omit [DecidableEq V] in
theorem minDegree_le_five (hV : 3 ≤ Fintype.card V)
    (hE : G.edgeFinset.card ≤ 3 * Fintype.card V - 6) :
    G.minDegree ≤ 5 := by
  obtain ⟨v, hv⟩ := exists_degree_le_five G hV hE
  exact (G.minDegree_le_degree v).trans hv

theorem induce_exists_degree_le_five
    (hplanar : ∀ s : Finset V, 3 ≤ s.card →
      (G.induce (s : Set V)).edgeFinset.card ≤ 3 * s.card - 6)
    (s : Finset V) (hs : s.Nonempty) :
    ∃ v ∈ s, (G.neighborFinset v ∩ s).card ≤ 5 := by
  by_cases h3 : 3 ≤ s.card
  · obtain ⟨⟨v, hv⟩, hdeg⟩ := exists_degree_le_five (G.induce (s : Set V))
      (by simpa using h3) (by simpa using hplanar s h3)
    refine ⟨v, hv, ?_⟩
    have hle : (G.neighborFinset v ∩ s).card ≤ (G.induce (s : Set V)).degree ⟨v, hv⟩ := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      refine Finset.card_le_card_of_injOn (fun w => if hw : w ∈ s then ⟨w, hw⟩ else ⟨v, hv⟩)
        ?_ ?_
      · intro w hw
        simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe,
          SimpleGraph.mem_neighborFinset] at hw
        simp [hw.2, hw.1]
      · intro a ha b hb hab
        simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at ha hb
        simpa [ha.2, hb.2] using hab
    exact hle.trans hdeg
  · obtain ⟨v, hv⟩ := hs
    refine ⟨v, hv, ?_⟩
    have hsub : G.neighborFinset v ∩ s ⊆ s.erase v := by
      intro w hw
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hw.1).symm, hw.2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hv] at this
    omega

end PlanarDegreeBridge
