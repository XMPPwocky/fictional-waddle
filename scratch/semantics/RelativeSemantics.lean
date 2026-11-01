/-
# Special, general and relative semantics

PROVED
Special semantics ("the map is not the territory, as long as nobody's accelerating"):
1. `map_is_not_territory`: a map with fewer symbols than the territory has places sends two different
   places to the same symbol.
2. `constant_velocity_error`: a map that extrapolates at constant velocity is wrong by exactly the
   acceleration (the second difference).
3. `no_acceleration_iff_affine`: that error is zero at every step exactly when the territory moves
   along a straight line, x k = x 0 + k·(x 1 − x 0).

General semantics ("the territory curves around the maps people carry"):
4. `general_semantics`: if the territory's response T to a map is a contraction, there is exactly one
   map m with T m = m (a map consistent with the territory it produces), and refitting from any
   starting map converges to it.
5. `linear_curving`: for the response T m = a + ε m with ε ≠ 1, that map is a / (1 − ε), not the
   unresponsive value a.

Relative semantics (sameness is relative to the probes you have):
6. `relEq_mono`: things the same relative to more probes are the same relative to fewer.
7. `relEq_univ_iff`: sameness relative to every probe is equality of the whole response.
8. `relEq_empty`: relative to no probes, everything is the same as everything.
9. `two_things_need_a_probe`: if two things differ relative to P, then P is not empty.
10. `same_resonance`, `sweep_separates`: oscillators (m, k) = (1, 1) and (2, 2) have the same
    resonance k/m = 1, but their responses 1/(k − m ω²) differ at ω = 0. One resonance merges them;
    a frequency sweep separates them.

INTERPRETED (not formalized)
- Moore's proof ("here is one hand, and here is another") needs a probe that tells two hands apart;
  with no probe (item 8), one hand and everything are one, which is the sound of one hand clapping.
-/

import Mathlib

namespace RelativeSemantics

/-! ## Special semantics -/

theorem map_is_not_territory {Place Symbol : Type*} [Fintype Place] [Fintype Symbol]
    (mapOf : Place → Symbol) (h : Fintype.card Symbol < Fintype.card Place) :
    ∃ a b, a ≠ b ∧ mapOf a = mapOf b :=
  Fintype.exists_ne_map_eq_of_card_lt mapOf h

/-- Constant-velocity prediction of the next position. -/
def predict (x : ℕ → ℝ) (k : ℕ) : ℝ := x (k + 1) + (x (k + 1) - x k)

theorem constant_velocity_error (x : ℕ → ℝ) (k : ℕ) :
    x (k + 2) - predict x k = x (k + 2) - 2 * x (k + 1) + x k := by
  unfold predict; ring

theorem no_acceleration_iff_affine (x : ℕ → ℝ) :
    (∀ k, x (k + 2) - predict x k = 0) ↔ ∀ k, x k = x 0 + k * (x 1 - x 0) := by
  constructor
  · intro h
    have h2 : ∀ k, x k = x 0 + k * (x 1 - x 0) ∧ x (k + 1) = x 0 + (k + 1 : ℕ) * (x 1 - x 0) := by
      intro k
      induction k with
      | zero => constructor <;> push_cast <;> ring
      | succ n ih =>
        refine ⟨ih.2, ?_⟩
        have := h n
        rw [constant_velocity_error] at this
        have e1 := ih.1
        have e2 := ih.2
        push_cast at e1 e2 ⊢
        linarith
    exact fun k => (h2 k).1
  · intro h k
    rw [constant_velocity_error, h (k + 2), h (k + 1), h k]
    push_cast
    ring

/-! ## General semantics -/

theorem general_semantics (T : ℝ → ℝ) (K : NNReal) (hT : ContractingWith K T) :
    (∃! m, T m = m) ∧
      ∀ m₀, Filter.Tendsto (fun n => T^[n] m₀) Filter.atTop
        (nhds (ContractingWith.fixedPoint T hT)) := by
  refine ⟨⟨ContractingWith.fixedPoint T hT, hT.fixedPoint_isFixedPt, fun y hy => ?_⟩, ?_⟩
  · exact hT.fixedPoint_unique hy
  · intro m₀
    exact hT.tendsto_iterate_fixedPoint m₀

theorem linear_curving (a ε : ℝ) (hε : ε ≠ 1) :
    a + ε * (a / (1 - ε)) = a / (1 - ε) := by
  have h : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm hε)
  field_simp
  ring

/-! ## Relative semantics -/

/-- `a` and `b` are the same relative to the probes `P`. -/
def relEq {Thing Probe R : Type*} (resp : Thing → Probe → R) (P : Set Probe) (a b : Thing) : Prop :=
  ∀ p ∈ P, resp a p = resp b p

theorem relEq_mono {Thing Probe R : Type*} (resp : Thing → Probe → R) {P Q : Set Probe}
    (hPQ : P ⊆ Q) (a b : Thing) (h : relEq resp Q a b) : relEq resp P a b :=
  fun p hp => h p (hPQ hp)

theorem relEq_univ_iff {Thing Probe R : Type*} (resp : Thing → Probe → R) (a b : Thing) :
    relEq resp Set.univ a b ↔ resp a = resp b := by
  constructor
  · intro h; funext p; exact h p (Set.mem_univ p)
  · intro h p _; rw [h]

theorem relEq_empty {Thing Probe R : Type*} (resp : Thing → Probe → R) (a b : Thing) :
    relEq resp ∅ a b :=
  fun _ hp => absurd hp (Set.notMem_empty _)

theorem two_things_need_a_probe {Thing Probe R : Type*} (resp : Thing → Probe → R)
    (P : Set Probe) (a b : Thing) (h : ¬ relEq resp P a b) : P.Nonempty := by
  by_contra hP
  rw [Set.not_nonempty_iff_eq_empty] at hP
  exact h (hP ▸ relEq_empty resp a b)

/-- Steady-state response 1 / (k − m ω²) of an oscillator with mass m and stiffness k. -/
noncomputable def response (mk : ℝ × ℝ) (ω : ℝ) : ℝ := 1 / (mk.2 - mk.1 * ω ^ 2)

/-- Squared resonant frequency k / m. -/
noncomputable def resonance (mk : ℝ × ℝ) : ℝ := mk.2 / mk.1

theorem same_resonance : resonance (1, 1) = resonance (2, 2) := by
  norm_num [resonance]

theorem sweep_separates :
    (1, 1) ≠ ((2, 2) : ℝ × ℝ) ∧ ¬ relEq response Set.univ (1, 1) (2, 2) := by
  refine ⟨by norm_num, ?_⟩
  intro h
  have := h 0 (Set.mem_univ 0)
  norm_num [response] at this

end RelativeSemantics

#print axioms RelativeSemantics.map_is_not_territory
#print axioms RelativeSemantics.constant_velocity_error
#print axioms RelativeSemantics.no_acceleration_iff_affine
#print axioms RelativeSemantics.general_semantics
#print axioms RelativeSemantics.linear_curving
#print axioms RelativeSemantics.relEq_mono
#print axioms RelativeSemantics.relEq_univ_iff
#print axioms RelativeSemantics.relEq_empty
#print axioms RelativeSemantics.two_things_need_a_probe
#print axioms RelativeSemantics.same_resonance
#print axioms RelativeSemantics.sweep_separates
