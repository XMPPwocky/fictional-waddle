import Mathlib

/-!
# The Nash product is the Minkowski interval

PROVED:
* `nash_product_eq_interval`: in light-cone coordinates `u₁ = t + x`, `u₂ = t − x`, the Nash product `u₁ u₂` is the
  Minkowski interval `t² − x²`, so the level sets of the Nash product are the hyperbolas of special relativity.
* `boost_eq_squeeze`: the Lorentz boost with rapidity `η` acts on light-cone coordinates as the squeeze
  `(u₁, u₂) ↦ (eᶯ u₁, e⁻ᶯ u₂)`.
* `squeeze_preserves_nash`: the squeeze preserves the Nash product exactly, so it preserves `t² − x²`.
* `rescale_nash`: rescaling the two utilities independently by `a, b > 0` multiplies the Nash product by `a b`, so it
  never changes which option maximizes it; the boosts are exactly the rescalings with `a b = 1`, which also keep its
  value.
* `nash_argmax_invariant`: for any finite set of options with positive gains, an option maximizes `u₁ u₂` iff it
  maximizes `(a u₁)(b u₂)`.
* `cut_and_choose`: if the cutter splits the cake into two pieces she values equally and the chooser takes the piece he
  values more, each gets at least half of the cake by their own measure, and neither prefers the other's piece.
* `rotation_fair_on_average`: if the whole resource goes to player `t mod n` at time `t`, then over one full cycle,
  times `0` to `n − 1`, every player receives exactly one share.
-/

namespace NashIsMinkowski
open Real

theorem nash_product_eq_interval (t x : ℝ) : (t + x) * (t - x) = t ^ 2 - x ^ 2 := by ring

theorem boost_eq_squeeze (η t x : ℝ) :
    let t' := t * cosh η + x * sinh η
    let x' := x * cosh η + t * sinh η
    t' + x' = exp η * (t + x) ∧ t' - x' = exp (-η) * (t - x) := by
  intro t' x'
  simp only [t', x', cosh_eq, sinh_eq]
  constructor <;> ring

theorem squeeze_preserves_nash (η u₁ u₂ : ℝ) : (exp η * u₁) * (exp (-η) * u₂) = u₁ * u₂ := by
  have h : exp η * exp (-η) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  calc (exp η * u₁) * (exp (-η) * u₂) = (exp η * exp (-η)) * (u₁ * u₂) := by ring
    _ = u₁ * u₂ := by rw [h, one_mul]

theorem boost_preserves_interval (η t x : ℝ) :
    (t * cosh η + x * sinh η) ^ 2 - (x * cosh η + t * sinh η) ^ 2 = t ^ 2 - x ^ 2 := by
  have h := cosh_sq_sub_sinh_sq η
  nlinarith [h]

theorem rescale_nash (a b u₁ u₂ : ℝ) : (a * u₁) * (b * u₂) = (a * b) * (u₁ * u₂) := by ring

theorem nash_argmax_invariant {X : Type*} (u₁ u₂ : X → ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : X) :
    (∀ y, u₁ y * u₂ y ≤ u₁ x * u₂ x) ↔ (∀ y, (a * u₁ y) * (b * u₂ y) ≤ (a * u₁ x) * (b * u₂ x)) := by
  have hab : 0 < a * b := mul_pos ha hb
  constructor
  · intro h y
    have := mul_le_mul_of_nonneg_left (h y) hab.le
    linarith [rescale_nash a b (u₁ y) (u₂ y), rescale_nash a b (u₁ x) (u₂ x)]
  · intro h y
    have h2 := h y
    exact le_of_mul_le_mul_left
      (by linarith [rescale_nash a b (u₁ y) (u₂ y), rescale_nash a b (u₁ x) (u₂ x)]) hab

theorem cut_and_choose (vA vB wA wB : ℝ) (hcut : vA = vB) :
    let chooserGets := max wA wB
    let cutterGets := if wB ≤ wA then vB else vA
    cutterGets = (vA + vB) / 2 ∧ (wA + wB) / 2 ≤ chooserGets ∧
      (if wB ≤ wA then wB ≤ wA else wA ≤ wB) := by
  intro chooserGets cutterGets
  refine ⟨?_, ?_, ?_⟩
  · simp only [cutterGets]; split_ifs <;> linarith
  · simp only [chooserGets]
    rcases le_total wA wB with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  · split_ifs with h
    · exact h
    · exact (not_le.mp h).le

theorem rotation_fair_on_average (n : ℕ) (v : ℝ) (i : Fin n) :
    ∑ t ∈ Finset.range n, (if t % n = i.val then v else 0) = v := by
  have h : ∀ t ∈ Finset.range n, (if t % n = i.val then v else 0) = if i.val = t then v else 0 := by
    intro t ht
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp ht)]
    by_cases hti : t = i.val
    · simp [hti]
    · simp [hti, Ne.symm hti]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]
  simp [i.isLt]

end NashIsMinkowski
