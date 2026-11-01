/-
# What two observers agree on fits exactly in a 1+1 light cone

Two observers each list a set of events in order (rank functions r₁, r₂). The pairs they both order the
same way form a partial order: a ≼ b iff r₁ a ≤ r₁ b and r₂ a ≤ r₂ b (an order of dimension at most 2).
Place event a at light-cone coordinates (u, v) = (r₁ a, r₂ a), i.e. time t = (u + v)/2 and space
x = (v − u)/2.

PROVED
1. `cone_iff`: for a displacement (Δu, Δv), Δt ≥ |Δx| exactly when Δu ≥ 0 and Δv ≥ 0. The future light
   cone in light-cone coordinates is the positive quadrant.
2. `agree_iff_causal`: a ≼ b (both observers put a no later than b) exactly when b lies in the future light
   cone of a under the placement above. The agreed order embeds exactly, with no distortion, as the causal
   order of 1+1 Minkowski space.
3. `disagree_iff_spacelike`: the observers order a and b oppositely exactly when the displacement is
   spacelike (|Δx| > Δt).

CITED, NOT PROVED HERE
- Dushnik–Miller: a partial order has dimension ≤ 2 exactly when it is the intersection of two linear
  orders, so item 2 covers every such order. The standard example S₃ has dimension 3 and does not embed in
  1+1 Minkowski space.
- Sarkar (2011): every weighted tree embeds in the hyperbolic plane with distortion arbitrarily close to 1,
  so tree-like (hierarchical) structure fits two dimensions when the plane is hyperbolic.
-/

import Mathlib

namespace TwoObserverMinkowski

theorem cone_iff (du dv : ℝ) : (du + dv) / 2 ≥ |(dv - du) / 2| ↔ 0 ≤ du ∧ 0 ≤ dv := by
  constructor
  · intro h
    have h1 := le_abs_self ((dv - du) / 2)
    have h2 := neg_abs_le ((dv - du) / 2)
    constructor <;> linarith
  · rintro ⟨hu, hv⟩
    rw [ge_iff_le, abs_le]
    constructor <;> linarith

theorem agree_iff_causal {E : Type*} (r₁ r₂ : E → ℝ) (a b : E) :
    (r₁ a ≤ r₁ b ∧ r₂ a ≤ r₂ b) ↔
      ((r₁ b - r₁ a) + (r₂ b - r₂ a)) / 2 ≥ |((r₂ b - r₂ a) - (r₁ b - r₁ a)) / 2| := by
  rw [cone_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem disagree_iff_spacelike {E : Type*} (r₁ r₂ : E → ℝ) (a b : E) :
    ((r₁ a < r₁ b ∧ r₂ b < r₂ a) ∨ (r₁ b < r₁ a ∧ r₂ a < r₂ b)) ↔
      |((r₂ b - r₂ a) - (r₁ b - r₁ a)) / 2| > |((r₁ b - r₁ a) + (r₂ b - r₂ a)) / 2| := by
  generalize hdu : r₁ b - r₁ a = du
  generalize hdv : r₂ b - r₂ a = dv
  have key : |(dv - du) / 2| > |(du + dv) / 2| ↔ (0 < du ∧ dv < 0) ∨ (du < 0 ∧ 0 < dv) := by
    rw [gt_iff_lt, ← sq_lt_sq]
    constructor
    · intro h
      have : du * dv < 0 := by nlinarith
      rcases lt_or_gt_of_ne (show du ≠ 0 by rintro rfl; simp at this) with hd | hd
      · right; exact ⟨hd, by nlinarith⟩
      · left; exact ⟨hd, by nlinarith⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · nlinarith [mul_neg_of_pos_of_neg h1 h2]
      · nlinarith [mul_neg_of_neg_of_pos h1 h2]
  rw [key]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left; constructor <;> linarith
    · right; constructor <;> linarith

end TwoObserverMinkowski

#print axioms TwoObserverMinkowski.cone_iff
#print axioms TwoObserverMinkowski.agree_iff_causal
#print axioms TwoObserverMinkowski.disagree_iff_spacelike
