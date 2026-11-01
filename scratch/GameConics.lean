import Mathlib

/-!
# Games are conics on a Minkowski plane; closed equilibria do not trade

**Part M.** Two players, one-dimensional strategies, bilinear learning dynamics `ẋ = a y`, `ẏ = b x`, with CoCo coordinates
`s = (a+b)/2` (team / selection part) and `z = (a−b)/2` (zero-sum / trade part).
* M1 `coco_det_minkowski`: `det [[0,a],[b,0]] = −ab = z² − s²`, a Minkowski norm of `(s, z)`.
* M2 `orbit_invariant`: `Q = b x² − a y²` is conserved along the flow, so the orbits are level sets of `Q`, i.e. conics.
* M3 `orbit_type`: the orbits are ellipses iff `z² > s²` (trade dominates), hyperbolas iff `s² > z²` (selection
  dominates), degenerate iff `s² = z²` (the light cone).
* M4 `zero_sum_elliptic`, `team_hyperbolic`: a pure zero-sum game cycles on ellipses; a pure team game runs on hyperbolas.

**Part T.** Flows `J i j` on a finite network (the flow from `i` to `j`).
* T1 `tellegen`: if `J` is antisymmetric and conserved at every node (zero row sums), it is orthogonal to every potential
  difference: `Σᵢⱼ (φ i − φ j) J i j = 0`.
* T2 `no_trade_at_equilibrium`: a flow that is both potential-driven (`J i j = φ i − φ j`) and conserved is zero. A closed
  system relaxed to potential flow has no flow at all.
-/

open Finset

namespace GameConics

/-- **M1.** The dynamics' determinant is the Minkowski norm of the CoCo coordinates. -/
theorem coco_det_minkowski (a b : ℝ) :
    !![(0 : ℝ), a; b, 0].det = ((a - b) / 2) ^ 2 - ((a + b) / 2) ^ 2 := by
  rw [Matrix.det_fin_two_of]; ring

/-- **M2.** `Q = b x² − a y²` is conserved: its derivative along `ẋ = a y`, `ẏ = b x` vanishes. -/
theorem orbit_invariant (a b x y : ℝ) : 2 * b * x * (a * y) - 2 * a * y * (b * x) = 0 := by
  ring

/-- **M3.** Orbit type from the CoCo coordinates. The level sets of `b x² − a y²` are ellipses iff `ab < 0`. -/
theorem orbit_type (a b : ℝ) :
    (a * b < 0 ↔ ((a + b) / 2) ^ 2 < ((a - b) / 2) ^ 2) ∧
      (0 < a * b ↔ ((a - b) / 2) ^ 2 < ((a + b) / 2) ^ 2) ∧
      (a * b = 0 ↔ ((a - b) / 2) ^ 2 = ((a + b) / 2) ^ 2) := by
  have key : ((a - b) / 2) ^ 2 - ((a + b) / 2) ^ 2 = -(a * b) := by ring
  refine ⟨⟨fun h => by linarith, fun h => by linarith⟩, ⟨fun h => by linarith, fun h => by linarith⟩,
    ⟨fun h => by linarith, fun h => by linarith⟩⟩

/-- **M4a.** A pure zero-sum game (`b = −a`, `a ≠ 0`) cycles: elliptic. -/
theorem zero_sum_elliptic (a : ℝ) (ha : a ≠ 0) : a * (-a) < 0 := by
  have h := mul_self_pos.mpr ha
  linarith [show a * (-a) = -(a * a) by ring]

/-- **M4b.** A pure team game (`b = a`, `a ≠ 0`) is hyperbolic. -/
theorem team_hyperbolic (a : ℝ) (ha : a ≠ 0) : 0 < a * a := by
  exact mul_self_pos.mpr ha

variable {n : ℕ}

/-- **T1.** Tellegen: a conserved antisymmetric flow is orthogonal to every potential difference. -/
theorem tellegen (J : Fin n → Fin n → ℝ) (φ : Fin n → ℝ) (hanti : ∀ i j, J i j = -J j i)
    (hcons : ∀ i, ∑ j, J i j = 0) : ∑ i, ∑ j, (φ i - φ j) * J i j = 0 := by
  have h1 : ∑ i, ∑ j, φ i * J i j = 0 := by
    simp [← Finset.mul_sum, hcons]
  have h2 : ∑ i, ∑ j, φ j * J i j = 0 := by
    rw [Finset.sum_comm]
    have hc : ∀ j, ∑ i, φ j * J i j = 0 := by
      intro j
      rw [← Finset.mul_sum]
      have : ∑ i, J i j = 0 := by
        rw [Finset.sum_congr rfl (fun i _ => hanti i j), Finset.sum_neg_distrib, hcons j, neg_zero]
      rw [this, mul_zero]
    simp [hc]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [h1, h2, sub_zero]

/-- **T2.** A flow that is both potential-driven and conserved is zero. -/
theorem no_trade_at_equilibrium (φ : Fin n → ℝ) (hcons : ∀ i, ∑ j, (φ i - φ j) = 0) :
    ∀ i j, φ i - φ j = 0 := by
  intro i j
  have hi := hcons i
  have hj := hcons j
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hi hj
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos i
  have : (n : ℝ) * φ i = n * φ j := by linarith
  have := mul_left_cancel₀ hn.ne' this
  linarith

end GameConics
