/-
# Three bounds on the CHSH game

S = a0·(b0 + b1) + a1·(b0 − b1), where each player has two settings.

PROVED
1. `classical_chsh`: if every a_i, b_j is ±1 (a fixed answer per setting), then S ≤ 2.
2. `tsirelson`: if a0, a1, b0, b1 are unit vectors in any real inner product space and the products
   are inner products, then S ≤ 2√2. The proof is Cauchy–Schwarz plus the parallelogram law
   ‖b0 + b1‖² + ‖b0 − b1‖² = 4, the Pythagorean theorem for the two diagonals.
3. `tsirelson_attained`: in the plane, a0 = (1,0), a1 = (0,1), b0, b1 at ±45° give S = 2√2.
4. `algebraic_max`: four correlations each in [−1, 1] give E00 + E01 + E10 − E11 ≤ 4.

INTERPRETED (not formalized)
- That quantum correlations are exactly inner products of unit vectors is Tsirelson's theorem,
  cited, not proved here. The value 4 is reached by the no-signalling "PR box", which is not
  constructed here.
-/

import Mathlib

namespace TsirelsonPythagoras

theorem classical_chsh (a0 a1 b0 b1 : ℝ)
    (ha0 : a0 = 1 ∨ a0 = -1) (ha1 : a1 = 1 ∨ a1 = -1)
    (hb0 : b0 = 1 ∨ b0 = -1) (hb1 : b1 = 1 ∨ b1 = -1) :
    a0 * (b0 + b1) + a1 * (b0 - b1) ≤ 2 := by
  rcases ha0 with rfl | rfl <;> rcases ha1 with rfl | rfl <;>
    rcases hb0 with rfl | rfl <;> rcases hb1 with rfl | rfl <;> norm_num

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem diagonals_sq (b0 b1 : E) (hb0 : ‖b0‖ = 1) (hb1 : ‖b1‖ = 1) :
    ‖b0 + b1‖ ^ 2 + ‖b0 - b1‖ ^ 2 = 4 := by
  rw [norm_add_sq_real, norm_sub_sq_real, hb0, hb1]
  ring

theorem tsirelson (a0 a1 b0 b1 : E) (ha0 : ‖a0‖ = 1) (ha1 : ‖a1‖ = 1)
    (hb0 : ‖b0‖ = 1) (hb1 : ‖b1‖ = 1) :
    inner ℝ a0 (b0 + b1) + inner ℝ a1 (b0 - b1) ≤ 2 * Real.sqrt 2 := by
  have h1 : inner ℝ a0 (b0 + b1) ≤ ‖b0 + b1‖ := by
    have := real_inner_le_norm a0 (b0 + b1)
    rwa [ha0, one_mul] at this
  have h2 : inner ℝ a1 (b0 - b1) ≤ ‖b0 - b1‖ := by
    have := real_inner_le_norm a1 (b0 - b1)
    rwa [ha1, one_mul] at this
  have hd := diagonals_sq b0 b1 hb0 hb1
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hu := norm_nonneg (b0 + b1)
  have hv := norm_nonneg (b0 - b1)
  have hsum : ‖b0 + b1‖ + ‖b0 - b1‖ ≤ 2 * Real.sqrt 2 := by
    nlinarith [sq_nonneg (‖b0 + b1‖ - ‖b0 - b1‖)]
  linarith

/-- Dot product on the plane. -/
def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

theorem tsirelson_attained :
    let s := Real.sqrt 2 / 2
    let a0 : ℝ × ℝ := (1, 0)
    let a1 : ℝ × ℝ := (0, 1)
    let b0 : ℝ × ℝ := (s, s)
    let b1 : ℝ × ℝ := (s, -s)
    dot a0 a0 = 1 ∧ dot a1 a1 = 1 ∧ dot b0 b0 = 1 ∧ dot b1 b1 = 1 ∧
      dot a0 (b0 + b1) + dot a1 (b0 - b1) = 2 * Real.sqrt 2 := by
  intro s a0 a1 b0 b1
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [dot, a0, a1, b0, b1, s, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  refine ⟨by ring, by ring, ?_, ?_, ?_⟩ <;> nlinarith [hs]

theorem algebraic_max (E00 E01 E10 E11 : ℝ) (h00 : |E00| ≤ 1) (h01 : |E01| ≤ 1)
    (h10 : |E10| ≤ 1) (h11 : |E11| ≤ 1) :
    E00 + E01 + E10 - E11 ≤ 4 := by
  have := (abs_le.mp h00).2
  have := (abs_le.mp h01).2
  have := (abs_le.mp h10).2
  have := (abs_le.mp h11).1
  linarith

end TsirelsonPythagoras

#print axioms TsirelsonPythagoras.classical_chsh
#print axioms TsirelsonPythagoras.tsirelson
#print axioms TsirelsonPythagoras.tsirelson_attained
#print axioms TsirelsonPythagoras.algebraic_max
