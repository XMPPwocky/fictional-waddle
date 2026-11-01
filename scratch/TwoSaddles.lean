import Mathlib

/-!
# Two saddles compose into a well, but only with a rotational part

Area-preserving 2×2 maps (det 1). A map is hyperbolic (a saddle: it has an escape direction) if |trace| > 2, and elliptic
(a bounded rotation: trapped, stable) if |trace| < 2.

* W1 `saddles_compose_to_well`: two saddles whose product is elliptic. Each alone runs off along its unstable direction;
  the composed round trip is a bounded rotation. (The Paul-trap / Kapitza principle, in its smallest form.)
* W2 `symmetric_saddles_never_trap`: if both saddles are SYMMETRIC (pure potential / pure selection), A = diag(λ, 1/λ)
  and B = R A Rᵀ for any rotation R, then trace(AB) ≥ 2: never elliptic. The trap in W1 needs B's antisymmetric
  (rotational, trade) part.
-/

open Matrix

namespace TwoSaddles

/-- **W1.** `A = diag(2, 1/2)` and `B = [[0,1],[−1,3]]` are both saddles (det 1, trace 5/2 and 3), yet `AB` has trace 3/2:
elliptic. -/
theorem saddles_compose_to_well :
    (!![(2 : ℝ), 0; 0, 1 / 2]).det = 1 ∧ (!![(0 : ℝ), 1; -1, 3]).det = 1 ∧
      2 < (!![(2 : ℝ), 0; 0, 1 / 2]).trace ∧ 2 < (!![(0 : ℝ), 1; -1, 3]).trace ∧
      (!![(2 : ℝ), 0; 0, 1 / 2] * !![(0 : ℝ), 1; -1, 3]).trace < 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.det_fin_two_of, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- **W2.** Two symmetric saddles never compose into a trap: with `A = diag(l, 1/l)` and `B = R A Rᵀ` (R the rotation by an
angle with cosine `c` and sine `s`), `trace(AB) = c²(l² + l⁻²) + 2s² ≥ 2`. -/
theorem symmetric_saddles_never_trap (l c s : ℝ) (hl : 0 < l) (hcs : c ^ 2 + s ^ 2 = 1) :
    2 ≤ c ^ 2 * (l ^ 2 + (1 / l) ^ 2) + 2 * s ^ 2 := by
  have h1 : 2 ≤ l ^ 2 + (1 / l) ^ 2 := by
    have : (l - 1 / l) ^ 2 ≥ 0 := sq_nonneg _
    have hh : l * (1 / l) = 1 := by field_simp
    nlinarith
  nlinarith [sq_nonneg c, sq_nonneg s]

/-- The trace formula used in W2, for the record. -/
theorem symmetric_composition_trace (l c s : ℝ) :
    (!![l, 0; 0, 1 / l] * (!![c, -s; s, c] * !![l, 0; 0, 1 / l] * !![c, s; -s, c])).trace
      = c ^ 2 * (l ^ 2 + (1 / l) ^ 2) + s ^ 2 * (l * (1 / l) + (1 / l) * l) := by
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

end TwoSaddles
