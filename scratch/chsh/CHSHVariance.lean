/-
# CHSH from Pythagoras, with covectors

Alice's two settings are covectors f0, f1 (continuous linear functionals E →L[ℝ] ℝ, of norm ≤ 1).
Bob's two settings are vectors b0, b1 in a normed space E (of norm ≤ 1). The score is
  chsh f0 f1 b0 b1 = f0 (b0 + b1) + f1 (b0 − b1).
No inner product is used in the definition: it is the evaluation pairing of covectors with vectors.

PROVED
1. `chsh_natural`: for a linear map T : E → F, pulling Alice's covectors back along T and pushing
   Bob's vectors forward along T give the same score. Covectors move contravariantly, vectors
   covariantly.
2. `chsh_le_diagonals`: in any normed space, the score is at most ‖b0 + b1‖ + ‖b0 − b1‖.
3. `chsh_le_four`: in any normed space, the score is at most 4.
4. `chsh_le_two_sqrt_two_of_parallelogram`: if the two diagonals satisfy the parallelogram law,
   ‖b0 + b1‖² + ‖b0 − b1‖² = 2‖b0‖² + 2‖b1‖², the score is at most 2√2.
5. `tsirelson_inner`: in every real inner product space the parallelogram law holds, so the score
   is at most 2√2.
6. `four_in_prod`: in Mathlib's `ℝ × ℝ`, whose norm is the max norm, the score 4 is reached with
   f0 = fst, f1 = snd, b0 = (1, 1), b1 = (1, −1).

So the same game has value 2√2 in a Euclidean type and 4 in `ℝ × ℝ`. The difference is carried by
the norm instance of the type.

Universes: E lives in `Type u` for a fixed universe variable u. Each theorem is a family of
statements, one per universe level; no single proposition here ranges over all universes.

INTERPRETED (not formalized)
- Quantum correlations are inner products of unit vectors (Tsirelson's theorem). The square
  unit ball of the max norm corresponds to the "squared bit" state space, where PR-box correlations
  are possible; regular-polygon state spaces between the square and the disc interpolate between
  4 and 2√2 (Janotta, Gogolin, Barrett, Brunner 2011). Cited, not proved here.
- By Jordan–von Neumann, a norm comes from an inner product exactly when the parallelogram law
  holds everywhere; item 4 uses it only for the one pair b0, b1.
-/

import Mathlib

universe u v

namespace CHSHVariance

section General

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The CHSH score: Alice's covectors evaluated on Bob's two diagonals. -/
def chsh (f0 f1 : E →L[ℝ] ℝ) (b0 b1 : E) : ℝ := f0 (b0 + b1) + f1 (b0 - b1)

theorem chsh_natural {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (f0 f1 : F →L[ℝ] ℝ) (b0 b1 : E) :
    chsh (f0.comp T) (f1.comp T) b0 b1 = chsh f0 f1 (T b0) (T b1) := by
  simp [chsh, map_add, map_sub]

theorem eval_le (f : E →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) (x : E) : f x ≤ ‖x‖ := by
  have h1 : f x ≤ ‖f x‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
  have h2 := f.le_opNorm x
  have h3 : ‖f‖ * ‖x‖ ≤ ‖x‖ := mul_le_of_le_one_left (norm_nonneg x) hf
  linarith

theorem chsh_le_diagonals (f0 f1 : E →L[ℝ] ℝ) (hf0 : ‖f0‖ ≤ 1) (hf1 : ‖f1‖ ≤ 1) (b0 b1 : E) :
    chsh f0 f1 b0 b1 ≤ ‖b0 + b1‖ + ‖b0 - b1‖ := by
  unfold chsh
  linarith [eval_le f0 hf0 (b0 + b1), eval_le f1 hf1 (b0 - b1)]

theorem chsh_le_four (f0 f1 : E →L[ℝ] ℝ) (hf0 : ‖f0‖ ≤ 1) (hf1 : ‖f1‖ ≤ 1) (b0 b1 : E)
    (hb0 : ‖b0‖ ≤ 1) (hb1 : ‖b1‖ ≤ 1) :
    chsh f0 f1 b0 b1 ≤ 4 := by
  have := chsh_le_diagonals f0 f1 hf0 hf1 b0 b1
  linarith [norm_add_le b0 b1, norm_sub_le b0 b1]

theorem chsh_le_two_sqrt_two_of_parallelogram (f0 f1 : E →L[ℝ] ℝ) (hf0 : ‖f0‖ ≤ 1)
    (hf1 : ‖f1‖ ≤ 1) (b0 b1 : E) (hb0 : ‖b0‖ ≤ 1) (hb1 : ‖b1‖ ≤ 1)
    (hpar : ‖b0 + b1‖ ^ 2 + ‖b0 - b1‖ ^ 2 = 2 * ‖b0‖ ^ 2 + 2 * ‖b1‖ ^ 2) :
    chsh f0 f1 b0 b1 ≤ 2 * Real.sqrt 2 := by
  have hd := chsh_le_diagonals f0 f1 hf0 hf1 b0 b1
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hu := norm_nonneg (b0 + b1)
  have hv := norm_nonneg (b0 - b1)
  have hn0 := norm_nonneg b0
  have hn1 := norm_nonneg b1
  have h4 : ‖b0 + b1‖ ^ 2 + ‖b0 - b1‖ ^ 2 ≤ 4 := by nlinarith
  have hsum : ‖b0 + b1‖ + ‖b0 - b1‖ ≤ 2 * Real.sqrt 2 := by
    nlinarith [sq_nonneg (‖b0 + b1‖ - ‖b0 - b1‖)]
  linarith

end General

theorem tsirelson_inner {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f0 f1 : E →L[ℝ] ℝ) (hf0 : ‖f0‖ ≤ 1) (hf1 : ‖f1‖ ≤ 1) (b0 b1 : E)
    (hb0 : ‖b0‖ ≤ 1) (hb1 : ‖b1‖ ≤ 1) :
    chsh f0 f1 b0 b1 ≤ 2 * Real.sqrt 2 := by
  refine chsh_le_two_sqrt_two_of_parallelogram f0 f1 hf0 hf1 b0 b1 hb0 hb1 ?_
  rw [norm_add_sq_real, norm_sub_sq_real]
  ring

theorem four_in_prod :
    ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 ∧ ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 ∧
      ‖((1 : ℝ), (1 : ℝ))‖ = 1 ∧ ‖((1 : ℝ), (-1 : ℝ))‖ = 1 ∧
      chsh (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ)
        ((1 : ℝ), (1 : ℝ)) ((1 : ℝ), (-1 : ℝ)) = 4 := by
  refine ⟨ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ, ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ,
    ?_, ?_, ?_⟩
  · simp [Prod.norm_def]
  · simp [Prod.norm_def]
  · simp [chsh]; norm_num

end CHSHVariance

#print axioms CHSHVariance.chsh_natural
#print axioms CHSHVariance.chsh_le_diagonals
#print axioms CHSHVariance.chsh_le_four
#print axioms CHSHVariance.chsh_le_two_sqrt_two_of_parallelogram
#print axioms CHSHVariance.tsirelson_inner
#print axioms CHSHVariance.four_in_prod
