import Mathlib

/-!
# Correlation bounds for three variables (graded similarity is not transitive)

PROVED
* `quadForm_nonneg_iff_posSemidef`: for `corrMatrix a b c = !![1,a,c; a,1,b; c,b,1]`,
  positive semidefiniteness (Mathlib `Matrix.PosSemidef`) is equivalent to
  `∀ x y z, 0 ≤ x² + y² + z² + 2axy + 2byz + 2cxz`.
* `entries_and_det_of_quadForm`: the quadratic-form condition gives `a² ≤ 1`, `b² ≤ 1` and
  `0 ≤ det = 1 − a² − b² − c² + 2abc`.
* `bounds_of_det`: `0 ≤ det` alone gives
  `a·b − √((1−a²)(1−b²)) ≤ c ≤ a·b + √((1−a²)(1−b²))`.
* `bounds_of_quadForm`, `bounds_of_posSemidef`: the same bounds from either PSD formulation.
* `gram_eq`, `posSemidef_of_gram`: for any `a b ∈ [−1,1]` and any `sa, sb` with `sa² = 1 − a²`,
  `sb² = 1 − b²`, the matrix `corrMatrix a b (a·b − sa·sb)` is the Gram matrix `Bᴴ B` of three
  unit vectors in `ℝ²`, hence PSD.
* `lower_attained`, `upper_attained`: both bounds are attained by PSD correlation matrices,
  for every `a b ∈ [−1,1]`; so the bounds are sharp.
* `witness_posSemidef`, `witness_lower_bound_eq`, `witness_not_transitive`: for
  `a = b = 7/10`, `c = −1/50 = 49/100 − 51/100` gives a PSD correlation matrix
  (Gram matrix of `(1,0)`, `(7/10, √51/10)`, `(−1/50, 7√51/50)`), `c` equals the lower bound,
  and `0 < a`, `0 < b`, `c < 0`.

INTERPRETED
* `a = r(A,B)`, `b = r(B,C)`, `c = r(A,C)` are correlations (cosine similarities) between three
  states of a person; PSD of the correlation matrix is exactly realizability by unit vectors.
* The witness shows that strong positive similarity of A to B and of B to C does not force any
  positive similarity of A to C: graded psychological connectedness is not transitive, which is
  the formal content behind Parfit's distinction between connectedness and continuity.
-/

namespace ParfitCorrelationBoundB

open Matrix

/-- Unit-diagonal symmetric 3×3 matrix with `r(A,B) = a`, `r(B,C) = b`, `r(A,C) = c`. -/
def corrMatrix (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, a, c; a, 1, b; c, b, 1]

/-- The quadratic form `xᵀ M x` of `corrMatrix a b c`. -/
def quadForm (a b c x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + z ^ 2 + 2 * a * x * y + 2 * b * y * z + 2 * c * x * z

/-- Determinant of `corrMatrix a b c`. -/
def det3 (a b c : ℝ) : ℝ := 1 - a ^ 2 - b ^ 2 - c ^ 2 + 2 * a * b * c

theorem det_corrMatrix (a b c : ℝ) : (corrMatrix a b c).det = det3 a b c := by
  simp [corrMatrix, det3, Matrix.det_fin_three]
  ring

theorem corrMatrix_isHermitian (a b c : ℝ) : (corrMatrix a b c).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corrMatrix, Matrix.conjTranspose_apply]

theorem dot_eq_quadForm (a b c : ℝ) (v : Fin 3 → ℝ) :
    star v ⬝ᵥ (corrMatrix a b c *ᵥ v) = quadForm a b c (v 0) (v 1) (v 2) := by
  simp [corrMatrix, quadForm, dotProduct, mulVec, Fin.sum_univ_three]
  ring

theorem quadForm_nonneg_iff_posSemidef (a b c : ℝ) :
    (corrMatrix a b c).PosSemidef ↔ ∀ x y z : ℝ, 0 ≤ quadForm a b c x y z := by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, h⟩ x y z
    have := h ![x, y, z]
    rw [dot_eq_quadForm] at this
    simpa using this
  · intro h
    refine ⟨corrMatrix_isHermitian a b c, fun v => ?_⟩
    rw [dot_eq_quadForm]
    exact h _ _ _

/-- The quadratic-form condition implies `a² ≤ 1`, `b² ≤ 1` and nonnegative determinant. -/
theorem entries_and_det_of_quadForm {a b c : ℝ} (h : ∀ x y z : ℝ, 0 ≤ quadForm a b c x y z) :
    a ^ 2 ≤ 1 ∧ b ^ 2 ≤ 1 ∧ 0 ≤ det3 a b c := by
  have hp : 0 ≤ 1 - a ^ 2 := by
    have := h 1 (-a) 0; unfold quadForm at this; nlinarith
  have hq : 0 ≤ 1 - b ^ 2 := by
    have := h 0 1 (-b); unfold quadForm at this; nlinarith
  -- reduced form after eliminating `y = -(a x + b z)`
  have hred : ∀ x z : ℝ,
      0 ≤ (1 - a ^ 2) * x ^ 2 + (1 - b ^ 2) * z ^ 2 + 2 * (c - a * b) * x * z := by
    intro x z
    have := h x (-(a * x + b * z)) z
    unfold quadForm at this
    nlinarith
  have key : (c - a * b) ^ 2 ≤ (1 - a ^ 2) * (1 - b ^ 2) := by
    set p := 1 - a ^ 2
    set q := 1 - b ^ 2
    set r := c - a * b
    rcases hq.lt_or_eq with hq' | hq'
    · have := hred q (-r)
      have h2 : 0 ≤ q * (p * q - r ^ 2) := by nlinarith
      nlinarith [(mul_nonneg_iff_of_pos_left hq').mp h2]
    · rcases hp.lt_or_eq with hp' | hp'
      · have := hred (-r) p
        rw [← hq'] at this
        have h2 : 0 ≤ p * (- r ^ 2) := by nlinarith
        have := (mul_nonneg_iff_of_pos_left hp').mp h2
        rw [← hq']; nlinarith [sq_nonneg r]
      · have := hred 1 (-r)
        rw [← hq', ← hp'] at this
        rw [← hq', ← hp']; nlinarith [sq_nonneg r]
  refine ⟨by linarith, by linarith, ?_⟩
  unfold det3
  nlinarith [key]

/-- Nonnegative determinant alone yields the two-sided bound on `c`. -/
theorem bounds_of_det {a b c : ℝ} (h : 0 ≤ det3 a b c) :
    a * b - Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) ≤ c ∧
      c ≤ a * b + Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) := by
  have key : (c - a * b) ^ 2 ≤ (1 - a ^ 2) * (1 - b ^ 2) := by
    unfold det3 at h; nlinarith
  have habs := Real.abs_le_sqrt key
  rw [abs_le] at habs
  constructor <;> linarith [habs.1, habs.2]

theorem bounds_of_quadForm {a b c : ℝ} (h : ∀ x y z : ℝ, 0 ≤ quadForm a b c x y z) :
    a * b - Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) ≤ c ∧
      c ≤ a * b + Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) :=
  bounds_of_det (entries_and_det_of_quadForm h).2.2

theorem bounds_of_posSemidef {a b c : ℝ} (h : (corrMatrix a b c).PosSemidef) :
    a * b - Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) ≤ c ∧
      c ≤ a * b + Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) :=
  bounds_of_quadForm ((quadForm_nonneg_iff_posSemidef a b c).mp h)

/-- Columns: `u = (1,0)`, `v = (a, sa)`, `w = (ab − sa·sb, sa·b + a·sb)`. -/
def gramB (a b sa sb : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![1, a, a * b - sa * sb; 0, sa, sa * b + a * sb]

theorem gram_eq {a b sa sb : ℝ} (ha : sa ^ 2 = 1 - a ^ 2) (hb : sb ^ 2 = 1 - b ^ 2) :
    (gramB a b sa sb)ᴴ * gramB a b sa sb = corrMatrix a b (a * b - sa * sb) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramB, corrMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
      | linear_combination ha
      | linear_combination b * ha
      | linear_combination (b ^ 2 + sb ^ 2) * ha + hb

theorem posSemidef_of_gram {a b sa sb : ℝ} (ha : sa ^ 2 = 1 - a ^ 2) (hb : sb ^ 2 = 1 - b ^ 2) :
    (corrMatrix a b (a * b - sa * sb)).PosSemidef := by
  rw [← gram_eq ha hb]
  exact posSemidef_conjTranspose_mul_self _

/-- The lower bound is attained by a PSD correlation matrix for every `a b ∈ [−1,1]`. -/
theorem lower_attained {a b : ℝ} (ha : a ^ 2 ≤ 1) (hb : b ^ 2 ≤ 1) :
    (corrMatrix a b (a * b - Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)))).PosSemidef := by
  have h1 : (0 : ℝ) ≤ 1 - a ^ 2 := by linarith
  have h2 : (0 : ℝ) ≤ 1 - b ^ 2 := by linarith
  rw [Real.sqrt_mul h1]
  exact posSemidef_of_gram (Real.sq_sqrt h1) (Real.sq_sqrt h2)

/-- The upper bound is attained by a PSD correlation matrix for every `a b ∈ [−1,1]`. -/
theorem upper_attained {a b : ℝ} (ha : a ^ 2 ≤ 1) (hb : b ^ 2 ≤ 1) :
    (corrMatrix a b (a * b + Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)))).PosSemidef := by
  have h1 : (0 : ℝ) ≤ 1 - a ^ 2 := by linarith
  have h2 : (0 : ℝ) ≤ 1 - b ^ 2 := by linarith
  have e : a * b + Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) =
      a * b - Real.sqrt (1 - a ^ 2) * (-Real.sqrt (1 - b ^ 2)) := by
    rw [Real.sqrt_mul h1]; ring
  rw [e]
  exact posSemidef_of_gram (Real.sq_sqrt h1) (by rw [neg_sq, Real.sq_sqrt h2])

/-- Explicit Gram factor of the witness: columns `(1,0)`, `(7/10, √51/10)`, `(−1/50, 7√51/50)`. -/
noncomputable def witnessB : Matrix (Fin 2) (Fin 3) ℝ :=
  !![1, 7 / 10, -1 / 50; 0, Real.sqrt 51 / 10, 7 * Real.sqrt 51 / 50]

theorem witness_gram : witnessBᴴ * witnessB = corrMatrix (7 / 10) (7 / 10) (-1 / 50) := by
  have hs : Real.sqrt 51 ^ 2 = 51 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessB, corrMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [hs]

theorem witness_posSemidef : (corrMatrix (7 / 10) (7 / 10) (-1 / 50)).PosSemidef := by
  rw [← witness_gram]
  exact posSemidef_conjTranspose_mul_self _

/-- The witness sits exactly on the lower bound: `−1/50 = 49/100 − 51/100`. -/
theorem witness_lower_bound_eq :
    (-1 / 50 : ℝ) = 7 / 10 * (7 / 10) -
      Real.sqrt ((1 - (7 / 10 : ℝ) ^ 2) * (1 - (7 / 10 : ℝ) ^ 2)) := by
  have : (1 - (7 / 10 : ℝ) ^ 2) * (1 - (7 / 10 : ℝ) ^ 2) = (51 / 100) ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num)]
  norm_num

/-- Graded similarity is not transitive: a valid correlation matrix with `r(A,B) > 0`,
`r(B,C) > 0`, `r(A,C) < 0`. -/
theorem witness_not_transitive :
    ∃ a b c : ℝ, (corrMatrix a b c).PosSemidef ∧ 0 < a ∧ 0 < b ∧ c < 0 ∧
      c = a * b - Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) :=
  ⟨7 / 10, 7 / 10, -1 / 50, witness_posSemidef, by norm_num, by norm_num, by norm_num,
    witness_lower_bound_eq⟩

end ParfitCorrelationBoundB
