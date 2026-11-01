import Mathlib

/-!
# ParfitCorrelationBoundA

Bounds on the third correlation of a 3×3 correlation matrix, and failure of
transitivity for graded similarity.

Setting: `corrMat a b c = !![1, a, c; a, 1, b; c, b, 1]`, with
`a = r(A,B)`, `b = r(B,C)`, `c = r(A,C)`.

PROVED
* `det_corrMat`: `det (corrMat a b c) = 1 - a² - b² - c² + 2abc
  = (1 - a²)(1 - b²) - (c - ab)²`.
* `bounds_of_det`: `0 ≤ 1 - a² - b² - c² + 2abc` alone implies
  `ab - √((1-a²)(1-b²)) ≤ c ≤ ab + √((1-a²)(1-b²))`
  (no separate hypothesis `|a|, |b| ≤ 1` is needed).
* `sq_le_of_quadForm_nonneg`, `bounds_of_quadForm_nonneg`: if
  `x² + y² + z² + 2axy + 2byz + 2cxz ≥ 0` for all real `x, y, z`, then
  `(c - ab)² ≤ (1-a²)(1-b²)` and the same two bounds hold.
* `bounds_of_posSemidef`: the same bounds from `(corrMat a b c).PosSemidef`
  (Mathlib's notion), and `det_nonneg_of_posSemidef`.
* `posSemidef_lower_extreme`, `posSemidef_upper_extreme`: for every
  `a, b ∈ [-1, 1]`, both extremes `c = ab ∓ √((1-a²)(1-b²))` give a PSD matrix,
  via an explicit Gram decomposition of the quadratic form into two squares
  (three unit vectors in ℝ²). So both bounds are sharp.
* `witness_posSemidef`, `witness_c_eq_lowerBound`, `witness_c_neg`: for
  `a = b = 7/10`, `c = -1/50 = 49/100 - 51/100` is the lower bound, the matrix is
  PSD (Gram matrix of `u = (1,0)`, `v = (7/10, √51/10)`, `w = (-1/50, 7√51/50)`;
  the quadratic form equals `(x + 7y/10 - z/50)² + (51/100)(y + 7z/5)²`).
* `not_transitive`: there is a PSD correlation matrix with `r(A,B) = r(B,C) = 7/10`
  and `r(A,C) < 0`.
* `gram_witness_unit_vectors`: the three explicit vectors in ℝ² are unit vectors
  with the stated pairwise inner products.

INTERPRETED
* Graded similarity measured by correlation (cosine of angles between unit
  vectors) is not transitive: A strongly resembling B and B strongly resembling C
  (r = 0.7 each) is compatible with A and C being anticorrelated. For a
  Parfit-style psychological-continuity relation measured this way, "strongly
  continuous with a strongly continuous successor" does not imply "continuous".
  The bounds say exactly how much the composite can degrade: angles add, so
  `arccos c ≤ arccos a + arccos b`.
-/

namespace ParfitCorrelationBoundA

open Matrix

/-- The 3×3 correlation matrix with `r(A,B) = a`, `r(B,C) = b`, `r(A,C) = c`. -/
def corrMat (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, a, c; a, 1, b; c, b, 1]

/-- The quadratic form `x · M x` of `corrMat a b c`. -/
def quadForm (a b c x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + z ^ 2 + 2 * a * x * y + 2 * b * y * z + 2 * c * x * z

/-- The bound radius `√((1 - a²)(1 - b²))`. -/
noncomputable def radius (a b : ℝ) : ℝ := Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2))

theorem corrMat_isHermitian (a b c : ℝ) : (corrMat a b c).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corrMat]

theorem dotProduct_corrMat (a b c : ℝ) (v : Fin 3 → ℝ) :
    star v ⬝ᵥ (corrMat a b c *ᵥ v) = quadForm a b c (v 0) (v 1) (v 2) := by
  simp [dotProduct, mulVec, Fin.sum_univ_three, corrMat, quadForm]
  ring

theorem det_corrMat (a b c : ℝ) :
    (corrMat a b c).det = 1 - a ^ 2 - b ^ 2 - c ^ 2 + 2 * a * b * c ∧
    (corrMat a b c).det = (1 - a ^ 2) * (1 - b ^ 2) - (c - a * b) ^ 2 := by
  rw [det_fin_three]
  simp [corrMat]
  constructor <;> ring

/-- The determinant condition alone gives both bounds. -/
theorem bounds_of_det {a b c : ℝ} (h : 0 ≤ 1 - a ^ 2 - b ^ 2 - c ^ 2 + 2 * a * b * c) :
    a * b - radius a b ≤ c ∧ c ≤ a * b + radius a b := by
  have hsq : (c - a * b) ^ 2 ≤ (1 - a ^ 2) * (1 - b ^ 2) := by nlinarith
  have habs := Real.abs_le_sqrt hsq
  rw [abs_le] at habs
  unfold radius
  constructor <;> linarith [habs.1, habs.2]

/-- Minimising the form over `y` leaves a binary form whose discriminant must be
nonpositive. -/
theorem sq_le_of_quadForm_nonneg {a b c : ℝ} (h : ∀ x y z, 0 ≤ quadForm a b c x y z) :
    (c - a * b) ^ 2 ≤ (1 - a ^ 2) * (1 - b ^ 2) := by
  have h2 : ∀ x : ℝ, 0 ≤ (1 - a ^ 2) * (x * x) + 2 * (c - a * b) * x + (1 - b ^ 2) := by
    intro x
    have := h x (-(a * x + b)) 1
    have e : quadForm a b c x (-(a * x + b)) 1
        = (1 - a ^ 2) * (x * x) + 2 * (c - a * b) * x + (1 - b ^ 2) := by
      unfold quadForm; ring
    rw [e] at this
    exact this
  have hd := discrim_le_zero h2
  unfold discrim at hd
  nlinarith [hd]

theorem bounds_of_quadForm_nonneg {a b c : ℝ} (h : ∀ x y z, 0 ≤ quadForm a b c x y z) :
    a * b - radius a b ≤ c ∧ c ≤ a * b + radius a b := by
  apply bounds_of_det
  nlinarith [sq_le_of_quadForm_nonneg h]

theorem quadForm_nonneg_of_posSemidef {a b c : ℝ} (hM : (corrMat a b c).PosSemidef) :
    ∀ x y z, 0 ≤ quadForm a b c x y z := by
  intro x y z
  have := hM.dotProduct_mulVec_nonneg ![x, y, z]
  rw [dotProduct_corrMat] at this
  simpa using this

theorem bounds_of_posSemidef {a b c : ℝ} (hM : (corrMat a b c).PosSemidef) :
    a * b - radius a b ≤ c ∧ c ≤ a * b + radius a b :=
  bounds_of_quadForm_nonneg (quadForm_nonneg_of_posSemidef hM)

theorem det_nonneg_of_posSemidef {a b c : ℝ} (hM : (corrMat a b c).PosSemidef) :
    0 ≤ (corrMat a b c).det := by
  rw [(det_corrMat a b c).2]
  nlinarith [sq_le_of_quadForm_nonneg (quadForm_nonneg_of_posSemidef hM)]

theorem posSemidef_of_quadForm_nonneg {a b c : ℝ} (h : ∀ x y z, 0 ≤ quadForm a b c x y z) :
    (corrMat a b c).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (corrMat_isHermitian a b c) ?_
  intro v
  rw [dotProduct_corrMat]
  exact h _ _ _

/-- Gram decomposition: with `sa = √(1-a²)`, `sb = √(1-b²)`, `s = ±1`, and
`c = ab - s·sa·sb`, the form is a sum of two squares
(vectors `u = (1,0)`, `v = (a, sa)`, `w = (c, sa·b + s·a·sb)`). -/
theorem quadForm_gram {a b sa sb s x y z : ℝ}
    (ha : sa ^ 2 = 1 - a ^ 2) (hb : sb ^ 2 = 1 - b ^ 2) (hs : s ^ 2 = 1) :
    quadForm a b (a * b - s * sa * sb) x y z
      = (x + a * y + (a * b - s * sa * sb) * z) ^ 2
        + (sa * y + (sa * b + s * a * sb) * z) ^ 2 := by
  unfold quadForm
  linear_combination (-(y ^ 2) - 2 * b * y * z - (b ^ 2 + s ^ 2 * sb ^ 2) * z ^ 2) * ha
    - z ^ 2 * hb - sb ^ 2 * z ^ 2 * hs

/-- Both extremes are attained: for `a, b ∈ [-1,1]` and `c = ab - s·√((1-a²)(1-b²))`
with `s = ±1`, the matrix is PSD. -/
theorem posSemidef_extreme {a b s : ℝ} (ha : a ^ 2 ≤ 1) (hb : b ^ 2 ≤ 1) (hs : s ^ 2 = 1) :
    (corrMat a b (a * b - s * radius a b)).PosSemidef := by
  have ha' : 0 ≤ 1 - a ^ 2 := by linarith
  have hb' : 0 ≤ 1 - b ^ 2 := by linarith
  have hr : radius a b = Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) := by
    unfold radius; rw [Real.sqrt_mul ha']
  apply posSemidef_of_quadForm_nonneg
  intro x y z
  rw [hr, ← mul_assoc, quadForm_gram (Real.sq_sqrt ha') (Real.sq_sqrt hb') hs]
  positivity

theorem posSemidef_lower_extreme {a b : ℝ} (ha : a ^ 2 ≤ 1) (hb : b ^ 2 ≤ 1) :
    (corrMat a b (a * b - radius a b)).PosSemidef := by
  simpa using posSemidef_extreme (s := 1) ha hb (by norm_num)

theorem posSemidef_upper_extreme {a b : ℝ} (ha : a ^ 2 ≤ 1) (hb : b ^ 2 ≤ 1) :
    (corrMat a b (a * b + radius a b)).PosSemidef := by
  simpa [sub_eq_add_neg] using posSemidef_extreme (s := -1) ha hb (by norm_num)

/-! ### The witness `a = b = 7/10`, `c = -1/50` -/

/-- Rational sum-of-squares form of the witness quadratic form. -/
theorem witness_quadForm (x y z : ℝ) :
    quadForm (7 / 10) (7 / 10) (-1 / 50) x y z
      = (x + 7 / 10 * y - 1 / 50 * z) ^ 2 + 51 / 100 * (y + 7 / 5 * z) ^ 2 := by
  unfold quadForm; ring

theorem witness_posSemidef : (corrMat (7 / 10) (7 / 10) (-1 / 50)).PosSemidef := by
  apply posSemidef_of_quadForm_nonneg
  intro x y z
  rw [witness_quadForm]
  positivity

theorem radius_witness : radius (7 / 10) (7 / 10) = 51 / 100 := by
  unfold radius
  rw [show (1 - (7 / 10 : ℝ) ^ 2) * (1 - (7 / 10) ^ 2) = (51 / 100) * (51 / 100) by norm_num]
  exact Real.sqrt_mul_self (by norm_num)

theorem witness_c_eq_lowerBound :
    (-1 / 50 : ℝ) = 7 / 10 * (7 / 10) - radius (7 / 10) (7 / 10) ∧
    (-1 / 50 : ℝ) = 49 / 100 - 51 / 100 := by
  rw [radius_witness]; constructor <;> norm_num

theorem witness_c_neg : (-1 / 50 : ℝ) < 0 := by norm_num

/-- Graded similarity is not transitive. -/
theorem not_transitive :
    ∃ c : ℝ, c < 0 ∧ (corrMat (7 / 10) (7 / 10) c).PosSemidef ∧
      c = 7 / 10 * (7 / 10) - radius (7 / 10) (7 / 10) :=
  ⟨-1 / 50, witness_c_neg, witness_posSemidef, witness_c_eq_lowerBound.1⟩

/-- No PSD correlation matrix with `a = b = 7/10` has `c < -1/50`. -/
theorem witness_is_minimum {c : ℝ} (hM : (corrMat (7 / 10) (7 / 10) c).PosSemidef) :
    -1 / 50 ≤ c := by
  have := (bounds_of_posSemidef hM).1
  rw [radius_witness] at this
  linarith

/-- The explicit Gram vectors in ℝ²: unit length with the stated inner products. -/
theorem gram_witness_unit_vectors :
    let u : Fin 2 → ℝ := ![1, 0]
    let v : Fin 2 → ℝ := ![7 / 10, Real.sqrt 51 / 10]
    let w : Fin 2 → ℝ := ![-1 / 50, 7 * Real.sqrt 51 / 50]
    u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ w ⬝ᵥ w = 1 ∧
      u ⬝ᵥ v = 7 / 10 ∧ v ⬝ᵥ w = 7 / 10 ∧ u ⬝ᵥ w = -1 / 50 := by
  intro u v w
  have h51 : Real.sqrt 51 ^ 2 = 51 := Real.sq_sqrt (by norm_num)
  simp only [u, v, w, dotProduct, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> nlinarith [h51]

end ParfitCorrelationBoundA
