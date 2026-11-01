import Mathlib

/-!
# Entropy production over ordered pairs is twice the Schnakenberg value

Setting: `ι` a finite linearly ordered type, `M : Matrix ι ι ℝ` with `M i j > 0` for `i ≠ j`,
`π : ι → ℝ` with `π i > 0`. Flux `J i j = π i * M i j - π j * M j i`, edge term
`phi i j = J i j * log ((π i * M i j) / (π j * M j i))`.
`sigmaOrdered` sums `phi` over ordered pairs `i ≠ j`; `sigmaUnordered` sums over `i < j`.

PROVED
* `phi_symm`: `phi i j = phi j i` (no positivity hypotheses needed).
* `sigmaOrdered_eq_two_mul`: `sigmaOrdered = 2 * sigmaUnordered` (no positivity hypotheses needed).
* `term_nonneg`: for `a, b > 0`, `0 ≤ (a - b) * log (a / b)`.
* `term_eq_zero_iff`: for `a, b > 0`, `(a - b) * log (a / b) = 0 ↔ a = b`.
* `phi_nonneg`: under the positivity hypotheses, `0 ≤ phi i j` for `i ≠ j`.
* `sigmaOrdered_nonneg`: under the positivity hypotheses, `0 ≤ sigmaOrdered`.
* `sigmaUnordered_nonneg`: under the positivity hypotheses, `0 ≤ sigmaUnordered`.
* `sigmaOrdered_eq_zero_iff`: under the positivity hypotheses, `sigmaOrdered = 0` iff
  `π i * M i j = π j * M j i` for all `i ≠ j` (detailed balance).
-/

namespace EntropyProductionOrderedPairs

open Finset

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Net probability flux from `i` to `j`. -/
def J (M : Matrix ι ι ℝ) (π : ι → ℝ) (i j : ι) : ℝ :=
  π i * M i j - π j * M j i

/-- Entropy production contribution of the ordered pair `(i, j)`. -/
noncomputable def phi (M : Matrix ι ι ℝ) (π : ι → ℝ) (i j : ι) : ℝ :=
  J M π i j * Real.log ((π i * M i j) / (π j * M j i))

/-- Sum of `phi` over ordered pairs with `i ≠ j`. -/
noncomputable def sigmaOrdered (M : Matrix ι ι ℝ) (π : ι → ℝ) : ℝ :=
  ∑ p ∈ univ.filter (fun p : ι × ι => p.1 ≠ p.2), phi M π p.1 p.2

/-- Sum of `phi` over pairs with `i < j` (Schnakenberg entropy production). -/
noncomputable def sigmaUnordered (M : Matrix ι ι ℝ) (π : ι → ℝ) : ℝ :=
  ∑ p ∈ univ.filter (fun p : ι × ι => p.1 < p.2), phi M π p.1 p.2

omit [Fintype ι] [LinearOrder ι] in
theorem phi_symm (M : Matrix ι ι ℝ) (π : ι → ℝ) (i j : ι) :
    phi M π i j = phi M π j i := by
  unfold phi J
  rw [show (π j * M j i) / (π i * M i j) = ((π i * M i j) / (π j * M j i))⁻¹ from
    (inv_div _ _).symm, Real.log_inv]
  ring

theorem sigmaOrdered_eq_two_mul (M : Matrix ι ι ℝ) (π : ι → ℝ) :
    sigmaOrdered M π = 2 * sigmaUnordered M π := by
  unfold sigmaOrdered sigmaUnordered
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hsplit : ∀ i j : ι, (if i ≠ j then phi M π i j else 0) =
      (if i < j then phi M π i j else 0) + (if j < i then phi M π j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le, phi_symm M π i j]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if j < i then phi M π j i else 0)]
  ring

theorem term_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a - b) * Real.log (a / b) := by
  rw [Real.log_div ha.ne' hb.ne']
  rcases le_total a b with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith)
      (by linarith [Real.log_le_log ha h])
  · exact mul_nonneg (by linarith) (by linarith [Real.log_le_log hb h])

theorem term_eq_zero_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) * Real.log (a / b) = 0 ↔ a = b := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · linarith
    · rcases Real.log_eq_zero.mp h1 with h2 | h2 | h2
      · exact absurd h2 (div_pos ha hb).ne'
      · exact (div_eq_one_iff_eq hb.ne').mp h2
      · exact absurd h2 (by linarith [div_pos ha hb])
  · intro h
    subst h
    simp

omit [Fintype ι] [LinearOrder ι] in
theorem phi_nonneg (M : Matrix ι ι ℝ) (π : ι → ℝ)
    (hM : ∀ i j, i ≠ j → 0 < M i j) (hπ : ∀ i, 0 < π i) {i j : ι} (hij : i ≠ j) :
    0 ≤ phi M π i j :=
  term_nonneg (mul_pos (hπ i) (hM i j hij)) (mul_pos (hπ j) (hM j i hij.symm))

theorem sigmaOrdered_nonneg (M : Matrix ι ι ℝ) (π : ι → ℝ)
    (hM : ∀ i j, i ≠ j → 0 < M i j) (hπ : ∀ i, 0 < π i) :
    0 ≤ sigmaOrdered M π := by
  unfold sigmaOrdered
  refine Finset.sum_nonneg fun p hp => ?_
  exact phi_nonneg M π hM hπ (Finset.mem_filter.mp hp).2

theorem sigmaUnordered_nonneg (M : Matrix ι ι ℝ) (π : ι → ℝ)
    (hM : ∀ i j, i ≠ j → 0 < M i j) (hπ : ∀ i, 0 < π i) :
    0 ≤ sigmaUnordered M π := by
  unfold sigmaUnordered
  refine Finset.sum_nonneg fun p hp => ?_
  exact phi_nonneg M π hM hπ (Finset.mem_filter.mp hp).2.ne

theorem sigmaOrdered_eq_zero_iff (M : Matrix ι ι ℝ) (π : ι → ℝ)
    (hM : ∀ i j, i ≠ j → 0 < M i j) (hπ : ∀ i, 0 < π i) :
    sigmaOrdered M π = 0 ↔ ∀ i j, i ≠ j → π i * M i j = π j * M j i := by
  unfold sigmaOrdered
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun p hp => phi_nonneg M π hM hπ (Finset.mem_filter.mp hp).2)]
  constructor
  · intro h i j hij
    have := h (i, j) (by simp [hij])
    exact (term_eq_zero_iff (mul_pos (hπ i) (hM i j hij))
      (mul_pos (hπ j) (hM j i hij.symm))).mp this
  · intro h p hp
    have hij := (Finset.mem_filter.mp hp).2
    exact (term_eq_zero_iff (mul_pos (hπ p.1) (hM p.1 p.2 hij))
      (mul_pos (hπ p.2) (hM p.2 p.1 (Ne.symm hij)))).mpr (h p.1 p.2 hij)

end EntropyProductionOrderedPairs
