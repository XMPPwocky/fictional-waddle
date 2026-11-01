import Mathlib

/-!
# Frustration bound for pairwise correlations of unit vectors

PROVED (in a real inner product space `E`):
* `norm_sq_add_three` : for unit vectors `v₁ v₂ v₃`,
  `‖v₁ + v₂ + v₃‖² = 3 + 2 (⟪v₁,v₂⟫ + ⟪v₂,v₃⟫ + ⟪v₁,v₃⟫)`.
* `triangle_bound` : for unit vectors `v₁ v₂ v₃`,
  `⟪v₁,v₂⟫ + ⟪v₂,v₃⟫ + ⟪v₁,v₃⟫ ≥ -3/2`.
* `triangle_eq_iff` : equality `⟪v₁,v₂⟫ + ⟪v₂,v₃⟫ + ⟪v₁,v₃⟫ = -3/2` holds iff `v₁ + v₂ + v₃ = 0`.
* `sum_sum_symm_split` : for any symmetric `f : Fin n → Fin n → ℝ`,
  `∑ i, ∑ j, f i j = ∑ i, f i i + 2 ∑ i, ∑ j ∈ Ioi i, f i j`.
* `norm_sq_sum_eq` : for unit vectors `v : Fin n → E`,
  `‖∑ i, v i‖² = n + 2 ∑_{i<j} ⟪v i, v j⟫`.
* `pair_sum_bound` : for unit vectors `v : Fin n → E`, `∑_{i<j} ⟪v i, v j⟫ ≥ -n/2`
  (holds for every `n`, including `n = 0, 1`).
* `pair_sum_eq_iff` : `∑_{i<j} ⟪v i, v j⟫ = -n/2` iff `∑ i, v i = 0`.
* `num_pairs` : the number of pairs `i < j` in `Fin n` is `n(n-1)/2`.
* `mean_pair_bound` : for `n ≥ 2`, the mean `(∑_{i<j} ⟪v i, v j⟫) / (n(n-1)/2)` is `≥ -1/(n-1)`.
* `mean_pair_eq_iff` : for `n ≥ 2`, that mean equals `-1/(n-1)` iff `∑ i, v i = 0`.
* `triangle_not_all_neg_one` : no unit vectors `v₁ v₂ v₃` have all three edge inner products
  equal to `-1`.
* `edge_attains_neg_one` : for any unit vector `u`, the pair `u, -u` consists of unit vectors
  with `⟪u, -u⟫ = -1`.
-/

namespace TriangleFrustrationBound

open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

theorem norm_sq_add_three (v₁ v₂ v₃ : E) (h₁ : ‖v₁‖ = 1) (h₂ : ‖v₂‖ = 1) (h₃ : ‖v₃‖ = 1) :
    ‖v₁ + v₂ + v₃‖ ^ 2 = 3 + 2 * (⟪v₁, v₂⟫ + ⟪v₂, v₃⟫ + ⟪v₁, v₃⟫) := by
  rw [norm_add_sq_real, norm_add_sq_real, inner_add_left, h₁, h₂, h₃]
  ring

theorem triangle_bound (v₁ v₂ v₃ : E) (h₁ : ‖v₁‖ = 1) (h₂ : ‖v₂‖ = 1) (h₃ : ‖v₃‖ = 1) :
    -3 / 2 ≤ ⟪v₁, v₂⟫ + ⟪v₂, v₃⟫ + ⟪v₁, v₃⟫ := by
  have h := norm_sq_add_three v₁ v₂ v₃ h₁ h₂ h₃
  have : 0 ≤ ‖v₁ + v₂ + v₃‖ ^ 2 := sq_nonneg _
  linarith

theorem triangle_eq_iff (v₁ v₂ v₃ : E) (h₁ : ‖v₁‖ = 1) (h₂ : ‖v₂‖ = 1) (h₃ : ‖v₃‖ = 1) :
    ⟪v₁, v₂⟫ + ⟪v₂, v₃⟫ + ⟪v₁, v₃⟫ = -3 / 2 ↔ v₁ + v₂ + v₃ = 0 := by
  have h := norm_sq_add_three v₁ v₂ v₃ h₁ h₂ h₃
  constructor
  · intro he
    have : ‖v₁ + v₂ + v₃‖ ^ 2 = 0 := by rw [h, he]; ring
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  · intro hz
    rw [hz, norm_zero] at h
    linarith

theorem sum_sum_symm_split {n : ℕ} (f : Fin n → Fin n → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = ∑ i, f i i + 2 * ∑ i, ∑ j ∈ Ioi i, f i j := by
  have hsplit : ∀ i, ∑ j, f i j = ∑ j ∈ Iio i, f i j + f i i + ∑ j ∈ Ioi i, f i j := by
    intro i
    have hpt : ∀ j, f i j = (if j < i then f i j else 0) + (if i = j then f i j else 0)
        + (if i < j then f i j else 0) := by
      intro j
      rcases lt_trichotomy j i with h | h | h
      · simp [h, h.ne', not_lt.mpr h.le]
      · subst h; simp
      · simp [h, h.ne, not_lt.mpr h.le]
    rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq, ← Finset.sum_filter, ← Finset.sum_filter]
    simp only [Finset.mem_univ, ite_true]
    congr 2
    · congr 1; ext j; simp
    · ext j; simp
  have hcomm : ∑ i, ∑ j ∈ Iio i, f i j = ∑ j, ∑ i ∈ Ioi j, f i j :=
    Finset.sum_comm' (fun x y => by simp)
  have hcomm' : ∑ j, ∑ i ∈ Ioi j, f i j = ∑ i, ∑ j ∈ Ioi i, f i j := by
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => hf i j))
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, Finset.sum_add_distrib,
    hcomm, hcomm']
  ring

theorem norm_sq_sum_eq {n : ℕ} (v : Fin n → E) (hv : ∀ i, ‖v i‖ = 1) :
    ‖∑ i, v i‖ ^ 2 = n + 2 * ∑ i, ∑ j ∈ Ioi i, ⟪v i, v j⟫ := by
  have h1 : ‖∑ i, v i‖ ^ 2 = ∑ i, ∑ j, ⟪v i, v j⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    exact Finset.sum_congr rfl (fun i _ => inner_sum _ _ _)
  rw [h1, sum_sum_symm_split (fun i j => ⟪v i, v j⟫) (fun i j => real_inner_comm _ _)]
  have h2 : ∑ i, ⟪v i, v i⟫ = (n : ℝ) := by
    simp [hv]
  rw [h2]

theorem pair_sum_bound {n : ℕ} (v : Fin n → E) (hv : ∀ i, ‖v i‖ = 1) :
    -(n : ℝ) / 2 ≤ ∑ i, ∑ j ∈ Ioi i, ⟪v i, v j⟫ := by
  have h := norm_sq_sum_eq v hv
  have : 0 ≤ ‖∑ i, v i‖ ^ 2 := sq_nonneg _
  linarith

theorem pair_sum_eq_iff {n : ℕ} (v : Fin n → E) (hv : ∀ i, ‖v i‖ = 1) :
    ∑ i, ∑ j ∈ Ioi i, ⟪v i, v j⟫ = -(n : ℝ) / 2 ↔ ∑ i, v i = 0 := by
  have h := norm_sq_sum_eq v hv
  constructor
  · intro he
    have : ‖∑ i, v i‖ ^ 2 = 0 := by rw [h, he]; ring
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  · intro hz
    rw [hz, norm_zero] at h
    linarith

theorem num_pairs (n : ℕ) :
    (∑ i : Fin n, ((Ioi i).card : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  have h := sum_sum_symm_split (n := n) (fun _ _ => (1 : ℝ)) (fun _ _ => rfl)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have h' : ∑ i : Fin n, ((Ioi i).card : ℝ) = ∑ i : Fin n, ∑ j ∈ Ioi i, (1 : ℝ) := by
    simp
  rw [h']
  have : (n : ℝ) * n = n + 2 * ∑ i : Fin n, ∑ j ∈ Ioi i, (1 : ℝ) := by
    simpa using h
  linarith

theorem mean_pair_bound {n : ℕ} (hn : 2 ≤ n) (v : Fin n → E) (hv : ∀ i, ‖v i‖ = 1) :
    -1 / ((n : ℝ) - 1) ≤ (∑ i, ∑ j ∈ Ioi i, ⟪v i, v j⟫) / ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) * ((n : ℝ) - 1) / 2 := by nlinarith
  have hb := pair_sum_bound v hv
  have : -1 / ((n : ℝ) - 1) = (-(n : ℝ) / 2) / ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
    field_simp
  rw [this]
  exact div_le_div_of_nonneg_right hb hpos.le

theorem mean_pair_eq_iff {n : ℕ} (hn : 2 ≤ n) (v : Fin n → E) (hv : ∀ i, ‖v i‖ = 1) :
    (∑ i, ∑ j ∈ Ioi i, ⟪v i, v j⟫) / ((n : ℝ) * ((n : ℝ) - 1) / 2) = -1 / ((n : ℝ) - 1)
      ↔ ∑ i, v i = 0 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) * ((n : ℝ) - 1) / 2 := by nlinarith
  have : -1 / ((n : ℝ) - 1) = (-(n : ℝ) / 2) / ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
    field_simp
  rw [this, div_left_inj' hpos.ne', pair_sum_eq_iff v hv]

theorem triangle_not_all_neg_one (v₁ v₂ v₃ : E) (h₁ : ‖v₁‖ = 1) (h₂ : ‖v₂‖ = 1)
    (h₃ : ‖v₃‖ = 1) : ¬ (⟪v₁, v₂⟫ = -1 ∧ ⟪v₂, v₃⟫ = -1 ∧ ⟪v₁, v₃⟫ = -1) := by
  rintro ⟨a, b, c⟩
  have := triangle_bound v₁ v₂ v₃ h₁ h₂ h₃
  rw [a, b, c] at this
  norm_num at this

theorem edge_attains_neg_one (u : E) (hu : ‖u‖ = 1) :
    ‖u‖ = 1 ∧ ‖-u‖ = 1 ∧ ⟪u, -u⟫ = -1 := by
  refine ⟨hu, by rw [norm_neg, hu], ?_⟩
  rw [inner_neg_right, real_inner_self_eq_norm_sq, hu]
  norm_num

end TriangleFrustrationBound
