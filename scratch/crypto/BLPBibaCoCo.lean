/-
# Bell–LaPadula and Biba form a CoCo pair

Levels form a finite partial order L. Encode a flow policy as a real matrix: the Bell–LaPadula matrix
P has P a b = 1 when information may flow from level a to level b (a ≤ b) and 0 otherwise. Biba
allows exactly the reversed flows, so its matrix is the transpose Pᵀ.

PROVED
1. `biba_is_transpose`: the Biba flow matrix (1 when b ≤ a) is Pᵀ.
2. `coco_of_policies`: with S = (P + Pᵀ)/2 and K = (P − Pᵀ)/2 (the CoCo cooperative and competitive
   parts of the pair (P, Pᵀ)), P = S + K, Pᵀ = S − K, S is symmetric and K is antisymmetric.
3. `coco_policies_unique`: S and K are the only symmetric and antisymmetric matrices with P = S + K.
4. `shared_eq_one_iff`: S a b = 1 exactly when a = b, i.e. when both policies allow the flow. The
   cooperative part is isolation.
5. `shared_eq_zero_iff`: S a b = 0 exactly when a and b are incomparable: neither policy allows the
   flow either way.
6. `conflict_pos_iff`, `conflict_neg_iff`: K a b = 1/2 exactly when a < b, and −1/2 exactly when
   b < a. The competitive part records only the direction, and the two policies disagree on it.
7. `isolation_is_hadamard`: allowed by both (the entrywise product P ⊙ Pᵀ) is the identity matrix.

INTERPRETED (not formalized)
- Ordering by secrecy gives "no read up, no write down"; reversing the order (transposing) gives
  "no write up, no read down". The two policies share their symmetric part, which is isolation, and
  differ only by the sign of the antisymmetric part, which is the direction of allowed flow.
-/

import Mathlib

namespace BLPBibaCoCo

open Matrix

variable {L : Type*} [Fintype L] [DecidableEq L] [PartialOrder L] [DecidableRel (α := L) (· ≤ ·)]

/-- Bell–LaPadula flow matrix: 1 when information may flow from a to b. -/
def blp : Matrix L L ℝ := fun a b => if a ≤ b then 1 else 0

/-- Biba flow matrix. -/
def biba : Matrix L L ℝ := fun a b => if b ≤ a then 1 else 0

noncomputable def shared : Matrix L L ℝ := (1 / 2 : ℝ) • (blp + blpᵀ)
noncomputable def conflict : Matrix L L ℝ := (1 / 2 : ℝ) • (blp - blpᵀ)

theorem biba_is_transpose : (biba : Matrix L L ℝ) = blpᵀ := by
  ext a b; simp [biba, blp]

theorem coco_of_policies :
    (blp : Matrix L L ℝ) = shared + conflict ∧ (blpᵀ : Matrix L L ℝ) = shared - conflict ∧
      (shared : Matrix L L ℝ)ᵀ = shared ∧ (conflict : Matrix L L ℝ)ᵀ = -conflict := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext a b <;> simp [shared, conflict] <;> ring

theorem coco_policies_unique (S K : Matrix L L ℝ) (hS : Sᵀ = S) (hK : Kᵀ = -K)
    (h : (blp : Matrix L L ℝ) = S + K) : S = shared ∧ K = conflict := by
  have hT : (blpᵀ : Matrix L L ℝ) = S - K := by
    rw [h, transpose_add, hS, hK, sub_eq_add_neg]
  constructor
  · ext a b
    have h1 := congrFun (congrFun h a) b
    have h2 := congrFun (congrFun hT a) b
    simp only [Matrix.add_apply, Matrix.sub_apply] at h1 h2
    simp only [shared, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    rw [h1, h2]; ring
  · ext a b
    have h1 := congrFun (congrFun h a) b
    have h2 := congrFun (congrFun hT a) b
    simp only [Matrix.add_apply, Matrix.sub_apply] at h1 h2
    simp only [conflict, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    rw [h1, h2]; ring

theorem shared_apply (a b : L) :
    (shared : Matrix L L ℝ) a b = (1 / 2) * ((if a ≤ b then 1 else 0) + (if b ≤ a then 1 else 0)) := by
  simp [shared, blp]

theorem conflict_apply (a b : L) :
    (conflict : Matrix L L ℝ) a b = (1 / 2) * ((if a ≤ b then 1 else 0) - (if b ≤ a then 1 else 0)) := by
  simp [conflict, blp]

theorem shared_eq_one_iff (a b : L) : (shared : Matrix L L ℝ) a b = 1 ↔ a = b := by
  rw [shared_apply]
  constructor
  · intro h
    by_cases h1 : a ≤ b <;> by_cases h2 : b ≤ a <;> simp only [h1, h2, if_true, if_false] at h
    · exact le_antisymm h1 h2
    all_goals norm_num at h
  · rintro rfl; simp; norm_num

theorem shared_eq_zero_iff (a b : L) : (shared : Matrix L L ℝ) a b = 0 ↔ ¬ a ≤ b ∧ ¬ b ≤ a := by
  rw [shared_apply]
  by_cases h1 : a ≤ b <;> by_cases h2 : b ≤ a <;> simp [h1, h2]

theorem conflict_pos_iff (a b : L) : (conflict : Matrix L L ℝ) a b = 1 / 2 ↔ a < b := by
  rw [conflict_apply, lt_iff_le_not_ge]
  by_cases h1 : a ≤ b <;> by_cases h2 : b ≤ a <;> simp [h1, h2] <;> norm_num

theorem conflict_neg_iff (a b : L) : (conflict : Matrix L L ℝ) a b = -(1 / 2) ↔ b < a := by
  rw [conflict_apply, lt_iff_le_not_ge]
  by_cases h1 : a ≤ b <;> by_cases h2 : b ≤ a <;> simp [h1, h2]
  all_goals norm_num

theorem isolation_is_hadamard : (blp : Matrix L L ℝ) ⊙ blpᵀ = 1 := by
  ext a b
  simp only [hadamard, transpose_apply, blp, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · by_cases h1 : a ≤ b <;> by_cases h2 : b ≤ a <;> simp [h1, h2, h]
    exact h (le_antisymm h1 h2)

/-- Non-vacuity: on `Bool` (false < true) the two levels are comparable and distinct. -/
theorem example_bool :
    (conflict : Matrix Bool Bool ℝ) false true = 1 / 2 ∧ (shared : Matrix Bool Bool ℝ) false false = 1 := by
  constructor
  · exact (conflict_pos_iff false true).mpr (by decide)
  · exact (shared_eq_one_iff false false).mpr rfl

end BLPBibaCoCo

#print axioms BLPBibaCoCo.biba_is_transpose
#print axioms BLPBibaCoCo.coco_of_policies
#print axioms BLPBibaCoCo.coco_policies_unique
#print axioms BLPBibaCoCo.shared_eq_one_iff
#print axioms BLPBibaCoCo.shared_eq_zero_iff
#print axioms BLPBibaCoCo.conflict_pos_iff
#print axioms BLPBibaCoCo.conflict_neg_iff
#print axioms BLPBibaCoCo.isolation_is_hadamard
#print axioms BLPBibaCoCo.example_bool
