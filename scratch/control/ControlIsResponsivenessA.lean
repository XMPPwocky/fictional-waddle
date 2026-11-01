import Mathlib

/-!
# Control is responsiveness

PROVED
* `control_of_prediction`: for `f : X → Y` and `y ∈ Set.range f`, `∃ x, f x = y`.
* `producible_eq_range`: the set of producible outputs `{y | ∃ x, f x = y}` is `Set.range f`.
* `otp_prob_true`: with `Y = b xor c`, `c` a fair coin, `P(Y = true) = 1/2` for both `b`.
* `otp_dist_indep`: the distribution of `Y` given `b` is the same for both values of `b`.
* `otp_joint_indep`: for any prior on `b`, the joint law of `(b, Y)` factors as
  `P(b) · P(Y)` (zero mutual information).
* `shift_eq_sum`: the shift `|P_{x₁}(A) − P_{x₂}(A)|` equals `|Σ_{i∈A} (K x₁ i − K x₂ i)|`.
* `shift_le_tv`: that shift is at most `TV(K x₁, K x₂)`.
* `shift_eq_tv_at_pos`: equality for `A = {i | K x₁ i > K x₂ i}`.
* `tv_isGreatest_shift`: `TV(K x₁, K x₂)` is the maximum over `A` of the achievable shift.

INTERPRETED
* "An intervener that knows `f` and chooses the input can produce `y`" is `∃ x, f x = y`.
* The one-time pad is modelled by the explicit finite law
  `P(Y = y | b) = Σ_c (1/2) · [b xor c = y]`; independence of `b` and `c` is built in by
  the coin law not depending on `b`. "Zero information" is stated as equality of the
  conditional laws and, for any prior on `b`, factorisation of the joint law.
* A response kernel is `K : X → Fin m → ℝ` with each `K x` nonnegative and summing to `1`;
  `P_x(A) = Σ_{i∈A} K x i` for `A : Finset (Fin m)`.
-/

namespace ControlIsResponsivenessA

open Finset

/-! ## (1) Prediction plus intervention is control -/

theorem control_of_prediction {X Y : Type*} (f : X → Y) (y : Y) (hy : y ∈ Set.range f) :
    ∃ x, f x = y := hy

theorem producible_eq_range {X Y : Type*} (f : X → Y) :
    {y | ∃ x, f x = y} = Set.range f := rfl

/-! ## (2) One-time pad -/

/-- Law of the private fair coin. -/
noncomputable def coin : Bool → ℝ := fun _ => 1 / 2

/-- Law of the output `Y = b xor c` given the intervener's choice `b`. -/
noncomputable def outDist (b : Bool) (y : Bool) : ℝ :=
  ∑ c : Bool, coin c * (if xor b c = y then 1 else 0)

theorem outDist_eq_half (b y : Bool) : outDist b y = 1 / 2 := by
  cases b <;> cases y <;> simp [outDist, coin]

theorem otp_prob_true (b : Bool) : outDist b true = 1 / 2 := outDist_eq_half b true

theorem otp_dist_indep (b₁ b₂ : Bool) : outDist b₁ = outDist b₂ := by
  funext y; rw [outDist_eq_half, outDist_eq_half]

/-- Marginal law of `Y` under a prior `pb` on the intervener's choice. -/
noncomputable def marginal (pb : Bool → ℝ) (y : Bool) : ℝ := ∑ b : Bool, pb b * outDist b y

theorem otp_joint_indep (pb : Bool → ℝ) (hpb : ∑ b : Bool, pb b = 1) (b y : Bool) :
    pb b * outDist b y = pb b * marginal pb y := by
  have : marginal pb y = 1 / 2 := by
    simp only [marginal, outDist_eq_half, ← Finset.sum_mul, hpb, one_mul]
  rw [this, outDist_eq_half]

/-! ## (3) Controllability equals responsiveness -/

/-- Total variation distance between two vectors on `Fin m`. -/
noncomputable def TV {m : ℕ} (p q : Fin m → ℝ) : ℝ := (1 / 2) * ∑ i, |p i - q i|

/-- Probability of the output set `A` under `p`. -/
noncomputable def prob {m : ℕ} (p : Fin m → ℝ) (A : Finset (Fin m)) : ℝ := ∑ i ∈ A, p i

/-- `p` is a probability vector. -/
def IsProbVec {m : ℕ} (p : Fin m → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

lemma pos_part_eq (x : ℝ) : max x 0 = (|x| + x) / 2 := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h, abs_of_nonpos h]; ring

lemma sum_pos_part {m : ℕ} (d : Fin m → ℝ) (hd : ∑ i, d i = 0) :
    ∑ i, max (d i) 0 = (1 / 2) * ∑ i, |d i| := by
  simp only [pos_part_eq]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hd]; ring

lemma sum_le_half_abs {m : ℕ} (d : Fin m → ℝ) (hd : ∑ i, d i = 0) (A : Finset (Fin m)) :
    ∑ i ∈ A, d i ≤ (1 / 2) * ∑ i, |d i| := by
  rw [← sum_pos_part d hd]
  calc ∑ i ∈ A, d i ≤ ∑ i ∈ A, max (d i) 0 :=
        Finset.sum_le_sum fun i _ => le_max_left _ _
    _ ≤ ∑ i, max (d i) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
          fun i _ _ => le_max_right _ _

theorem shift_eq_sum {X : Type*} {m : ℕ} (K : X → Fin m → ℝ) (x₁ x₂ : X)
    (A : Finset (Fin m)) :
    |prob (K x₁) A - prob (K x₂) A| = |∑ i ∈ A, (K x₁ i - K x₂ i)| := by
  rw [prob, prob, Finset.sum_sub_distrib]

theorem shift_le_tv {X : Type*} [Fintype X] {m : ℕ} (K : X → Fin m → ℝ)
    (hK : ∀ x, IsProbVec (K x)) (x₁ x₂ : X) (A : Finset (Fin m)) :
    |∑ i ∈ A, (K x₁ i - K x₂ i)| ≤ TV (K x₁) (K x₂) := by
  have hd : ∑ i, (K x₁ i - K x₂ i) = 0 := by
    rw [Finset.sum_sub_distrib, (hK x₁).2, (hK x₂).2, sub_self]
  have hd' : ∑ i, (-(K x₁ i - K x₂ i)) = 0 := by
    rw [Finset.sum_neg_distrib, hd, neg_zero]
  rw [TV, abs_le]
  constructor
  · have h := sum_le_half_abs (fun i => -(K x₁ i - K x₂ i)) hd' A
    simp only [abs_neg, Finset.sum_neg_distrib] at h
    linarith
  · exact sum_le_half_abs (fun i => K x₁ i - K x₂ i) hd A

theorem shift_eq_tv_at_pos {X : Type*} [Fintype X] {m : ℕ} (K : X → Fin m → ℝ)
    (hK : ∀ x, IsProbVec (K x)) (x₁ x₂ : X) :
    |∑ i ∈ Finset.univ.filter (fun i => K x₁ i > K x₂ i), (K x₁ i - K x₂ i)|
      = TV (K x₁) (K x₂) := by
  have hd : ∑ i, (K x₁ i - K x₂ i) = 0 := by
    rw [Finset.sum_sub_distrib, (hK x₁).2, (hK x₂).2, sub_self]
  have key : ∑ i ∈ Finset.univ.filter (fun i => K x₁ i > K x₂ i), (K x₁ i - K x₂ i)
      = ∑ i, max (K x₁ i - K x₂ i) 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rw [max_eq_left (by linarith)]
    · rw [max_eq_right (by linarith)]
  rw [key, sum_pos_part _ hd, TV]
  exact abs_of_nonneg
    (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => abs_nonneg _))

theorem tv_isGreatest_shift {X : Type*} [Fintype X] {m : ℕ} (K : X → Fin m → ℝ)
    (hK : ∀ x, IsProbVec (K x)) (x₁ x₂ : X) :
    IsGreatest {s | ∃ A : Finset (Fin m), s = |prob (K x₁) A - prob (K x₂) A|}
      (TV (K x₁) (K x₂)) := by
  refine ⟨⟨Finset.univ.filter (fun i => K x₁ i > K x₂ i), ?_⟩, ?_⟩
  · rw [shift_eq_sum, shift_eq_tv_at_pos K hK]
  · rintro s ⟨A, rfl⟩
    rw [shift_eq_sum]
    exact shift_le_tv K hK x₁ x₂ A

end ControlIsResponsivenessA
