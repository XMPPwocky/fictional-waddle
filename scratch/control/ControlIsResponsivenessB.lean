import Mathlib

/-!
# Control is responsiveness

PROVED
* `exists_input_of_mem_range`, `producible_eq_range`: an intervener that knows the response
  function `f : X → Y` and chooses the input can produce exactly the outputs in `Set.range f`.
* `otp_prob_true`: for `Y = b xor c` with `c` a fair private coin (finite-sum model, weight `1/2`
  on each value of `c`), `P(Y = true) = 1/2` for both choices of `b`.
* `otp_dist_indep`: the output distribution of `Y` is the same function for `b = false` and
  `b = true`, hence for any two choices of `b`.
* `otp_measure_eq_uniform`, `otp_measure_prob_true`, `otp_measure_indep`: the same statements
  for measures: with `coinμ = Measure.uniformOfFinset univ` on `Bool`, the pushforward
  `coinμ.map (xor b ·)` equals `coinμ` for every `b`, and gives `{true}` mass `2⁻¹`.
* `shift_le_tv`: for a probability kernel `K : X → (Fin m → ℝ)`, any inputs `x₁ x₂` and any
  output set `A`, `|Σ_{i∈A} (K x₁ i − K x₂ i)| ≤ TV(K x₁, K x₂)`.
* `shift_eq_probDiff`: that quantity is `|P_{x₁}(A) − P_{x₂}(A)|`.
* `shift_eq_tv_at_pos`: equality holds for `A = {i | K x₁ i > K x₂ i}`.
* `tv_eq_max_shift`: TV is the maximum over all output sets of the achievable shift.

INTERPRETED
* "The intervener can move `P(output ∈ A)` by `δ`" is read as: choosing `x₁` instead of `x₂`
  changes `P(output ∈ A) = Σ_{i∈A} K x i` by exactly `δ` in absolute value.
* The private fair coin independent of `b` is modelled as the uniform distribution on `Bool`
  that does not depend on `b` (independence is built into the product/marginalization).
* Probability vectors are functions `Fin m → ℝ` with nonnegative entries summing to `1`.
  The finiteness hypothesis on `X` is carried but not needed.
-/

namespace ControlIsResponsivenessB

open Finset MeasureTheory

/-! ## (1) Prediction plus intervention is control -/

/-- The outputs an intervener who chooses the input can produce. -/
def producible {X Y : Type*} (f : X → Y) : Set Y := {y | ∃ x, f x = y}

theorem exists_input_of_mem_range {X Y : Type*} (f : X → Y) (y : Y) (hy : y ∈ Set.range f) :
    ∃ x, f x = y := hy

theorem producible_eq_range {X Y : Type*} (f : X → Y) : producible f = Set.range f := rfl

/-! ## (2) One-time pad -/

/-- The private fair coin. -/
noncomputable def coin : Bool → ℝ := fun _ => 1 / 2

/-- Distribution of `Y = b xor c` given the intervener's choice `b`. -/
noncomputable def otpDist (b : Bool) (y : Bool) : ℝ :=
  ∑ c : Bool, coin c * (if xor b c = y then 1 else 0)

theorem coin_isProb : (∀ c, 0 ≤ coin c) ∧ ∑ c : Bool, coin c = 1 := by
  refine ⟨fun _ => by norm_num [coin], ?_⟩
  norm_num [coin]

theorem otp_prob_true (b : Bool) : otpDist b true = 1 / 2 := by
  cases b <;> simp [otpDist, coin]

theorem otp_dist_eq_half (b y : Bool) : otpDist b y = 1 / 2 := by
  cases b <;> cases y <;> simp [otpDist, coin]

theorem otp_dist_indep (b₁ b₂ : Bool) : otpDist b₁ = otpDist b₂ := by
  funext y; rw [otp_dist_eq_half, otp_dist_eq_half]

theorem otp_zero_control : ∀ b : Bool, otpDist b true = 1 / 2 := otp_prob_true

theorem otp_zero_information : otpDist false = otpDist true := otp_dist_indep false true

/-- The private fair coin as a probability measure: uniform on `Bool`. -/
noncomputable def coinμ : Measure Bool := Measure.uniformOfFinset (Finset.univ : Finset Bool)

/-- Measure version: the law of `Y = b xor c` is uniform whatever `b` is. -/
theorem otp_measure_eq_uniform (b : Bool) :
    coinμ.map (fun c => xor b c) = coinμ := by
  have hb : (fun c : Bool => xor b c) = (if b then (fun c => !c) else id) := by
    funext c; cases b <;> cases c <;> rfl
  cases b
  · simp only [hb]; simp
  · rw [hb]
    simp only [coinμ, Measure.uniformOfFinset, Fintype.sum_bool, ite_true]
    rw [Measure.map_add _ _ (measurable_of_finite _), Measure.map_smul, Measure.map_smul,
      Measure.map_dirac' (measurable_of_finite _), Measure.map_dirac' (measurable_of_finite _)]
    · simp [add_comm]
    all_goals exact (measurable_of_finite _).aemeasurable

theorem otp_measure_prob_true (b : Bool) :
    (coinμ.map (fun c => xor b c)) {true} = 2⁻¹ := by
  rw [otp_measure_eq_uniform]; simp [coinμ]

theorem otp_measure_indep (b₁ b₂ : Bool) :
    coinμ.map (fun c => xor b₁ c) = coinμ.map (fun c => xor b₂ c) := by
  rw [otp_measure_eq_uniform, otp_measure_eq_uniform]

/-! ## (3) Controllability equals responsiveness -/

/-- Total variation distance between two vectors on `Fin m`. -/
noncomputable def TV {m : ℕ} (p q : Fin m → ℝ) : ℝ := (1 / 2) * ∑ i, |p i - q i|

/-- Probability vector. -/
def IsProb {m : ℕ} (p : Fin m → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- `P(output ∈ A)` under the probability vector `p`. -/
def probOf {m : ℕ} (p : Fin m → ℝ) (A : Finset (Fin m)) : ℝ := ∑ i ∈ A, p i

/-- The amount by which switching between `x₁` and `x₂` moves `P(output ∈ A)`. -/
noncomputable def shift {X : Type*} {m : ℕ} (K : X → Fin m → ℝ) (x₁ x₂ : X)
    (A : Finset (Fin m)) : ℝ :=
  |∑ i ∈ A, (K x₁ i - K x₂ i)|

theorem shift_eq_probDiff {X : Type*} {m : ℕ} (K : X → Fin m → ℝ) (x₁ x₂ : X)
    (A : Finset (Fin m)) :
    shift K x₁ x₂ A = |probOf (K x₁) A - probOf (K x₂) A| := by
  simp [shift, probOf, Finset.sum_sub_distrib]

lemma tv_eq_sum_pos {m : ℕ} (p q : Fin m → ℝ) (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) :
    TV p q = ∑ i, max (p i - q i) 0 := by
  have hd : ∑ i, (p i - q i) = 0 := by rw [Finset.sum_sub_distrib, hp, hq]; ring
  have habs : ∀ i, |p i - q i| = 2 * max (p i - q i) 0 - (p i - q i) := by
    intro i
    rcases le_total (p i - q i) 0 with h | h
    · rw [abs_of_nonpos h, max_eq_right h]; ring
    · rw [abs_of_nonneg h, max_eq_left h]; ring
  unfold TV
  simp_rw [habs]
  rw [Finset.sum_sub_distrib, hd, ← Finset.mul_sum]; ring

lemma sum_le_sum_pos {m : ℕ} (d : Fin m → ℝ) (A : Finset (Fin m)) :
    ∑ i ∈ A, d i ≤ ∑ i, max (d i) 0 := by
  calc ∑ i ∈ A, d i ≤ ∑ i ∈ A, max (d i) 0 :=
        Finset.sum_le_sum (fun i _ => le_max_left _ _)
    _ ≤ ∑ i, max (d i) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => le_max_right _ _)

theorem shift_le_tv {X : Type*} [Fintype X] {m : ℕ} (K : X → Fin m → ℝ)
    (hK : ∀ x, IsProb (K x)) (x₁ x₂ : X) (A : Finset (Fin m)) :
    shift K x₁ x₂ A ≤ TV (K x₁) (K x₂) := by
  rw [tv_eq_sum_pos _ _ (hK x₁).2 (hK x₂).2]
  set d : Fin m → ℝ := fun i => K x₁ i - K x₂ i with hd_def
  have hd0 : ∑ i, d i = 0 := by
    simp only [hd_def]; rw [Finset.sum_sub_distrib, (hK x₁).2, (hK x₂).2]; ring
  have hsplit : ∑ i ∈ A, d i + ∑ i ∈ Aᶜ, d i = 0 := by
    rw [Finset.sum_add_sum_compl, hd0]
  have h1 := sum_le_sum_pos d A
  have h2 := sum_le_sum_pos d Aᶜ
  unfold shift
  change |∑ i ∈ A, d i| ≤ ∑ i, max (d i) 0
  rw [abs_le]; constructor <;> linarith

theorem shift_eq_tv_at_pos {X : Type*} [Fintype X] {m : ℕ} (K : X → Fin m → ℝ)
    (hK : ∀ x, IsProb (K x)) (x₁ x₂ : X) :
    shift K x₁ x₂ (Finset.univ.filter (fun i => K x₁ i > K x₂ i)) = TV (K x₁) (K x₂) := by
  rw [tv_eq_sum_pos _ _ (hK x₁).2 (hK x₂).2]
  unfold shift
  rw [Finset.sum_filter]
  have hpt : ∀ i, (if K x₁ i > K x₂ i then K x₁ i - K x₂ i else 0) =
      max (K x₁ i - K x₂ i) 0 := by
    intro i
    split_ifs with h
    · rw [max_eq_left]; linarith
    · rw [max_eq_right]; linarith [not_lt.mp h]
  simp_rw [hpt]
  exact abs_of_nonneg (Finset.sum_nonneg (fun i _ => le_max_right _ _))

/-- TV is exactly the largest shift the intervener can produce on any event. -/
theorem tv_eq_max_shift {X : Type*} [Fintype X] {m : ℕ} (K : X → Fin m → ℝ)
    (hK : ∀ x, IsProb (K x)) (x₁ x₂ : X) :
    (∀ A, shift K x₁ x₂ A ≤ TV (K x₁) (K x₂)) ∧
      ∃ A, shift K x₁ x₂ A = TV (K x₁) (K x₂) :=
  ⟨shift_le_tv K hK x₁ x₂, ⟨_, shift_eq_tv_at_pos K hK x₁ x₂⟩⟩

end ControlIsResponsivenessB
