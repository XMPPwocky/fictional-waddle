import Mathlib

/-!
# Reading a temperature off a two-state Gibbs policy

Setting: two states with energies `0` (state `false`) and `Δ > 0` (state `true`), temperature
`T > 0`. The Gibbs probability of the higher state is
`p Δ T = exp (-Δ/T) / (1 + exp (-Δ/T))`, which equals `1 / (1 + exp (Δ/T))` (`p_eq`).

PROVED
* `p_eq` : `p Δ T = 1 / (1 + exp (Δ / T))`, for all real `Δ, T`.
* (1) `single_sample_nonidentifiable` : for `T₁ ≠ T₂` (both positive) and any rule
  `r : Bool → ℝ`, there is a state `o` with positive probability under both temperatures such that
  `r o ≠ T₁ ∨ r o ≠ T₂` (it cannot equal both). Strengthening `every_state_ambiguous`: every state
  has positive probability under both temperatures. Corollary `single_sample_error_pos`: the error
  probability `P_{T₁}(r ≠ T₁)` or `P_{T₂}(r ≠ T₂)` is strictly positive.
* (2) `p_pos`, `p_lt_half`, `p_strictMonoOn` : `0 < p Δ T < 1/2` for `T > 0`, and
  `T ↦ p Δ T` is strictly increasing on `(0, ∞)`.
* (3) `temperature_from_p` : `T = Δ / log ((1 - p) / p)` with `p = p Δ T`;
  `p_injOn` : `T ↦ p Δ T` is injective on `(0, ∞)`; `pInv_leftInvOn` : `pInv Δ q = Δ / log((1-q)/q)`
  is an explicit left inverse on `(0, ∞)`.
* (4) `binomial_mean_freq` : for `N ≥ 1` and any real `q`,
  `Σ_{k=0}^{N} C(N,k) q^k (1-q)^(N-k) · (k/N) = q`;
  `binomial_var_freq` : `Σ_{k=0}^{N} C(N,k) q^k (1-q)^(N-k) · (k/N - q)^2 = q (1 - q) / N`.
  Specialisations `freq_unbiased`, `freq_variance` at `q = p Δ T`.

INTERPRETED
* An observed state is a `Bool` (`true` = the higher-energy state). The single-sample law under
  temperature `T` is `stateProb Δ T : Bool → ℝ`, `true ↦ p`, `false ↦ 1 - p`.
* "r is wrong with positive probability under T₁ or under T₂" is formalised twice: as the existence
  of a state with positive probability under both on which `r` misses at least one of `T₁, T₂`, and
  as positivity of `Σ_o stateProb T_i o · [r o ≠ T_i]` for some `i`.
* Expectation and variance of `k/N` for `k ~ Binomial(N, p)` are stated as the explicit finite sums
  over `k ∈ {0, …, N}` with binomial weights, as in the target.
-/

namespace OwnTemperatureA

open Real Finset

/-- Gibbs probability of the higher-energy state (energy `Δ`) at temperature `T`. -/
noncomputable def p (Δ T : ℝ) : ℝ := Real.exp (-Δ / T) / (1 + Real.exp (-Δ / T))

/-- Single-sample law: `true` is the higher state. -/
noncomputable def stateProb (Δ T : ℝ) : Bool → ℝ
  | true => p Δ T
  | false => 1 - p Δ T

/-- Explicit inverse of `T ↦ p Δ T`. -/
noncomputable def pInv (Δ q : ℝ) : ℝ := Δ / Real.log ((1 - q) / q)

theorem p_eq (Δ T : ℝ) : p Δ T = 1 / (1 + Real.exp (Δ / T)) := by
  unfold p
  have h2 : 0 < Real.exp (Δ / T) := Real.exp_pos _
  rw [neg_div, Real.exp_neg]
  field_simp
  ring

theorem p_pos (Δ T : ℝ) : 0 < p Δ T := by
  rw [p_eq]; have := Real.exp_pos (Δ / T); positivity

theorem p_lt_one (Δ T : ℝ) : p Δ T < 1 := by
  rw [p_eq]
  have := Real.exp_pos (Δ / T)
  rw [div_lt_one (by linarith)]; linarith

theorem p_lt_half {Δ T : ℝ} (hΔ : 0 < Δ) (hT : 0 < T) : p Δ T < 1 / 2 := by
  rw [p_eq]
  have h : 1 < Real.exp (Δ / T) := Real.one_lt_exp_iff.mpr (div_pos hΔ hT)
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith

theorem p_strictMonoOn {Δ : ℝ} (hΔ : 0 < Δ) : StrictMonoOn (p Δ) (Set.Ioi 0) := by
  intro T₁ hT₁ T₂ hT₂ hlt
  simp only [Set.mem_Ioi] at hT₁ hT₂
  rw [p_eq, p_eq]
  have hd : Δ / T₂ < Δ / T₁ := div_lt_div_of_pos_left hΔ hT₁ hlt
  have he : Real.exp (Δ / T₂) < Real.exp (Δ / T₁) := Real.exp_lt_exp.mpr hd
  have h0 := Real.exp_pos (Δ / T₂)
  apply one_div_lt_one_div_of_lt (by linarith); linarith

theorem stateProb_pos (Δ T : ℝ) (o : Bool) : 0 < stateProb Δ T o := by
  cases o
  · simp [stateProb]; exact p_lt_one Δ T
  · simp [stateProb]; exact p_pos Δ T

/-- Every state has positive probability under both temperatures, and no single value of the rule
can equal two distinct temperatures. -/
theorem every_state_ambiguous (Δ : ℝ) {T₁ T₂ : ℝ} (hne : T₁ ≠ T₂) (r : Bool → ℝ) (o : Bool) :
    0 < stateProb Δ T₁ o ∧ 0 < stateProb Δ T₂ o ∧ (r o ≠ T₁ ∨ r o ≠ T₂) := by
  refine ⟨stateProb_pos _ _ _, stateProb_pos _ _ _, ?_⟩
  by_contra h
  push Not at h
  exact hne (h.1.symm.trans h.2)

/-- (1) Single-sample non-identifiability. -/
theorem single_sample_nonidentifiable {Δ : ℝ} (_hΔ : 0 < Δ) {T₁ T₂ : ℝ} (_h₁ : 0 < T₁)
    (_h₂ : 0 < T₂) (hne : T₁ ≠ T₂) (r : Bool → ℝ) :
    ∃ o : Bool, 0 < stateProb Δ T₁ o ∧ 0 < stateProb Δ T₂ o ∧ (r o ≠ T₁ ∨ r o ≠ T₂) :=
  ⟨true, every_state_ambiguous Δ hne r true⟩

/-- (1), error-probability form: under `T₁` or under `T₂`, the rule reports the wrong temperature
with strictly positive probability. -/
theorem single_sample_error_pos {Δ : ℝ} (hΔ : 0 < Δ) {T₁ T₂ : ℝ} (h₁ : 0 < T₁) (h₂ : 0 < T₂)
    (hne : T₁ ≠ T₂) (r : Bool → ℝ) :
    0 < ∑ o : Bool, stateProb Δ T₁ o * (if r o ≠ T₁ then 1 else 0) ∨
      0 < ∑ o : Bool, stateProb Δ T₂ o * (if r o ≠ T₂ then 1 else 0) := by
  obtain ⟨o, hp₁, hp₂, hr⟩ := single_sample_nonidentifiable hΔ h₁ h₂ hne r
  have key : ∀ T : ℝ, r o ≠ T →
      0 < ∑ o' : Bool, stateProb Δ T o' * (if r o' ≠ T then 1 else 0) := by
    intro T hT
    have hnn : ∀ o' ∈ (Finset.univ : Finset Bool),
        0 ≤ stateProb Δ T o' * (if r o' ≠ T then 1 else 0) := by
      intro o' _
      have := (stateProb_pos Δ T o').le
      split_ifs <;> simp [this]
    have hpos : 0 < stateProb Δ T o * (if r o ≠ T then 1 else 0) := by
      rw [ite_eq_left_iff.mpr (fun h => absurd hT h), mul_one]; exact stateProb_pos Δ T o
    exact lt_of_lt_of_le hpos (Finset.single_le_sum hnn (Finset.mem_univ o))
  rcases hr with h | h
  · exact Or.inl (key T₁ h)
  · exact Or.inr (key T₂ h)

/-- (3) The temperature is recovered from `p` by `T = Δ / log ((1 - p) / p)`. -/
theorem temperature_from_p {Δ T : ℝ} (hΔ : 0 < Δ) (hT : 0 < T) :
    T = Δ / Real.log ((1 - p Δ T) / p Δ T) := by
  have hratio : (1 - p Δ T) / p Δ T = Real.exp (Δ / T) := by
    rw [p_eq]
    have := Real.exp_pos (Δ / T)
    field_simp
    ring
  rw [hratio, Real.log_exp]
  field_simp

theorem pInv_leftInvOn {Δ : ℝ} (hΔ : 0 < Δ) : Set.LeftInvOn (pInv Δ) (p Δ) (Set.Ioi 0) := by
  intro T hT
  exact (temperature_from_p hΔ hT).symm

/-- (3) `T ↦ p Δ T` is injective on `(0, ∞)`. -/
theorem p_injOn {Δ : ℝ} (hΔ : 0 < Δ) : Set.InjOn (p Δ) (Set.Ioi 0) :=
  (pInv_leftInvOn hΔ).injOn

/-- Binomial weight. -/
noncomputable def w (N k : ℕ) (q : ℝ) : ℝ := (N.choose k : ℝ) * q ^ k * (1 - q) ^ (N - k)

theorem sum_w (N : ℕ) (q : ℝ) : ∑ k ∈ range (N + 1), w N k q = 1 := by
  have := congrArg (Polynomial.eval q) (bernsteinPolynomial.sum ℝ N)
  simpa [Polynomial.eval_finsetSum, bernsteinPolynomial, w] using this

theorem sum_k_w (N : ℕ) (q : ℝ) : ∑ k ∈ range (N + 1), (k : ℝ) * w N k q = N * q := by
  have := congrArg (Polynomial.eval q) (bernsteinPolynomial.sum_smul ℝ N)
  simpa [Polynomial.eval_finsetSum, bernsteinPolynomial, w, nsmul_eq_mul, mul_assoc] using this

theorem sum_kk_w (N : ℕ) (q : ℝ) :
    ∑ k ∈ range (N + 1), ((k * (k - 1) : ℕ) : ℝ) * w N k q = ((N * (N - 1) : ℕ) : ℝ) * q ^ 2 := by
  have := congrArg (Polynomial.eval q) (bernsteinPolynomial.sum_mul_smul ℝ N)
  simp only [Polynomial.eval_finsetSum, nsmul_eq_mul, Polynomial.eval_mul,
    Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X] at this
  rw [← this]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [bernsteinPolynomial, w, mul_assoc]

theorem sum_ksq_w (N : ℕ) (q : ℝ) :
    ∑ k ∈ range (N + 1), (k : ℝ) ^ 2 * w N k q = ((N * (N - 1) : ℕ) : ℝ) * q ^ 2 + N * q := by
  rw [← sum_kk_w, ← sum_k_w, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ((k * (k - 1) : ℕ) : ℝ) + k = (k : ℝ) ^ 2 := by
    rcases k with _ | k
    · simp
    · push_cast [Nat.add_sub_cancel]; ring
  rw [← hk]; ring

/-- (4) Mean of the empirical frequency `k/N` under `Binomial(N, q)`. -/
theorem binomial_mean_freq {N : ℕ} (hN : 1 ≤ N) (q : ℝ) :
    ∑ k ∈ range (N + 1), (N.choose k : ℝ) * q ^ k * (1 - q) ^ (N - k) * ((k : ℝ) / N) = q := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have h := sum_k_w N q
  calc ∑ k ∈ range (N + 1), (N.choose k : ℝ) * q ^ k * (1 - q) ^ (N - k) * ((k : ℝ) / N)
      = (∑ k ∈ range (N + 1), (k : ℝ) * w N k q) / N := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [w]; ring
    _ = q := by rw [h]; field_simp

/-- (4) Variance of the empirical frequency `k/N` under `Binomial(N, q)`. -/
theorem binomial_var_freq {N : ℕ} (hN : 1 ≤ N) (q : ℝ) :
    ∑ k ∈ range (N + 1), (N.choose k : ℝ) * q ^ k * (1 - q) ^ (N - k) * ((k : ℝ) / N - q) ^ 2
      = q * (1 - q) / N := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hcast : ((N * (N - 1) : ℕ) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    push_cast [Nat.add_sub_cancel]; ring
  have expand : ∀ k ∈ range (N + 1),
      (N.choose k : ℝ) * q ^ k * (1 - q) ^ (N - k) * ((k : ℝ) / N - q) ^ 2
        = (1 / (N : ℝ) ^ 2) * ((k : ℝ) ^ 2 * w N k q) + (-2 * q / N) * ((k : ℝ) * w N k q)
          + q ^ 2 * w N k q := by
    intro k _
    simp only [w]; field_simp; ring
  rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, sum_ksq_w, sum_k_w, sum_w, hcast]
  field_simp
  ring

/-- (4) at the Gibbs probability: `k/N` is an unbiased estimator of `p Δ T`. -/
theorem freq_unbiased {N : ℕ} (hN : 1 ≤ N) (Δ T : ℝ) :
    ∑ k ∈ range (N + 1),
        (N.choose k : ℝ) * p Δ T ^ k * (1 - p Δ T) ^ (N - k) * ((k : ℝ) / N) = p Δ T :=
  binomial_mean_freq hN _

/-- (4) at the Gibbs probability: variance `p (1 - p) / N`. -/
theorem freq_variance {N : ℕ} (hN : 1 ≤ N) (Δ T : ℝ) :
    ∑ k ∈ range (N + 1),
        (N.choose k : ℝ) * p Δ T ^ k * (1 - p Δ T) ^ (N - k) * ((k : ℝ) / N - p Δ T) ^ 2
      = p Δ T * (1 - p Δ T) / N :=
  binomial_var_freq hN _

end OwnTemperatureA
