import Mathlib

/-!
# Reading a temperature off a two-state Gibbs policy

Two states with energies `0` and `Δ`; at temperature `T` the higher state has probability
`pHigh Δ T = e^(-Δ/T) / (1 + e^(-Δ/T))`.

PROVED
* `pHigh_eq` : `pHigh Δ T = 1 / (1 + e^(Δ/T))`.
* `single_sample_nonidentifiable` : for `T₁ ≠ T₂` and any rule `r : Bool → ℝ`, there is a
  state `o` with positive probability under both temperatures and `r o ≠ T₁ ∨ r o ≠ T₂`
  (in fact every state qualifies: `single_sample_nonidentifiable_forall`).
* `single_sample_error_pos` : the probability that `r` misreports the temperature is positive
  under `T₁` or under `T₂`.
* `pHigh_pos`, `pHigh_lt_half` : `0 < pHigh Δ T < 1/2` for `Δ > 0`, `T > 0`.
* `pHigh_strictMonoOn` : `T ↦ pHigh Δ T` is strictly increasing on `(0, ∞)` for `Δ > 0`.
* `temperatureOf_pHigh` : `T = Δ / log ((1 - p) / p)` for `p = pHigh Δ T`.
* `pHigh_injOn` : `T ↦ pHigh Δ T` is injective on `(0, ∞)`; `temperatureOf Δ` is a left
  inverse on `(0, ∞)` (`temperatureOf_leftInvOn`).
* `binomial_mean_freq` : `∑ₖ C(N,k) p^k (1-p)^(N-k) · k/N = p` for `N > 0`, any real `p`.
* `binomial_var_freq` : `∑ₖ C(N,k) p^k (1-p)^(N-k) · (k/N - p)^2 = p(1-p)/N` for `N > 0`.
* `freq_unbiased_pHigh`, `freq_var_pHigh` : the same two facts at `p = pHigh Δ T`.

INTERPRETED
* An observation is a `Bool` (`true` = high-energy state); the single-sample law is `prob Δ T`.
* "Wrong with positive probability under T" is `0 < ∑ o, [r o ≠ T] · prob Δ T o`.
* The law of `k` high states among `N` independent samples is the binomial weight
  `C(N,k) p^k (1-p)^(N-k)` on `k ∈ {0, …, N}`; expectation and variance of `k/N` are the
  corresponding finite weighted sums.
-/

namespace OwnTemperatureB

open Real Finset

/-- Probability of the higher-energy state of a two-state Gibbs policy. -/
noncomputable def pHigh (Δ T : ℝ) : ℝ := Real.exp (-Δ / T) / (1 + Real.exp (-Δ / T))

/-- The single-observation law: `true` is the higher state. -/
noncomputable def prob (Δ T : ℝ) : Bool → ℝ := fun b => if b then pHigh Δ T else 1 - pHigh Δ T

/-- Explicit inverse: temperature recovered from the high-state probability. -/
noncomputable def temperatureOf (Δ p : ℝ) : ℝ := Δ / Real.log ((1 - p) / p)

theorem pHigh_eq (Δ T : ℝ) : pHigh Δ T = 1 / (1 + Real.exp (Δ / T)) := by
  unfold pHigh
  have h : Real.exp (-Δ / T) = (Real.exp (Δ / T))⁻¹ := by
    rw [neg_div, Real.exp_neg]
  have hp : 0 < Real.exp (Δ / T) := Real.exp_pos _
  rw [h]
  field_simp
  ring

theorem one_sub_pHigh (Δ T : ℝ) :
    1 - pHigh Δ T = Real.exp (Δ / T) / (1 + Real.exp (Δ / T)) := by
  rw [pHigh_eq]
  have hp : 0 < Real.exp (Δ / T) := Real.exp_pos _
  field_simp
  ring

theorem pHigh_pos' (Δ T : ℝ) : 0 < pHigh Δ T := by
  rw [pHigh_eq]; have := Real.exp_pos (Δ / T); positivity

theorem one_sub_pHigh_pos (Δ T : ℝ) : 0 < 1 - pHigh Δ T := by
  rw [one_sub_pHigh]; have := Real.exp_pos (Δ / T); positivity

theorem prob_pos (Δ T : ℝ) (o : Bool) : 0 < prob Δ T o := by
  cases o
  · exact one_sub_pHigh_pos Δ T
  · exact pHigh_pos' Δ T

/-- (1) Every observed state has positive probability under both temperatures, and no report
`r o` can equal both. -/
theorem single_sample_nonidentifiable_forall (Δ T₁ T₂ : ℝ) (h : T₁ ≠ T₂) (r : Bool → ℝ)
    (o : Bool) : 0 < prob Δ T₁ o ∧ 0 < prob Δ T₂ o ∧ (r o ≠ T₁ ∨ r o ≠ T₂) := by
  refine ⟨prob_pos _ _ _, prob_pos _ _ _, ?_⟩
  by_cases h1 : r o = T₁
  · right; rw [h1]; exact h
  · left; exact h1

/-- (1) Single-sample non-identifiability, as stated. -/
theorem single_sample_nonidentifiable (Δ T₁ T₂ : ℝ) (h : T₁ ≠ T₂) (r : Bool → ℝ) :
    ∃ o : Bool, 0 < prob Δ T₁ o ∧ 0 < prob Δ T₂ o ∧ (r o ≠ T₁ ∨ r o ≠ T₂) :=
  ⟨true, single_sample_nonidentifiable_forall Δ T₁ T₂ h r true⟩

/-- Error probability of the rule `r` when the true temperature is `T`. -/
noncomputable def errorProb (Δ T : ℝ) (r : Bool → ℝ) : ℝ :=
  ∑ o : Bool, if r o ≠ T then prob Δ T o else 0

theorem errorProb_pos_of (Δ T : ℝ) (r : Bool → ℝ) (o : Bool) (ho : r o ≠ T) :
    0 < errorProb Δ T r := by
  unfold errorProb
  have hnn : ∀ o' ∈ (Finset.univ : Finset Bool), 0 ≤ (if r o' ≠ T then prob Δ T o' else 0) := by
    intro o' _
    split_ifs
    · exact (prob_pos _ _ _).le
    · exact le_refl _
  have hle := Finset.single_le_sum hnn (Finset.mem_univ o)
  simp only [ho, ne_eq, not_false_eq_true, ite_true] at hle
  exact lt_of_lt_of_le (prob_pos _ _ _) hle

/-- (1) Any single-observation rule is wrong with positive probability under `T₁` or `T₂`. -/
theorem single_sample_error_pos (Δ T₁ T₂ : ℝ) (h : T₁ ≠ T₂) (r : Bool → ℝ) :
    0 < errorProb Δ T₁ r ∨ 0 < errorProb Δ T₂ r := by
  rcases (single_sample_nonidentifiable_forall Δ T₁ T₂ h r true).2.2 with h1 | h2
  · exact Or.inl (errorProb_pos_of Δ T₁ r true h1)
  · exact Or.inr (errorProb_pos_of Δ T₂ r true h2)

/-- (2) Positivity. -/
theorem pHigh_pos {Δ T : ℝ} (_hΔ : 0 < Δ) (_hT : 0 < T) : 0 < pHigh Δ T := pHigh_pos' Δ T

/-- (2) Strictly below one half. -/
theorem pHigh_lt_half {Δ T : ℝ} (hΔ : 0 < Δ) (hT : 0 < T) : pHigh Δ T < 1 / 2 := by
  rw [pHigh_eq]
  have h1 : 1 < Real.exp (Δ / T) := by
    simpa using Real.exp_lt_exp.mpr (div_pos hΔ hT)
  apply one_div_lt_one_div_of_lt (by norm_num)
  linarith

/-- (2) Strictly increasing in `T` on `(0, ∞)`. -/
theorem pHigh_strictMonoOn {Δ : ℝ} (hΔ : 0 < Δ) : StrictMonoOn (pHigh Δ) (Set.Ioi 0) := by
  intro T₁ hT₁ T₂ _ hlt
  simp only [Set.mem_Ioi] at hT₁
  rw [pHigh_eq, pHigh_eq]
  have hd : Δ / T₂ < Δ / T₁ := div_lt_div_of_pos_left hΔ hT₁ hlt
  have he : Real.exp (Δ / T₂) < Real.exp (Δ / T₁) := Real.exp_lt_exp.mpr hd
  have hpos : 0 < 1 + Real.exp (Δ / T₂) := by have := Real.exp_pos (Δ / T₂); linarith
  exact one_div_lt_one_div_of_lt hpos (by linarith)

theorem odds_pHigh (Δ T : ℝ) : (1 - pHigh Δ T) / pHigh Δ T = Real.exp (Δ / T) := by
  rw [one_sub_pHigh, pHigh_eq]
  have hp : 0 < Real.exp (Δ / T) := Real.exp_pos _
  field_simp

/-- (3) Explicit inversion: `T = Δ / log ((1 - p) / p)` at `p = pHigh Δ T`. -/
theorem temperatureOf_pHigh {Δ T : ℝ} (hΔ : 0 < Δ) (hT : 0 < T) :
    T = Δ / Real.log ((1 - pHigh Δ T) / pHigh Δ T) := by
  rw [odds_pHigh, Real.log_exp]
  field_simp

/-- (3) `temperatureOf Δ` is a left inverse of `pHigh Δ` on `(0, ∞)`. -/
theorem temperatureOf_leftInvOn {Δ : ℝ} (hΔ : 0 < Δ) :
    Set.LeftInvOn (temperatureOf Δ) (pHigh Δ) (Set.Ioi 0) := by
  intro T hT
  exact (temperatureOf_pHigh hΔ hT).symm

/-- (3) Identifiability from the distribution. -/
theorem pHigh_injOn {Δ : ℝ} (hΔ : 0 < Δ) : Set.InjOn (pHigh Δ) (Set.Ioi 0) :=
  (temperatureOf_leftInvOn hΔ).injOn

/-- Binomial weight. -/
noncomputable def binom (N : ℕ) (p : ℝ) (k : ℕ) : ℝ := (N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k)

theorem binom_eval (N : ℕ) (p : ℝ) (k : ℕ) :
    (bernsteinPolynomial ℝ N k).eval p = binom N p k := by
  simp [bernsteinPolynomial, binom]

theorem binom_sum (N : ℕ) (p : ℝ) : ∑ k ∈ range (N + 1), binom N p k = 1 := by
  have := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum ℝ N)
  rw [Polynomial.eval_finsetSum] at this
  simpa [binom_eval] using this

theorem binom_sum_mul (N : ℕ) (p : ℝ) :
    ∑ k ∈ range (N + 1), (k : ℝ) * binom N p k = N * p := by
  have := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum_smul ℝ N)
  rw [Polynomial.eval_finsetSum] at this
  simpa [binom_eval, nsmul_eq_mul] using this

theorem binom_sum_mul2 (N : ℕ) (p : ℝ) :
    ∑ k ∈ range (N + 1), ((k * (k - 1) : ℕ) : ℝ) * binom N p k
      = ((N * (N - 1) : ℕ) : ℝ) * p ^ 2 := by
  have := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum_mul_smul ℝ N)
  rw [Polynomial.eval_finsetSum] at this
  simp only [nsmul_eq_mul, Polynomial.eval_mul, Polynomial.eval_natCast, binom_eval,
    Polynomial.eval_pow, Polynomial.eval_X] at this
  exact this

theorem cast_sq_eq (k : ℕ) : (k : ℝ) ^ 2 = ((k * (k - 1) : ℕ) : ℝ) + k := by
  cases k with
  | zero => simp
  | succ n => simp only [Nat.add_sub_cancel]; push_cast; ring

/-- (4) The frequency `k/N` is unbiased: binomial mean of `k/N` equals `p`. -/
theorem binomial_mean_freq (N : ℕ) (hN : 0 < N) (p : ℝ) :
    ∑ k ∈ range (N + 1), (N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k) * ((k : ℝ) / N) = p := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h : ∀ k ∈ range (N + 1),
      (N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k) * ((k : ℝ) / N)
        = (1 / (N : ℝ)) * ((k : ℝ) * binom N p k) := by
    intro k _; unfold binom; field_simp
  rw [sum_congr rfl h, ← mul_sum, binom_sum_mul]
  field_simp

/-- (4) Variance of the frequency: `p (1 - p) / N`. -/
theorem binomial_var_freq (N : ℕ) (hN : 0 < N) (p : ℝ) :
    ∑ k ∈ range (N + 1), (N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k) * ((k : ℝ) / N - p) ^ 2
      = p * (1 - p) / N := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h : ∀ k ∈ range (N + 1),
      (N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k) * ((k : ℝ) / N - p) ^ 2
        = (1 / (N : ℝ) ^ 2) * (((k * (k - 1) : ℕ) : ℝ) * binom N p k)
          + ((1 / (N : ℝ) ^ 2 - 2 * p / N) * ((k : ℝ) * binom N p k)
          + p ^ 2 * binom N p k) := by
    intro k _
    have hk := cast_sq_eq k
    unfold binom
    have e : ((k : ℝ) / N - p) ^ 2 = (k : ℝ) ^ 2 / (N : ℝ) ^ 2 - 2 * p * k / N + p ^ 2 := by
      field_simp; ring
    rw [e, hk]
    field_simp
    ring
  rw [sum_congr rfl h, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
    binom_sum_mul2, binom_sum_mul, binom_sum]
  have hc : ((N * (N - 1) : ℕ) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN.ne'), Nat.cast_one]
  rw [hc]
  field_simp
  ring

/-- (4) at the Gibbs probability: unbiasedness. -/
theorem freq_unbiased_pHigh (Δ T : ℝ) (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ range (N + 1), (N.choose k : ℝ) * pHigh Δ T ^ k * (1 - pHigh Δ T) ^ (N - k)
      * ((k : ℝ) / N) = pHigh Δ T :=
  binomial_mean_freq N hN _

/-- (4) at the Gibbs probability: variance. -/
theorem freq_var_pHigh (Δ T : ℝ) (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ range (N + 1), (N.choose k : ℝ) * pHigh Δ T ^ k * (1 - pHigh Δ T) ^ (N - k)
      * ((k : ℝ) / N - pHigh Δ T) ^ 2 = pHigh Δ T * (1 - pHigh Δ T) / N :=
  binomial_var_freq N hN _

end OwnTemperatureB
