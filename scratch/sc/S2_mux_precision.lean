import Mathlib

/-!
# S2: MUX scaled addition and stochastic-stream precision

(1) MUX. A 2:1 multiplexer `out = if s then a else b` with a select bit `s`
independent of the data pair `(a, b)` and `P(s = 1) = t` computes the scaled sum
`P(out = 1) = t * P(a = 1) + (1 - t) * P(b = 1)`; with `t = 1/2` this is
`(P(a=1) + P(b=1)) / 2`. The model is a finite joint mass function
`J : Bool → Bool → Bool → ℝ` (indices `s a b`), total mass 1, independence stated as
"joint = product of the `s`-marginal and the `(a,b)`-marginal". No nonnegativity is
needed for the identity, so none is assumed.

(2) Precision. For `n ≥ 1` independent `{0,1}`-valued random variables with
`P(X i = 1) = p`, the empirical mean `(∑ i, X i) / n` has expectation `p`,
variance `p (1 - p) / n`, and satisfies Chebyshev:
`P(|mean - p| ≥ ε) ≤ p (1 - p) / (n ε²)`.
-/

open MeasureTheory ProbabilityTheory

namespace S2

/-- The 2:1 multiplexer on bits. -/
def mux (s a b : Bool) : Bool := if s then a else b

/-- Indicator of a Bool as a real. -/
def ind (x : Bool) : ℝ := if x then 1 else 0

/-- Probability that a Bool-valued function of `(s,a,b)` is true, under mass `J`. -/
noncomputable def probOf (J : Bool → Bool → Bool → ℝ) (f : Bool → Bool → Bool → Bool) : ℝ :=
  ∑ s, ∑ a, ∑ b, J s a b * ind (f s a b)

/-- `s`-marginal. -/
noncomputable def margS (J : Bool → Bool → Bool → ℝ) (s : Bool) : ℝ := ∑ a, ∑ b, J s a b

/-- `(a,b)`-marginal. -/
noncomputable def margAB (J : Bool → Bool → Bool → ℝ) (a b : Bool) : ℝ := ∑ s, J s a b

/-- PROVED (finite model): MUX with select probability `t` computes
`t * P(a) + (1 - t) * P(b)`. -/
theorem mux_weighted (J : Bool → Bool → Bool → ℝ) (t : ℝ)
    (hsum : ∑ s, ∑ a, ∑ b, J s a b = 1)
    (hind : ∀ s a b, J s a b = margS J s * margAB J a b)
    (ht : margS J true = t) :
    probOf J (fun s a b => mux s a b)
      = t * probOf J (fun _ a _ => a) + (1 - t) * probOf J (fun _ _ b => b) := by
  obtain ⟨P, hP⟩ : ∃ P : Bool → ℝ, ∀ s, margS J s = P s := ⟨_, fun _ => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Bool → Bool → ℝ, ∀ a b, margAB J a b = M a b := ⟨_, fun _ _ => rfl⟩
  have key : ∀ s a b, J s a b = P s * M a b := fun s a b => by rw [hind, hP, hM]
  have h1 : P true + P false = 1 := by
    rw [← hP, ← hP]
    simp only [margS]
    rw [Fintype.sum_bool] at hsum
    exact hsum
  have ht' : P true = t := by rw [← hP]; exact ht
  have hf : P false = 1 - t := by linarith
  simp only [probOf, key, mux, ind, Fintype.sum_bool]
  rw [ht', hf]
  simp
  ring

/-- PROVED (finite model): fair-select MUX is scaled addition,
`P(out=1) = (P(a=1) + P(b=1)) / 2`. -/
theorem mux_scaled_addition (J : Bool → Bool → Bool → ℝ)
    (hsum : ∑ s, ∑ a, ∑ b, J s a b = 1)
    (hind : ∀ s a b, J s a b = margS J s * margAB J a b)
    (hhalf : margS J true = 1 / 2) :
    probOf J (fun s a b => mux s a b)
      = (probOf J (fun _ a _ => a) + probOf J (fun _ _ b => b)) / 2 := by
  rw [mux_weighted J (1 / 2) hsum hind hhalf]
  ring

section Precision

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} {X : Fin n → Ω → ℝ} {p : ℝ}

/-- Each `{0,1}`-valued measurable variable is in `L²`. -/
lemma memLp_bit (hmeas : ∀ i, Measurable (X i)) (hbit : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (i : Fin n) : MemLp (X i) 2 μ :=
  MemLp.of_bound (hmeas i).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by rcases hbit i ω with h | h <;> simp [h])

omit [IsProbabilityMeasure μ] in
/-- A Bernoulli(p) bit has expectation `p`. -/
lemma integral_bit (hmeas : ∀ i, Measurable (X i)) (hbit : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hp : ∀ i, μ.real {ω | X i ω = 1} = p) (i : Fin n) : μ[X i] = p := by
  have hs : MeasurableSet {ω | X i ω = 1} := hmeas i (measurableSet_singleton 1)
  have hpt : ∀ ω, X i ω = Set.indicator {ω | X i ω = 1} 1 ω := by
    intro ω; rcases hbit i ω with h | h <;> simp [Set.indicator, h]
  have : ∫ ω, X i ω ∂μ = ∫ ω, Set.indicator {ω | X i ω = 1} 1 ω ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [this, integral_indicator_one hs, hp i]

/-- A Bernoulli(p) bit has variance `p (1 - p)` (uses `X² = X` for bits). -/
lemma variance_bit (hmeas : ∀ i, Measurable (X i)) (hbit : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hp : ∀ i, μ.real {ω | X i ω = 1} = p) (i : Fin n) : Var[X i; μ] = p * (1 - p) := by
  have hsq : μ[X i ^ 2] = μ[X i] := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    rcases hbit i ω with h | h <;> simp [h]
  rw [variance_eq_sub (memLp_bit hmeas hbit i), hsq, integral_bit hmeas hbit hp i]
  ring

/-- PROVED: the empirical mean of Bernoulli(p) bits has expectation `p`
(independence not needed). -/
theorem mean_expectation (hn : 0 < n) (hmeas : ∀ i, Measurable (X i))
    (hbit : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hp : ∀ i, μ.real {ω | X i ω = 1} = p) :
    μ[fun ω => (∑ i, X i ω) / n] = p := by
  rw [integral_div, integral_finsetSum _ (fun i _ => (memLp_bit hmeas hbit i).integrable one_le_two)]
  simp only [integral_bit hmeas hbit hp, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- PROVED: the empirical mean of `n` independent Bernoulli(p) bits has variance
`p (1 - p) / n`. -/
theorem mean_variance (hn : 0 < n) (hmeas : ∀ i, Measurable (X i))
    (hbit : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hp : ∀ i, μ.real {ω | X i ω = 1} = p)
    (hindep : iIndepFun X μ) :
    Var[fun ω => (∑ i, X i ω) / n; μ] = p * (1 - p) / n := by
  have hfun : (fun ω => (∑ i, X i ω) / n) = fun ω => (1 / (n : ℝ)) * (∑ i, X i) ω := by
    funext ω; simp only [Finset.sum_apply]; ring
  rw [hfun, variance_const_mul,
    IndepFun.variance_sum (fun i _ => memLp_bit hmeas hbit i)
      (fun i _ j _ hij => hindep.indepFun hij)]
  simp only [variance_bit hmeas hbit hp, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- PROVED: Chebyshev precision bound for the stochastic stream,
`P(|mean - p| ≥ ε) ≤ p (1 - p) / (n ε²)`. -/
theorem mean_chebyshev (hn : 0 < n) (hmeas : ∀ i, Measurable (X i))
    (hbit : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hp : ∀ i, μ.real {ω | X i ω = 1} = p)
    (hindep : iIndepFun X μ) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |(∑ i, X i ω) / n - p|} ≤ ENNReal.ofReal (p * (1 - p) / (n * ε ^ 2)) := by
  have hY : MemLp (fun ω => (∑ i, X i ω) / n) 2 μ := by
    have hfun : (fun ω => (∑ i, X i ω) / n) = fun ω => (1 / (n : ℝ)) * (∑ i, X i ω) := by
      funext ω; ring
    rw [hfun]
    exact (memLp_finsetSum _ (fun i _ => memLp_bit hmeas hbit i)).const_mul _
  have h := meas_ge_le_variance_div_sq hY hε
  rw [mean_expectation hn hmeas hbit hp, mean_variance hn hmeas hbit hp hindep] at h
  exact h.trans_eq (by rw [div_div])

/-- PROVED (new, "down" corollary of `mean_chebyshev`): a stream length sufficient for
precision `ε` at confidence `1 - δ`, uniformly in the unknown `p`. If `1 ≤ 4 n ε² δ`
(i.e. `n ≥ 1 / (4 δ ε²)`), then `P(|mean - p| ≥ ε) ≤ δ`. Uses `p (1 - p) ≤ 1/4`,
which holds for every real `p`. -/
theorem mean_sample_size (hn : 0 < n) (hmeas : ∀ i, Measurable (X i))
    (hbit : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hp : ∀ i, μ.real {ω | X i ω = 1} = p)
    (hindep : iIndepFun X μ) {ε δ : ℝ} (hε : 0 < ε) (hN : 1 ≤ 4 * n * ε ^ 2 * δ) :
    μ {ω | ε ≤ |(∑ i, X i ω) / n - p|} ≤ ENNReal.ofReal δ := by
  refine (mean_chebyshev hn hmeas hbit hp hindep hε).trans (ENNReal.ofReal_le_ofReal ?_)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) * ε ^ 2 := by positivity
  rw [div_le_iff₀ hd]
  nlinarith [sq_nonneg (p - 1 / 2)]

end Precision

/-! ## Concrete instances (fidelity / non-vacuity checks) -/

/-- Concrete MUX instance: fair select, `P(a=1) = 0.3` and `P(b=1) = 0.9` with `a, b`
correlated (`P(a=1,b=1) = 0.25`); the joint is `J s a b = 1/2 * q a b`. The hypotheses of
`mux_scaled_addition` hold and the output probability is `0.6 = (0.3 + 0.9)/2`. -/
noncomputable def qAB (a b : Bool) : ℝ :=
  match a, b with
  | true, true => 1/4 | true, false => 1/20 | false, true => 13/20 | false, false => 1/20

noncomputable def Jex (_s a b : Bool) : ℝ := 1/2 * qAB a b

example : probOf Jex (fun s a b => mux s a b) = 3/5 := by
  have h := mux_scaled_addition Jex
    (by simp [Jex, qAB]; norm_num)
    (fun s a b => by cases s <;> cases a <;> cases b <;>
      simp [Jex, qAB, margS, margAB] <;> norm_num)
    (by simp [margS, Jex, qAB]; norm_num)
  rw [h]
  simp [probOf, Jex, qAB, ind]; norm_num

/-- A fair coin on `Bool`. -/
noncomputable def coin : Measure Bool :=
  (1/2 : ENNReal) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure coin := ⟨by simp [coin]; exact ENNReal.inv_two_add_inv_two⟩

/-- The `i`-th coordinate of a stream of `n` fair coins, as a real bit. -/
noncomputable def coinBit (n : ℕ) (i : Fin n) (ω : Fin n → Bool) : ℝ := if ω i then 1 else 0

lemma coinBit_meas (n : ℕ) (i : Fin n) : Measurable (coinBit n i) := measurable_of_finite _

lemma coinBit_bit (n : ℕ) (i : Fin n) (ω : Fin n → Bool) : coinBit n i ω = 0 ∨ coinBit n i ω = 1 := by
  unfold coinBit; split_ifs <;> simp

lemma coinBit_indep (n : ℕ) : iIndepFun (coinBit n) (Measure.pi fun _ => coin) :=
  iIndepFun_pi (X := fun (_ : Fin n) (b : Bool) => if b then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

lemma coinBit_prob (n : ℕ) (i : Fin n) :
    (Measure.pi fun _ => coin).real {ω | coinBit n i ω = 1} = 1/2 := by
  have : {ω | coinBit n i ω = 1} = (fun ω : Fin n → Bool => ω i) ⁻¹' {true} := by
    ext ω; simp [coinBit]
  rw [this, measureReal_def, (measurePreserving_eval (fun _ => coin) i).measure_preimage
    (measurableSet_singleton _).nullMeasurableSet]
  simp [coin]

/-- Non-vacuity + concrete numbers: the precision hypotheses are satisfied by `n = 100`
genuinely independent fair coins (product measure), and Chebyshev gives
`P(|mean - 1/2| ≥ 1/10) ≤ 1/4`. -/
example : (Measure.pi fun _ => coin) {ω : Fin 100 → Bool |
    (1/10 : ℝ) ≤ |(∑ i, coinBit 100 i ω) / (100 : ℕ) - 1/2|} ≤ ENNReal.ofReal (1/4) := by
  have h := mean_chebyshev (by norm_num) (coinBit_meas 100) (coinBit_bit 100) (coinBit_prob 100)
    (coinBit_indep 100) (ε := 1/10) (by norm_num)
  refine h.trans_eq ?_
  norm_num

/-- Concrete use of `mean_sample_size`: `n = 2500` fair coins give precision `0.05` with
failure probability at most `δ = 0.04` (`4 · 2500 · 0.05² · 0.04 = 1`). -/
example : (Measure.pi fun _ => coin) {ω : Fin 2500 → Bool |
    (1/20 : ℝ) ≤ |(∑ i, coinBit 2500 i ω) / (2500 : ℕ) - 1/2|} ≤ ENNReal.ofReal (1/25) :=
  mean_sample_size (by norm_num) (coinBit_meas 2500) (coinBit_bit 2500) (coinBit_prob 2500)
    (coinBit_indep 2500) (by norm_num) (by norm_num)

end S2
