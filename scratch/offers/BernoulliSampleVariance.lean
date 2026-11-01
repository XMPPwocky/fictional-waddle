import Mathlib

/-!
# Bernoulli sampling variance and shot-noise floor

Setting: the finite product space `Fin n → Bool` with product weight
`mu n p ω = ∏ i, (if ω i then p else 1 - p)`, the expectation
`E n p f = ∑ ω, mu n p ω * f ω`, and the sample mean
`phat n ω = (1/n) * ∑ i, [ω i]` where `[b] = 1` if `b` and `0` otherwise.

PROVED
* `moment` : for every real `p` and every finite set `s` of coordinates,
  `E[∏ i ∈ s, X_i] = p ^ |s|` (the coordinates are independent Bernoulli(p)).
* `sum_mu_eq_one` : (1) the weights sum to one, `∑ ω, mu n p ω = 1` (any real `p`).
* `mu_nonneg` : for `p ∈ [0,1]`, every weight is nonnegative, so `mu` is a probability
  mass function.
* `E_ind`, `ind_mul_self`, `E_ind_mul` : `E[X_i] = p`, `X_i^2 = X_i`, and
  `E[X_i X_j] = p` if `i = j`, `p^2` otherwise.
* `expectation_phat` : (2) for `n ≥ 1`, `E[phat] = p` (any real `p`).
* `variance_phat` : (3) for `n ≥ 1`, `Var(phat) = E[(phat - E phat)^2] = p(1-p)/n`
  (any real `p`).
* `sqrt_variance_le` : (4) for `n ≥ 1`, `sqrt(Var(phat)) ≤ 1/(2 sqrt n)` (any real `p`,
  since `p(1-p) ≤ 1/4` always).
* `chebyshev` : (5) for `n ≥ 1`, `p ∈ [0,1]`, `e > 0`,
  `P(|phat - p| ≥ e) ≤ p(1-p)/(n e^2)`, where `P(A) = ∑ ω, if A ω then mu ω else 0`.
-/

namespace BernoulliSampleVariance

open Finset

/-- Weight of one coordinate: `p` for `true`, `1 - p` for `false`. -/
noncomputable def w (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- Indicator of a Boolean outcome as a real number. -/
def ind (b : Bool) : ℝ := if b then 1 else 0

/-- Product weight on `Fin n → Bool`. -/
noncomputable def mu (n : ℕ) (p : ℝ) (ω : Fin n → Bool) : ℝ := ∏ i, w p (ω i)

/-- Expectation with respect to `mu`. -/
noncomputable def E (n : ℕ) (p : ℝ) (f : (Fin n → Bool) → ℝ) : ℝ := ∑ ω, mu n p ω * f ω

/-- Sample mean of the `n` coordinates. -/
noncomputable def phat (n : ℕ) (ω : Fin n → Bool) : ℝ := (1 / (n : ℝ)) * ∑ i, ind (ω i)

/-- Variance of the sample mean. -/
noncomputable def var (n : ℕ) (p : ℝ) : ℝ :=
  E n p (fun ω => (phat n ω - E n p (phat n)) ^ 2)

/-- Probability that the sample mean deviates from `p` by at least `e`. -/
noncomputable def probDev (n : ℕ) (p e : ℝ) : ℝ :=
  ∑ ω, if e ≤ |phat n ω - p| then mu n p ω else 0

theorem moment (n : ℕ) (p : ℝ) (s : Finset (Fin n)) :
    ∑ ω : Fin n → Bool, mu n p ω * ∏ i ∈ s, ind (ω i) = p ^ s.card := by
  have h1 : ∀ ω : Fin n → Bool, mu n p ω * ∏ i ∈ s, ind (ω i)
      = ∏ i, (w p (ω i) * (if i ∈ s then ind (ω i) else 1)) := by
    intro ω
    rw [Finset.prod_mul_distrib, mu, Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i b => w p b * (if i ∈ s then ind b else 1))]
  have h2 : ∀ i : Fin n, ∑ b : Bool, w p b * (if i ∈ s then ind b else 1)
      = if i ∈ s then p else 1 := by
    intro i
    split_ifs <;> simp [w, ind]
  simp_rw [h2]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

theorem sum_mu_eq_one (n : ℕ) (p : ℝ) : ∑ ω : Fin n → Bool, mu n p ω = 1 := by
  have := moment n p ∅
  simpa using this

theorem mu_nonneg (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : Fin n → Bool) :
    0 ≤ mu n p ω := by
  apply Finset.prod_nonneg
  intro i _
  unfold w
  split_ifs <;> linarith

theorem E_ind (n : ℕ) (p : ℝ) (i : Fin n) :
    ∑ ω : Fin n → Bool, mu n p ω * ind (ω i) = p := by
  have := moment n p {i}
  simpa using this

theorem ind_mul_self (b : Bool) : ind b * ind b = ind b := by
  cases b <;> simp [ind]

theorem E_ind_mul (n : ℕ) (p : ℝ) (i j : Fin n) :
    ∑ ω : Fin n → Bool, mu n p ω * (ind (ω i) * ind (ω j))
      = if i = j then p else p ^ 2 := by
  split_ifs with h
  · subst h
    simp_rw [ind_mul_self]
    exact E_ind n p i
  · have := moment n p {i, j}
    rw [Finset.card_pair h] at this
    simpa [Finset.prod_pair h] using this

theorem expectation_phat (n : ℕ) (hn : 1 ≤ n) (p : ℝ) : E n p (phat n) = p := by
  have hn' : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold E phat
  have : ∀ ω : Fin n → Bool, mu n p ω * (1 / (n : ℝ) * ∑ i, ind (ω i))
      = 1 / (n : ℝ) * ∑ i, mu n p ω * ind (ω i) := by
    intro ω
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [this]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [E_ind]
  simp
  field_simp

theorem variance_phat (n : ℕ) (hn : 1 ≤ n) (p : ℝ) : var n p = p * (1 - p) / n := by
  have hn' : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold var
  rw [expectation_phat n hn p]
  unfold E
  have hpt : ∀ ω : Fin n → Bool, mu n p ω * (phat n ω - p) ^ 2
      = (1 / (n : ℝ)) ^ 2 * ∑ i, ∑ j,
          (mu n p ω * (ind (ω i) * ind (ω j)) - p * (mu n p ω * ind (ω i))
            - p * (mu n p ω * ind (ω j)) + p ^ 2 * mu n p ω) := by
    intro ω
    have hd : phat n ω - p = (1 / (n : ℝ)) * ∑ i, (ind (ω i) - p) := by
      unfold phat
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    rw [hd, mul_pow, pow_two (∑ i : Fin n, (ind (ω i) - p)), Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  simp_rw [hpt]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hinner : ∀ i : Fin n, ∑ ω : Fin n → Bool, ∑ j,
      (mu n p ω * (ind (ω i) * ind (ω j)) - p * (mu n p ω * ind (ω i))
        - p * (mu n p ω * ind (ω j)) + p ^ 2 * mu n p ω)
      = ∑ j, (if i = j then p - p ^ 2 else 0) := by
    intro i
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      E_ind_mul, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, E_ind, E_ind,
      sum_mu_eq_one]
    split_ifs <;> ring
  simp_rw [hinner]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem sqrt_variance_le (n : ℕ) (hn : 1 ≤ n) (p : ℝ) :
    Real.sqrt (var n p) ≤ 1 / (2 * Real.sqrt n) := by
  have hnpos : (0 : ℝ) < n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  rw [variance_phat n hn p, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [div_pow, mul_pow, Real.sq_sqrt hnpos.le, div_le_div_iff₀ hnpos (by positivity)]
  nlinarith [sq_nonneg (2 * p - 1)]

theorem chebyshev (n : ℕ) (hn : 1 ≤ n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {e : ℝ} (he : 0 < e) :
    probDev n p e ≤ p * (1 - p) / (n * e ^ 2) := by
  have hvar := variance_phat n hn p
  unfold var at hvar
  rw [expectation_phat n hn p] at hvar
  unfold E at hvar
  have he2 : 0 < e ^ 2 := by positivity
  have hbound : probDev n p e ≤ ∑ ω, mu n p ω * (phat n ω - p) ^ 2 / e ^ 2 := by
    unfold probDev
    refine Finset.sum_le_sum (fun ω _ => ?_)
    have hm := mu_nonneg n hp0 hp1 ω
    split_ifs with h
    · rw [le_div_iff₀ he2]
      have : e ^ 2 ≤ (phat n ω - p) ^ 2 := by
        rw [← sq_abs (phat n ω - p)]
        exact pow_le_pow_left₀ he.le h 2
      nlinarith
    · positivity
  rw [← Finset.sum_div, hvar] at hbound
  rw [div_div] at hbound
  exact hbound

end BernoulliSampleVariance
