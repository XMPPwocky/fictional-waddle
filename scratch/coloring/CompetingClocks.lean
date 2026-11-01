import Mathlib

/-!
# Competing clocks: which of two independent searches succeeds first

Two independent searches run in discrete steps `k = 0, 1, 2, ...`. On each step search `W`
succeeds with probability `p` and search `S` with probability `q`, independently across steps
and of each other, with `0 < p ≤ 1` and `0 < q ≤ 1`. Write `a = (1 - p) * (1 - q)` for the
probability that both fail on a given step.

INTERPRETED: by independence, the probability that the first success of `W` is at step `k` and
`S` has not succeeded at steps `0, ..., k` is `a ^ k * (p * (1 - q))`; the probability that `W`
first succeeds at step `k` and `S` has not succeeded at steps `0, ..., k - 1` is `a ^ k * p`.
The events for different `k` are disjoint, so the probabilities in question are the sums of
these series over `k`. The theorems below are statements about these series (`HasSum`), not
about an explicitly constructed measure on sequences of outcomes. The continuous version is
stated as the integral `∫₀^∞ λ e^{-λt} e^{-μt} dt`, the density of the first exponential clock
times the survival function of the second.

PROVED:
* `both_fail_lt_one`: `0 ≤ a < 1`, so the series converge.
* `hasSum_W_strictly_first`: `∑ₖ a^k p (1-q) = p (1-q) / (1 - a)`, the probability that `W`
  succeeds strictly before `S`.
* `hasSum_S_strictly_first`: `∑ₖ a^k q (1-p) = q (1-p) / (1 - a)`, the same for `S`.
* `hasSum_tie`: `∑ₖ a^k p q = p q / (1 - a)`, the probability that both first succeed on the
  same step.
* `hasSum_W_no_later`: `∑ₖ a^k p = p / (1 - a)`, the probability that `W` succeeds no later
  than `S`.
* `W_no_later_eq_first_add_tie`: no-later = strictly-first + tie.
* `outcomes_sum_to_one`: strictly-W-first + strictly-S-first + tie = 1 (someone eventually
  succeeds almost surely).
* `W_first_more_likely_iff`: `W` is strictly more likely than `S` to succeed strictly first
  iff `q < p`.
* `W_first_more_likely_of_lt`: the corollary, if `q < p` then `W` is more likely to be found
  strictly first.
* `W_first_sub_S_first`: the difference of the two strictly-first probabilities is
  `(p - q) / (1 - a)`.
* `integral_exponential_race`: for rates `λ, μ > 0`,
  `∫_{t > 0} λ e^{-λt} e^{-μt} dt = λ / (λ + μ)`, the probability that an exponential clock of
  rate `λ` rings before an independent one of rate `μ`.
* `tendsto_discrete_to_exponential`: with `p = λ h`, `q = μ h`, the discrete strictly-first
  probability tends to `λ / (λ + μ)` as `h → 0⁺`.
-/

namespace CompetingClocks

open Filter Topology MeasureTheory Set

/-- Probability that `W` succeeds strictly before `S`. -/
noncomputable def pFirst (p q : ℝ) : ℝ := p * (1 - q) / (1 - (1 - p) * (1 - q))

/-- Probability that `W` succeeds no later than `S`. -/
noncomputable def pNoLater (p q : ℝ) : ℝ := p / (1 - (1 - p) * (1 - q))

/-- Probability that both first succeed on the same step. -/
noncomputable def pTie (p q : ℝ) : ℝ := p * q / (1 - (1 - p) * (1 - q))

variable {p q : ℝ}

theorem both_fail_nonneg (hp1 : p ≤ 1) (hq1 : q ≤ 1) : 0 ≤ (1 - p) * (1 - q) :=
  mul_nonneg (by linarith) (by linarith)

theorem both_fail_lt_one (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    0 ≤ (1 - p) * (1 - q) ∧ (1 - p) * (1 - q) < 1 := by
  refine ⟨both_fail_nonneg hp1 hq1, ?_⟩
  have h1 : (1 - p) * (1 - q) ≤ 1 - p :=
    mul_le_of_le_one_right (by linarith) (by linarith)
  linarith

theorem one_sub_both_fail_pos (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    0 < 1 - (1 - p) * (1 - q) := by
  have := (both_fail_lt_one hp hp1 hq hq1).2
  linarith

theorem hasSum_geom_mul (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) (c : ℝ) :
    HasSum (fun k : ℕ => ((1 - p) * (1 - q)) ^ k * c) (c / (1 - (1 - p) * (1 - q))) := by
  obtain ⟨h0, h1⟩ := both_fail_lt_one hp hp1 hq hq1
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_right c
  convert h using 1
  rw [div_eq_mul_inv, mul_comm]

/-- `W` strictly first: `∑ₖ ((1-p)(1-q))^k · p · (1-q) = p(1-q) / (1 - (1-p)(1-q))`. -/
theorem hasSum_W_strictly_first (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    HasSum (fun k : ℕ => (1 - p) ^ k * (1 - q) ^ k * p * (1 - q)) (pFirst p q) := by
  have h := hasSum_geom_mul hp hp1 hq hq1 (p * (1 - q))
  unfold pFirst
  convert h using 1
  funext k
  rw [mul_pow]; ring

/-- `S` strictly first. -/
theorem hasSum_S_strictly_first (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    HasSum (fun k : ℕ => (1 - p) ^ k * (1 - q) ^ k * q * (1 - p)) (pFirst q p) := by
  have h := hasSum_geom_mul hp hp1 hq hq1 (q * (1 - p))
  unfold pFirst
  rw [mul_comm (1 - q) (1 - p)]
  convert h using 1
  funext k
  rw [mul_pow]; ring

/-- Both first succeed on the same step. -/
theorem hasSum_tie (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    HasSum (fun k : ℕ => (1 - p) ^ k * (1 - q) ^ k * p * q) (pTie p q) := by
  have h := hasSum_geom_mul hp hp1 hq hq1 (p * q)
  unfold pTie
  convert h using 1
  funext k
  rw [mul_pow]; ring

/-- `W` no later than `S`: `∑ₖ ((1-p)(1-q))^k · p = p / (1 - (1-p)(1-q))`. -/
theorem hasSum_W_no_later (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    HasSum (fun k : ℕ => (1 - p) ^ k * (1 - q) ^ k * p) (pNoLater p q) := by
  have h := hasSum_geom_mul hp hp1 hq hq1 p
  unfold pNoLater
  convert h using 1
  funext k
  rw [mul_pow]

theorem W_no_later_eq_first_add_tie (p q : ℝ) : pNoLater p q = pFirst p q + pTie p q := by
  unfold pNoLater pFirst pTie
  rw [← add_div]; ring_nf

theorem outcomes_sum_to_one (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    pFirst p q + pFirst q p + pTie p q = 1 := by
  have hd := one_sub_both_fail_pos hp hp1 hq hq1
  unfold pFirst pTie
  rw [mul_comm (1 - q) (1 - p), ← add_div, ← add_div,
    div_eq_one_iff_eq hd.ne']
  ring

theorem W_first_sub_S_first (p q : ℝ) :
    pFirst p q - pFirst q p = (p - q) / (1 - (1 - p) * (1 - q)) := by
  unfold pFirst
  rw [mul_comm (1 - q) (1 - p), ← sub_div]; ring_nf

theorem W_first_more_likely_iff (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    pFirst q p < pFirst p q ↔ q < p := by
  have hd := one_sub_both_fail_pos hp hp1 hq hq1
  rw [← sub_pos, W_first_sub_S_first, div_pos_iff_of_pos_right hd, sub_pos]

/-- Corollary: if `p > q` then `W` is more likely than `S` to be found strictly first. -/
theorem W_first_more_likely_of_lt (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1)
    (hpq : q < p) : pFirst q p < pFirst p q :=
  (W_first_more_likely_iff hp hp1 hq hq1).2 hpq

/-- Exponential race: `∫_{t>0} λ e^{-λt} e^{-μt} dt = λ / (λ + μ)`. -/
theorem integral_exponential_race {l m : ℝ} (hl : 0 < l) (hm : 0 < m) :
    ∫ t in Ioi (0 : ℝ), l * Real.exp (-l * t) * Real.exp (-m * t) = l / (l + m) := by
  have hs : -(l + m) < 0 := by linarith
  have h : ∀ t : ℝ, l * Real.exp (-l * t) * Real.exp (-m * t)
      = l * Real.exp (-(l + m) * t) := by
    intro t
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  simp_rw [h]
  rw [integral_const_mul, integral_exp_mul_Ioi hs]
  have : l + m ≠ 0 := by linarith
  field_simp
  simp

/-- Discrete-to-continuous limit: with `p = λh`, `q = μh`, the strictly-first probability
tends to `λ / (λ + μ)` as `h → 0⁺`. -/
theorem tendsto_discrete_to_exponential {l m : ℝ} (hl : 0 < l) (hm : 0 < m) :
    Tendsto (fun h : ℝ => pFirst (l * h) (m * h)) (𝓝[>] 0) (𝓝 (l / (l + m))) := by
  have hlm : l + m ≠ 0 := by linarith
  have key : ∀ h : ℝ, 0 < h →
      pFirst (l * h) (m * h) = l * (1 - m * h) / (l + m - l * m * h) := by
    intro h hh
    unfold pFirst
    have e : 1 - (1 - l * h) * (1 - m * h) = h * (l + m - l * m * h) := by ring
    rw [e, mul_comm l h, mul_assoc, mul_div_mul_left _ _ hh.ne']
  have hc : ContinuousAt (fun h : ℝ => l * (1 - m * h) / (l + m - l * m * h)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using hlm
  have h0 : l * (1 - m * 0) / (l + m - l * m * 0) = l / (l + m) := by simp
  have ht := hc.tendsto
  rw [h0] at ht
  refine (ht.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (key h hh).symm

end CompetingClocks
