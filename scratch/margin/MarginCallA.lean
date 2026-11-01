import Mathlib

/-!
# MarginCallA: over-betting is ruinous for a log-utility bettor

Even-money bet (odds `b = 1`) won with probability `p ∈ (1/2, 1)`. Staking a fraction
`f ∈ [0,1)` of wealth gives expected log-growth
`g p f = p * log (1 + f) + (1 - p) * log (1 - f)`.

PROVED
* `kelly_mem`            : `f* = 2p - 1 ∈ [0,1)`.
* `kelly_isMaxOn`        : `g p` attains its maximum on `[0,1)` at `f* = 2p - 1`.
* `kelly_unique`         : for every `f ∈ [0,1)` with `f ≠ f*`, `g p f < g p f*` (strict, unique maximiser).
* `kelly_growth_pos`     : `0 < g p f*`.
* `growth_tendsto_atBot` : `Tendsto (g p) (𝓝[<] 1) atBot`.
* `exists_overbet_loses` : there is `f₀ ∈ (f*, 1)` with `g p f₀ < 0`.
* `eventually_overbet_loses` : the stronger filter form: `g p f < 0` for all `f < 1` close enough to `1`.
* `leverage_ruin`        : for `f ≥ 1` and initial wealth `W ≥ 0`, one loss leaves wealth `W * (1 - f) ≤ 0`;
                           in particular for `W = 1`, wealth `1 - f ≤ 0`.
* `leverage_ruin_prob_tendsto_one` : the real sequence `1 - p ^ n` tends to `1`.
                           (Only the limit is proved; no probability space is formalized. Reading
                           `1 - p ^ n` as the chance of at least one loss in `n` independent rounds,
                           and hence of ruin for `f ≥ 1`, is interpretation.)

INTERPRETED
A claim sized beyond its margin gets called: there is an optimal stake set by the edge
(`f* = 2p - 1`), staking beyond it lowers growth, staking nearly all of the margin makes growth
arbitrarily negative however good the edge, and staking beyond the margin (`f ≥ 1`) is wiped
out by a single loss, which eventually occurs with probability tending to one.
-/

namespace MarginCallA

open Real Filter Topology Set

/-- Expected log-growth of an even-money bet won with probability `p`, staking fraction `f`. -/
noncomputable def g (p f : ℝ) : ℝ := p * Real.log (1 + f) + (1 - p) * Real.log (1 - f)

/-- The Kelly fraction for an even-money bet. -/
def fstar (p : ℝ) : ℝ := 2 * p - 1

/-- Wealth after one round, starting from wealth `W`, staking fraction `f`, with outcome `win`. -/
def wealthAfter (W f : ℝ) (win : Bool) : ℝ := if win then W * (1 + f) else W * (1 - f)

theorem kelly_mem {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) : fstar p ∈ Ico (0 : ℝ) 1 := by
  unfold fstar; constructor <;> linarith

/-- Gibbs-type bound: `g p f - g p f* ≤ 0`, written out. -/
private lemma key_le {p f : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    g p f ≤ g p (fstar p) := by
  unfold g fstar
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < 1 - p := by linarith
  have h1 : 0 < (1 + f) / (2 * p) := by positivity
  have h2 : 0 < (1 - f) / (2 * (1 - p)) := div_pos (by linarith) (by linarith)
  have e1 : Real.log (1 + f) = Real.log ((1 + f) / (2 * p)) + Real.log (1 + (2 * p - 1)) := by
    rw [show 1 + (2 * p - 1) = 2 * p by ring, Real.log_div (by linarith) (by linarith)]; ring
  have e2 : Real.log (1 - f) = Real.log ((1 - f) / (2 * (1 - p))) + Real.log (1 - (2 * p - 1)) := by
    rw [show 1 - (2 * p - 1) = 2 * (1 - p) by ring, Real.log_div (by linarith) (by linarith)]; ring
  have l1 := Real.log_le_sub_one_of_pos h1
  have l2 := Real.log_le_sub_one_of_pos h2
  have c1 : p * ((1 + f) / (2 * p) - 1) = (1 + f) / 2 - p := by field_simp
  have c2 : (1 - p) * ((1 - f) / (2 * (1 - p)) - 1) = (1 - f) / 2 - (1 - p) := by
    field_simp
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left l1 hp0.le, mul_le_mul_of_nonneg_left l2 hq0.le]

theorem kelly_isMaxOn {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) :
    IsMaxOn (g p) (Ico (0 : ℝ) 1) (fstar p) := by
  intro f hf
  exact key_le hp1 hp2 hf.1 hf.2

theorem kelly_unique {p f : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) (hf : f ∈ Ico (0 : ℝ) 1)
    (hne : f ≠ fstar p) : g p f < g p (fstar p) := by
  obtain ⟨hf0, hf1⟩ := hf
  unfold g fstar
  unfold fstar at hne
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < 1 - p := by linarith
  have h1 : 0 < (1 + f) / (2 * p) := by positivity
  have h2 : 0 < (1 - f) / (2 * (1 - p)) := div_pos (by linarith) (by linarith)
  have hn1 : (1 + f) / (2 * p) ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq (by linarith)] at h
    exact hne (by linarith)
  have e1 : Real.log (1 + f) = Real.log ((1 + f) / (2 * p)) + Real.log (1 + (2 * p - 1)) := by
    rw [show 1 + (2 * p - 1) = 2 * p by ring, Real.log_div (by linarith) (by linarith)]; ring
  have e2 : Real.log (1 - f) = Real.log ((1 - f) / (2 * (1 - p))) + Real.log (1 - (2 * p - 1)) := by
    rw [show 1 - (2 * p - 1) = 2 * (1 - p) by ring, Real.log_div (by linarith) (by linarith)]; ring
  have l1 := Real.log_lt_sub_one_of_pos h1 hn1
  have l2 := Real.log_le_sub_one_of_pos h2
  have c1 : p * ((1 + f) / (2 * p) - 1) = (1 + f) / 2 - p := by field_simp
  have c2 : (1 - p) * ((1 - f) / (2 * (1 - p)) - 1) = (1 - f) / 2 - (1 - p) := by
    field_simp
  rw [e1, e2]
  nlinarith [mul_lt_mul_of_pos_left l1 hp0, mul_le_mul_of_nonneg_left l2 hq0.le]

theorem kelly_growth_pos {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) : 0 < g p (fstar p) := by
  have h0 : g p 0 = 0 := by simp [g]
  have hne : (0 : ℝ) ≠ fstar p := by unfold fstar; intro h; linarith
  have := kelly_unique hp1 hp2 (f := 0) ⟨le_refl _, by norm_num⟩ hne
  linarith

theorem growth_tendsto_atBot {p : ℝ} (hp2 : p < 1) :
    Tendsto (g p) (𝓝[<] (1 : ℝ)) atBot := by
  have hq0 : 0 < 1 - p := by linarith
  have hA : Tendsto (fun f : ℝ => p * Real.log (1 + f)) (𝓝[<] (1 : ℝ))
      (𝓝 (p * Real.log (1 + 1))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt (fun f : ℝ => p * Real.log (1 + f)) 1 := by
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.log (by fun_prop) (by norm_num)
    exact hc.tendsto
  have hsub : Tendsto (fun f : ℝ => 1 - f) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun f : ℝ => 1 - f) (𝓝 (1 : ℝ)) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · filter_upwards [self_mem_nhdsWithin] with f hf
      simp only [mem_Ioi, sub_pos]
      exact hf
  have hB : Tendsto (fun f : ℝ => (1 - p) * Real.log (1 - f)) (𝓝[<] (1 : ℝ)) atBot :=
    (Real.tendsto_log_nhdsGT_zero.comp hsub).const_mul_atBot hq0
  exact hA.add_atBot hB

theorem eventually_overbet_loses {p : ℝ} (hp2 : p < 1) :
    ∀ᶠ f in 𝓝[<] (1 : ℝ), g p f < 0 :=
  (growth_tendsto_atBot hp2).eventually (eventually_lt_atBot 0)

theorem exists_overbet_loses {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) :
    ∃ f₀ ∈ Ioo (fstar p) 1, g p f₀ < 0 := by
  have hlt : fstar p < 1 := (kelly_mem hp1 hp2).2
  have hI : ∀ᶠ f in 𝓝[<] (1 : ℝ), f ∈ Ioo (fstar p) 1 := Ioo_mem_nhdsLT hlt
  obtain ⟨f, hf, hg⟩ := (hI.and (eventually_overbet_loses hp2)).exists
  exact ⟨f, hf, hg⟩

theorem leverage_ruin {W f : ℝ} (hW : 0 ≤ W) (hf : 1 ≤ f) : wealthAfter W f false ≤ 0 := by
  unfold wealthAfter
  simp only [Bool.false_eq_true, ite_false]
  exact mul_nonpos_of_nonneg_of_nonpos hW (by linarith)

theorem leverage_ruin_unit {f : ℝ} (hf : 1 ≤ f) : 1 - f ≤ 0 := by linarith

theorem leverage_ruin_prob_tendsto_one {p : ℝ} (hp0 : 0 ≤ p) (hp2 : p < 1) :
    Tendsto (fun n : ℕ => 1 - p ^ n) atTop (𝓝 1) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hp0 hp2
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  simpa using this

end MarginCallA
