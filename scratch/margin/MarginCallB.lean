import Mathlib

/-!
# MarginCallB

Even-money bet (odds `b = 1`) won with probability `p`, staking fraction `f` of wealth.
Expected log-growth per round: `g p f = p * log (1 + f) + (1 - p) * log (1 - f)`.

PROVED (for `1/2 < p < 1`):
* `kelly_mem` : `f* = 2p - 1 ∈ [0, 1)`.
* `kelly_isMaxOn` : `g p` is maximized on `[0, 1)` at `f* = 2p - 1`
  (`IsMaxOn (g p) (Set.Ico 0 1) (2 * p - 1)`).
* `kelly_strict_max` : the maximum is strict: `g p f < g p f*` for every `f ∈ (-1, 1)`, `f ≠ f*`.
* `kelly_growth_pos` : `0 < g p (2 * p - 1)`.
* `tendsto_atBot` : `Tendsto (g p) (𝓝[<] 1) atBot` (needs only `p < 1`).
* `exists_overbet_negative` : there is `f₀ ∈ (f*, 1)` with `g p f₀ < 0` (needs only `p < 1`).
* `leverage_ruin` : for `f ≥ 1` and any wealth `W ≥ 0`, a single loss leaves `W * (1 - f) ≤ 0`;
  in particular `1 - f ≤ 0`.
* `leverage_ruin_prob_tendsto_one` : for `0 ≤ p < 1`, the probability `1 - p ^ n` of at least
  one loss in `n` independent rounds tends to `1`.

INTERPRETED: a claim sized beyond its margin gets called. Staking near the whole margin
drives expected log-growth to `-∞` however large the edge, over-betting past some point has
negative growth despite a positive edge, and leverage `f ≥ 1` is wiped out by one loss.
-/

namespace MarginCallB

open Filter Topology Real

/-- Expected log-growth of staking fraction `f` on an even-money bet won with probability `p`. -/
noncomputable def g (p f : ℝ) : ℝ := p * Real.log (1 + f) + (1 - p) * Real.log (1 - f)

theorem kelly_mem {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) :
    2 * p - 1 ∈ Set.Ico (0 : ℝ) 1 := by
  constructor <;> linarith

/-- Gap to the optimum on `(-1, 1)` written as a sum of logs of ratios. -/
theorem g_sub_le {p f : ℝ} (hp0 : 0 < p) (hp2 : p < 1) (hf1 : -1 < f) (hf2 : f < 1) :
    g p f - g p (2 * p - 1) =
      p * Real.log ((1 + f) / (2 * p)) + (1 - p) * Real.log ((1 - f) / (2 * (1 - p))) := by
  unfold g
  have h1 : (0 : ℝ) < 1 + f := by linarith
  have h2 : (0 : ℝ) < 1 - f := by linarith
  have h3 : (0 : ℝ) < 2 * p := by linarith
  have h4 : (0 : ℝ) < 2 * (1 - p) := by linarith
  rw [Real.log_div h1.ne' h3.ne', Real.log_div h2.ne' h4.ne']
  have e1 : (1 : ℝ) + (2 * p - 1) = 2 * p := by ring
  have e2 : (1 : ℝ) - (2 * p - 1) = 2 * (1 - p) := by ring
  rw [e1, e2]
  ring

theorem kelly_le {p f : ℝ} (hp0 : 0 < p) (hp2 : p < 1) (hf1 : -1 < f) (hf2 : f < 1) :
    g p f ≤ g p (2 * p - 1) := by
  have hd := g_sub_le hp0 hp2 hf1 hf2
  have h1 : (0 : ℝ) < 1 + f := by linarith
  have h2 : (0 : ℝ) < 1 - f := by linarith
  have h3 : (0 : ℝ) < 2 * p := by linarith
  have h4 : (0 : ℝ) < 2 * (1 - p) := by linarith
  have l1 := Real.log_le_sub_one_of_pos (div_pos h1 h3)
  have l2 := Real.log_le_sub_one_of_pos (div_pos h2 h4)
  have m1 := mul_le_mul_of_nonneg_left l1 hp0.le
  have m2 := mul_le_mul_of_nonneg_left l2 (by linarith : (0 : ℝ) ≤ 1 - p)
  have k1 : p * ((1 + f) / (2 * p) - 1) = (1 + f) / 2 - p := by field_simp
  have k2 : (1 - p) * ((1 - f) / (2 * (1 - p)) - 1) = (1 - f) / 2 - (1 - p) := by
    have : (1 - p) ≠ 0 := by linarith
    field_simp
  linarith

theorem kelly_strict_max {p f : ℝ} (hp0 : 0 < p) (hp2 : p < 1) (hf1 : -1 < f) (hf2 : f < 1)
    (hne : f ≠ 2 * p - 1) : g p f < g p (2 * p - 1) := by
  have hd := g_sub_le hp0 hp2 hf1 hf2
  have h1 : (0 : ℝ) < 1 + f := by linarith
  have h2 : (0 : ℝ) < 1 - f := by linarith
  have h3 : (0 : ℝ) < 2 * p := by linarith
  have h4 : (0 : ℝ) < 2 * (1 - p) := by linarith
  have hx : (1 + f) / (2 * p) ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq h3.ne'] at h
    exact hne (by linarith)
  have l1 := Real.log_lt_sub_one_of_pos (div_pos h1 h3) hx
  have l2 := Real.log_le_sub_one_of_pos (div_pos h2 h4)
  have m1 := mul_lt_mul_of_pos_left l1 hp0
  have m2 := mul_le_mul_of_nonneg_left l2 (by linarith : (0 : ℝ) ≤ 1 - p)
  have k1 : p * ((1 + f) / (2 * p) - 1) = (1 + f) / 2 - p := by field_simp
  have k2 : (1 - p) * ((1 - f) / (2 * (1 - p)) - 1) = (1 - f) / 2 - (1 - p) := by
    have : (1 - p) ≠ 0 := by linarith
    field_simp
  linarith

/-- (1) `g p` is maximized on `[0, 1)` at `f* = 2p - 1`. -/
theorem kelly_isMaxOn {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) :
    IsMaxOn (g p) (Set.Ico 0 1) (2 * p - 1) := by
  intro f hf
  exact kelly_le (by linarith) hp2 (by linarith [hf.1]) hf.2

/-- (1) The optimal growth rate is strictly positive. -/
theorem kelly_growth_pos {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) :
    0 < g p (2 * p - 1) := by
  have h := kelly_strict_max (f := 0) (by linarith) hp2 (by norm_num) (by norm_num)
    (by intro h; linarith)
  have h0 : g p 0 = 0 := by simp [g]
  linarith

/-- (2) Growth tends to `-∞` as the stake approaches the whole margin from below. -/
theorem tendsto_atBot {p : ℝ} (hp2 : p < 1) :
    Tendsto (g p) (𝓝[<] 1) atBot := by
  have hA : Tendsto (fun f : ℝ => p * Real.log (1 + f)) (𝓝[<] 1) (𝓝 (p * Real.log (1 + 1))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt (fun f : ℝ => p * Real.log (1 + f)) 1 := by
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.log (by fun_prop) (by norm_num)
    exact hc.tendsto
  have hsub : Tendsto (fun f : ℝ => 1 - f) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun f : ℝ => 1 - f) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with f hf
      simp only [Set.mem_Ioi, sub_pos]
      exact hf
  have hB : Tendsto (fun f : ℝ => (1 - p) * Real.log (1 - f)) (𝓝[<] 1) atBot :=
    (Real.tendsto_log_nhdsGT_zero.comp hsub).const_mul_atBot (by linarith)
  exact hA.add_atBot hB

/-- (3) Over-betting past some point has negative growth despite a positive edge. -/
theorem exists_overbet_negative {p : ℝ} (hp2 : p < 1) :
    ∃ f₀ ∈ Set.Ioo (2 * p - 1) 1, g p f₀ < 0 := by
  have hneg : ∀ᶠ f in 𝓝[<] (1 : ℝ), g p f < 0 :=
    (tendsto_atBot hp2).eventually (eventually_lt_atBot 0)
  have hIoo : ∀ᶠ f in 𝓝[<] (1 : ℝ), f ∈ Set.Ioo (2 * p - 1) 1 :=
    Ioo_mem_nhdsLT (by linarith)
  obtain ⟨f, hf1, hf2⟩ := (hIoo.and hneg).exists
  exact ⟨f, hf1, hf2⟩

/-- (4) With leverage `f ≥ 1`, a single loss leaves wealth `W * (1 - f) ≤ 0`. -/
theorem leverage_ruin {f W : ℝ} (hf : 1 ≤ f) (hW : 0 ≤ W) : W * (1 - f) ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos hW (by linarith)

/-- (4) Unit-wealth form: a single loss at leverage `f ≥ 1` leaves `1 - f ≤ 0`. -/
theorem leverage_ruin_unit {f : ℝ} (hf : 1 ≤ f) : 1 - f ≤ 0 := by linarith

/-- With independent rounds, the probability `1 - p ^ n` of at least one loss tends to `1`. -/
theorem leverage_ruin_prob_tendsto_one {p : ℝ} (hp0 : 0 ≤ p) (hp2 : p < 1) :
    Tendsto (fun n : ℕ => 1 - p ^ n) atTop (𝓝 1) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hp0 hp2
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h

end MarginCallB
