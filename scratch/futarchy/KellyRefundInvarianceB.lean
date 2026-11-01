import Mathlib

/-!
# Kelly betting is invariant under refunds

A log-utility bettor stakes a fraction `f ∈ [0,1)` of wealth on a binary bet at odds `b > 0`
(wealth multiplier `1 + b f` on a win, `1 - f` on a loss), winning with probability `p`.
The market is refunded (wealth multiplier `1`) with probability `1 - ε` and resolved with
probability `ε`.

PROVED
* `refundGrowth_eq`: the expected log-growth
  `(1-ε) log 1 + ε p log(1+bf) + ε(1-p) log(1-f)` equals `ε * g p b f`, where
  `g p b f = p log(1+bf) + (1-p) log(1-f)`.
* `isMaxOn_refund_iff`: for every `ε > 0`, `f` maximizes `refundGrowth ε p b` on `[0,1)`
  iff `f` maximizes `g p b` on `[0,1)`.
* `argmax_refund_eq_argmax`: the two argmax sets on `[0,1)` are equal for every `ε > 0`.
* `kelly_facts`: if `0 < f* < 1` with `f* = p - (1-p)/b`, then `0 < p < 1`,
  `1 + b f* = p(1+b)`, `1 - f* = (1-p)(1+b)/b`.
* `kelly_le`, `kelly_lt`: if `0 < f* < 1`, then `g f ≤ g f*` for all `f ∈ [0,1)`, strictly for
  `f ≠ f*` (via `log x ≤ x - 1`, strict for `x ≠ 1`; this is the tangent-line / concavity
  argument at `f*`, where the first-order terms cancel exactly).
* `kelly_isMaxOn`, `argmax_g_eq_kelly`: `f*` is the unique maximizer of `g` on `[0,1)`.
* `argmax_refund_eq_kelly`: for every `ε > 0`, `f*` is the unique maximizer of
  `refundGrowth ε p b` on `[0,1)` (Kelly fraction unchanged by refunds).
* `optimal_refund_growth`, `sSup_refund_growth`: for `ε > 0` the optimal expected log-growth
  under refunds is `ε * g p b f*` (attained at `f*`), i.e. linear in `ε`.
* `zero_isMaxOn_of_kelly_nonpos`: if `p ∈ [0,1]` and `f* ≤ 0`, then `f = 0` maximizes `g`
  on `[0,1)` (with optimal growth `0`), and hence also maximizes `refundGrowth ε p b`.

INTERPRETED
* `ε ∈ (0,1]` is the resolution probability; only `ε > 0` is used. `ε ≤ 1` is needed only for
  the three outcome probabilities `1-ε, εp, ε(1-p)` to be a probability distribution, which
  the algebra does not use.
* "Optimal growth rate" is the maximum (equivalently the supremum) of the expected
  log-growth over `f ∈ [0,1)`.
-/

namespace KellyRefundInvarianceB

open Set Real

/-- Expected log-growth of the resolved bet. -/
noncomputable def g (p b f : ℝ) : ℝ :=
  p * Real.log (1 + b * f) + (1 - p) * Real.log (1 - f)

/-- Expected log-growth when the market is refunded with probability `1 - ε`. -/
noncomputable def refundGrowth (ε p b f : ℝ) : ℝ :=
  (1 - ε) * Real.log 1 + (ε * p) * Real.log (1 + b * f) + (ε * (1 - p)) * Real.log (1 - f)

/-- The Kelly fraction. -/
noncomputable def kelly (p b : ℝ) : ℝ := p - (1 - p) / b

/-- (1) The refunded expected log-growth is `ε * g`. -/
theorem refundGrowth_eq (ε p b f : ℝ) : refundGrowth ε p b f = ε * g p b f := by
  simp only [refundGrowth, g, Real.log_one, mul_zero, zero_add]
  ring

/-- (2) Maximizers of `ε g` and `g` on `[0,1)` coincide for `ε > 0`. -/
theorem isMaxOn_refund_iff {ε : ℝ} (hε : 0 < ε) (p b f : ℝ) :
    IsMaxOn (refundGrowth ε p b) (Ico 0 1) f ↔ IsMaxOn (g p b) (Ico 0 1) f := by
  simp only [isMaxOn_iff, refundGrowth_eq]
  constructor
  · intro h x hx
    exact le_of_mul_le_mul_left (h x hx) hε
  · intro h x hx
    exact mul_le_mul_of_nonneg_left (h x hx) hε.le

theorem argmax_refund_eq_argmax {ε : ℝ} (hε : 0 < ε) (p b : ℝ) :
    {f ∈ Ico (0 : ℝ) 1 | IsMaxOn (refundGrowth ε p b) (Ico 0 1) f}
      = {f ∈ Ico (0 : ℝ) 1 | IsMaxOn (g p b) (Ico 0 1) f} := by
  ext f
  simp only [mem_ofPred_eq, isMaxOn_refund_iff hε]

theorem kelly_facts {p b : ℝ} (hb : 0 < b) (h0 : 0 < kelly p b) (h1 : kelly p b < 1) :
    0 < p ∧ p < 1 ∧ 1 + b * kelly p b = p * (1 + b) ∧
      1 - kelly p b = (1 - p) * (1 + b) / b := by
  unfold kelly at *
  have e : (1 - p) / b * b = 1 - p := div_mul_cancel₀ _ hb.ne'
  have hp0 : 0 < p := by nlinarith [mul_pos h0 hb]
  have hp1 : p < 1 := by nlinarith [mul_pos (sub_pos.mpr h1) hb]
  refine ⟨hp0, hp1, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring

/-- Strict optimality of the Kelly fraction on `[0,1)`. -/
theorem kelly_lt {p b f : ℝ} (hb : 0 < b) (h0 : 0 < kelly p b) (h1 : kelly p b < 1)
    (hf0 : 0 ≤ f) (hf1 : f < 1) (hne : f ≠ kelly p b) :
    g p b f < g p b (kelly p b) := by
  obtain ⟨hp0, hp1, hA, hB⟩ := kelly_facts hb h0 h1
  set k := kelly p b with hk
  have hA0 : 0 < 1 + b * f := by nlinarith
  have hAk : 0 < 1 + b * k := by rw [hA]; positivity
  have hB0 : 0 < 1 - f := by linarith
  have hBk : 0 < 1 - k := by linarith
  have l1 : Real.log (1 + b * f) - Real.log (1 + b * k) ≤ (1 + b * f) / (1 + b * k) - 1 := by
    rw [← Real.log_div hA0.ne' hAk.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hA0 hAk)
  have l2 : Real.log (1 - f) - Real.log (1 - k) < (1 - f) / (1 - k) - 1 := by
    rw [← Real.log_div hB0.ne' hBk.ne']
    apply Real.log_lt_sub_one_of_pos (div_pos hB0 hBk)
    intro h
    rw [div_eq_one_iff_eq hBk.ne'] at h
    exact hne (by linarith)
  have hpne : p ≠ 0 := hp0.ne'
  have hqne : 1 - p ≠ 0 := (sub_pos.mpr hp1).ne'
  have hbne : b ≠ 0 := hb.ne'
  have hb1 : 1 + b ≠ 0 := by positivity
  have key : p * ((1 + b * f) / (1 + b * k) - 1) + (1 - p) * ((1 - f) / (1 - k) - 1) = 0 := by
    rw [hA, hB]
    field_simp
    ring
  unfold g
  nlinarith [mul_le_mul_of_nonneg_left l1 hp0.le, mul_lt_mul_of_pos_left l2 (sub_pos.mpr hp1)]

theorem kelly_le {p b f : ℝ} (hb : 0 < b) (h0 : 0 < kelly p b) (h1 : kelly p b < 1)
    (hf0 : 0 ≤ f) (hf1 : f < 1) : g p b f ≤ g p b (kelly p b) := by
  by_cases hne : f = kelly p b
  · rw [hne]
  · exact (kelly_lt hb h0 h1 hf0 hf1 hne).le

theorem kelly_isMaxOn {p b : ℝ} (hb : 0 < b) (h0 : 0 < kelly p b) (h1 : kelly p b < 1) :
    IsMaxOn (g p b) (Ico 0 1) (kelly p b) :=
  isMaxOn_iff.mpr fun _ hx => kelly_le hb h0 h1 hx.1 hx.2

/-- `f*` is the unique maximizer of `g` on `[0,1)`. -/
theorem argmax_g_eq_kelly {p b : ℝ} (hb : 0 < b) (h0 : 0 < kelly p b) (h1 : kelly p b < 1) :
    {f ∈ Ico (0 : ℝ) 1 | IsMaxOn (g p b) (Ico 0 1) f} = {kelly p b} := by
  ext f
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hf, hmax⟩
    by_contra hne
    have h := isMaxOn_iff.mp hmax (kelly p b) ⟨h0.le, h1⟩
    exact absurd h (not_le.mpr (kelly_lt hb h0 h1 hf.1 hf.2 hne))
  · rintro rfl
    exact ⟨⟨h0.le, h1⟩, kelly_isMaxOn hb h0 h1⟩

/-- (2) The Kelly fraction is the unique maximizer of the refunded growth, for every `ε > 0`. -/
theorem argmax_refund_eq_kelly {ε p b : ℝ} (hε : 0 < ε) (hb : 0 < b) (h0 : 0 < kelly p b)
    (h1 : kelly p b < 1) :
    {f ∈ Ico (0 : ℝ) 1 | IsMaxOn (refundGrowth ε p b) (Ico 0 1) f} = {kelly p b} := by
  rw [argmax_refund_eq_argmax hε, argmax_g_eq_kelly hb h0 h1]

/-- (3) The optimal refunded growth is `ε * g f*`, attained at `f*`. -/
theorem optimal_refund_growth {ε p b : ℝ} (hε : 0 < ε) (hb : 0 < b) (h0 : 0 < kelly p b)
    (h1 : kelly p b < 1) :
    IsGreatest (refundGrowth ε p b '' Ico 0 1) (ε * g p b (kelly p b)) := by
  refine ⟨⟨kelly p b, ⟨h0.le, h1⟩, refundGrowth_eq _ _ _ _⟩, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  rw [refundGrowth_eq]
  exact mul_le_mul_of_nonneg_left (kelly_le hb h0 h1 hf.1 hf.2) hε.le

theorem sSup_refund_growth {ε p b : ℝ} (hε : 0 < ε) (hb : 0 < b) (h0 : 0 < kelly p b)
    (h1 : kelly p b < 1) :
    sSup (refundGrowth ε p b '' Ico 0 1) = ε * g p b (kelly p b) :=
  (optimal_refund_growth hε hb h0 h1).csSup_eq

/-- Boundary case: if `f* ≤ 0`, betting nothing is optimal, with growth `0`. -/
theorem zero_isMaxOn_of_kelly_nonpos {p b : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hb : 0 < b)
    (hk : kelly p b ≤ 0) :
    IsMaxOn (g p b) (Ico 0 1) 0 ∧ g p b 0 = 0 := by
  have g0 : g p b 0 = 0 := by simp [g]
  refine ⟨isMaxOn_iff.mpr fun f hf => ?_, g0⟩
  rw [g0]
  have hA0 : 0 < 1 + b * f := by nlinarith [hf.1]
  have hB0 : 0 < 1 - f := by linarith [hf.2]
  have l1 := Real.log_le_sub_one_of_pos hA0
  have l2 := Real.log_le_sub_one_of_pos hB0
  have e : kelly p b * b = p * b - (1 - p) := by
    unfold kelly
    rw [sub_mul, div_mul_cancel₀ _ hb.ne']
  have hkb : f * (kelly p b * b) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hf.1 (mul_nonpos_of_nonpos_of_nonneg hk hb.le)
  unfold g
  nlinarith [mul_le_mul_of_nonneg_left l1 hp0, mul_le_mul_of_nonneg_left l2 (sub_nonneg.mpr hp1)]

theorem zero_isMaxOn_refund_of_kelly_nonpos {ε p b : ℝ} (hε : 0 < ε) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hb : 0 < b) (hk : kelly p b ≤ 0) :
    IsMaxOn (refundGrowth ε p b) (Ico 0 1) 0 :=
  (isMaxOn_refund_iff hε p b 0).mpr (zero_isMaxOn_of_kelly_nonpos hp0 hp1 hb hk).1

end KellyRefundInvarianceB
