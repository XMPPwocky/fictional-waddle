import Mathlib

/-!
# Kelly fraction is invariant under refunds

Setting: a log-utility bettor stakes fraction `f` of wealth on a binary bet with net odds
`b > 0`. On a win wealth is multiplied by `1 + b f`, on a loss by `1 - f`. The win has
probability `p` conditional on resolution. With probability `1 - ε` the market is refunded
(wealth multiplied by `1`), with probability `ε` it resolves.

PROVED:
* `refundGrowth_eq`: expected log-growth under refunds equals `ε * g p b f`, where
  `g p b f = p log (1 + b f) + (1 - p) log (1 - f)`.
* `isMaxOn_refund_iff`, `argmax_refund_eq`: for every `ε > 0` and every set `s`, `f` maximizes
  `ε g` on `s` iff it maximizes `g` on `s`; in particular the argmax sets over `[0,1)` agree.
* `g_le_g_kelly`, `g_lt_g_kelly`: if `0 < f* < 1` with `f* = p - (1 - p)/b`, then `f*` is the
  unique maximizer of `g` over all `f < 1` with `1 + b f > 0` (a superset of `[0,1)`).
  Proof is direct, from `log x ≤ x - 1` (tangent-line inequality, i.e. concavity of `log`).
  No hypothesis on `p` is needed: `0 < f* < 1` with `b > 0` forces `0 < p < 1`.
* `kelly_isMaxOn_g`, `kelly_isMaxOn_refund`, `isMaxOn_refund_iff_eq_kelly`: `f*` maximizes `g`
  and `ε g` on `[0,1)` for every `ε > 0`, and is the unique maximizer of `ε g` there.
* `optimal_refund_growth`, `sSup_refund_growth`, `optimal_growth_linear_in_eps`: the optimal
  growth over `[0,1)` is attained and equals `ε * g p b f*`, linear in `ε` with slope
  `g p b f*` independent of `ε`.
* `zero_isMaxOn_of_kelly_nonpos`, `zero_isMaxOn_refund_of_kelly_nonpos`: if `f* ≤ 0` and
  `0 ≤ p ≤ 1`, staking nothing is optimal on `[0,1)` for every `ε > 0` (refunds again do not
  change the answer).

INTERPRETED:
* The refund event contributes `(1 - ε) * log 1`; resolution and outcome are modelled as
  probabilities `ε` and `p` (conditional on resolution), so the joint win probability is `ε p`.
* "Maximizer over `[0,1)`" is `IsMaxOn _ (Set.Ico 0 1) f` with `f ∈ Set.Ico 0 1`;
  "optimal growth rate" is the greatest element (equivalently `sSup`) of the image of
  `[0,1)` under the expected log-growth.
-/

namespace KellyRefundInvarianceA

open Real Set

/-- Expected log-growth of a resolved bet. -/
noncomputable def g (p b f : ℝ) : ℝ :=
  p * Real.log (1 + b * f) + (1 - p) * Real.log (1 - f)

/-- Expected log-growth when the market is refunded with probability `1 - ε` and resolved
with probability `ε`; conditional on resolution the bet wins with probability `p`. -/
noncomputable def refundGrowth (ε p b f : ℝ) : ℝ :=
  (1 - ε) * Real.log 1 + (ε * p) * Real.log (1 + b * f) + (ε * (1 - p)) * Real.log (1 - f)

/-- The Kelly fraction `p - (1 - p) / b`. -/
noncomputable def kelly (p b : ℝ) : ℝ := p - (1 - p) / b

/-- (1) The refund identity. -/
theorem refundGrowth_eq (ε p b f : ℝ) : refundGrowth ε p b f = ε * g p b f := by
  simp only [refundGrowth, g, Real.log_one]
  ring

/-- (2) Scaling by `ε > 0` does not change maximizers, on any set. -/
theorem isMaxOn_refund_iff {ε p b f : ℝ} (hε : 0 < ε) (s : Set ℝ) :
    IsMaxOn (refundGrowth ε p b) s f ↔ IsMaxOn (g p b) s f := by
  simp only [isMaxOn_iff, refundGrowth_eq]
  constructor
  · intro h x hx
    exact le_of_mul_le_mul_left (h x hx) hε
  · intro h x hx
    exact mul_le_mul_of_nonneg_left (h x hx) hε.le

/-- (2) The argmax sets over `[0,1)` coincide for every `ε > 0`. -/
theorem argmax_refund_eq {ε p b : ℝ} (hε : 0 < ε) :
    {f | f ∈ Ico (0 : ℝ) 1 ∧ IsMaxOn (refundGrowth ε p b) (Ico 0 1) f} =
      {f | f ∈ Ico (0 : ℝ) 1 ∧ IsMaxOn (g p b) (Ico 0 1) f} :=
  Set.ext fun _ => and_congr_right fun _ => isMaxOn_refund_iff hε _

lemma log_le_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y ≤ Real.log x + (y / x - 1) := by
  have h1 := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h1
  linarith

lemma log_lt_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : y ≠ x) :
    Real.log y < Real.log x + (y / x - 1) := by
  have hne : y / x ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq hx.ne'] at h
    exact hxy h
  have h1 := Real.log_lt_sub_one_of_pos (div_pos hy hx) hne
  rw [Real.log_div hy.ne' hx.ne'] at h1
  linarith

lemma p_pos_of_kelly_pos {p b : ℝ} (hb : 0 < b) (h0 : 0 < kelly p b) : 0 < p := by
  by_contra hp
  replace hp := not_lt.mp hp
  have : 0 < (1 - p) / b := div_pos (by linarith) hb
  unfold kelly at h0
  linarith

lemma p_lt_one_of_kelly_lt_one {p b : ℝ} (hb : 0 < b) (h1 : kelly p b < 1) : p < 1 := by
  by_contra hp
  replace hp := not_lt.mp hp
  have : (1 - p) / b ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le
  unfold kelly at h1
  linarith

lemma one_add_mul_kelly {p b : ℝ} (hb : 0 < b) : 1 + b * kelly p b = p * (1 + b) := by
  unfold kelly
  field_simp
  ring

lemma one_sub_kelly {p b : ℝ} (hb : 0 < b) : 1 - kelly p b = (1 - p) * (1 + b) / b := by
  unfold kelly
  field_simp
  ring

/-- The first-order term of the tangent bound vanishes at the Kelly fraction. -/
lemma kelly_first_order {p b : ℝ} (hb : 0 < b) (hp0 : 0 < p) (hp1 : p < 1) (f : ℝ) :
    p * ((1 + b * f) / (1 + b * kelly p b) - 1)
      + (1 - p) * ((1 - f) / (1 - kelly p b) - 1) = 0 := by
  rw [one_add_mul_kelly hb, one_sub_kelly hb]
  have h1 : (1 - p) ≠ 0 := by linarith
  have h2 : (1 + b) ≠ 0 := by linarith
  have h3 : p ≠ 0 := hp0.ne'
  have h4 : b ≠ 0 := hb.ne'
  field_simp
  ring

/-- `f*` maximizes `g` over every admissible `f` (both payoffs positive). -/
theorem g_le_g_kelly {p b f : ℝ} (hb : 0 < b) (h0 : 0 < kelly p b) (h1 : kelly p b < 1)
    (hfA : 0 < 1 + b * f) (hfB : f < 1) : g p b f ≤ g p b (kelly p b) := by
  have hp0 := p_pos_of_kelly_pos hb h0
  have hp1 := p_lt_one_of_kelly_lt_one hb h1
  have hAs : 0 < 1 + b * kelly p b := by rw [one_add_mul_kelly hb]; positivity
  have hBs : 0 < 1 - kelly p b := by linarith
  have ha := mul_le_mul_of_nonneg_left (log_le_tangent hAs hfA) hp0.le
  have hb' := mul_le_mul_of_nonneg_left (log_le_tangent hBs (sub_pos.2 hfB))
    (sub_pos.2 hp1).le
  have key := kelly_first_order hb hp0 hp1 f
  unfold g
  nlinarith [ha, hb', key]

/-- Strict version: `f*` is the unique maximizer of `g` among admissible `f`. -/
theorem g_lt_g_kelly {p b f : ℝ} (hb : 0 < b) (h0 : 0 < kelly p b) (h1 : kelly p b < 1)
    (hfA : 0 < 1 + b * f) (hfB : f < 1) (hf : f ≠ kelly p b) :
    g p b f < g p b (kelly p b) := by
  have hp0 := p_pos_of_kelly_pos hb h0
  have hp1 := p_lt_one_of_kelly_lt_one hb h1
  have hAs : 0 < 1 + b * kelly p b := by rw [one_add_mul_kelly hb]; positivity
  have hBs : 0 < 1 - kelly p b := by linarith
  have hne : 1 + b * f ≠ 1 + b * kelly p b := by
    intro h
    apply hf
    have : b * f = b * kelly p b := by linarith
    exact mul_left_cancel₀ hb.ne' this
  have ha := mul_lt_mul_of_pos_left (log_lt_tangent hAs hfA hne) hp0
  have hb' := mul_le_mul_of_nonneg_left (log_le_tangent hBs (sub_pos.2 hfB))
    (sub_pos.2 hp1).le
  have key := kelly_first_order hb hp0 hp1 f
  unfold g
  nlinarith [ha, hb', key]

lemma admissible_of_mem_Ico {b f : ℝ} (hb : 0 < b) (hf : f ∈ Ico (0 : ℝ) 1) :
    0 < 1 + b * f ∧ f < 1 :=
  ⟨by nlinarith [hf.1], hf.2⟩

lemma kelly_mem_Ico {p b : ℝ} (h0 : 0 < kelly p b) (h1 : kelly p b < 1) :
    kelly p b ∈ Ico (0 : ℝ) 1 :=
  ⟨h0.le, h1⟩

/-- `f*` maximizes `g` on `[0,1)` when `0 < f* < 1`. -/
theorem kelly_isMaxOn_g {p b : ℝ} (hb : 0 < b) (h0 : 0 < kelly p b) (h1 : kelly p b < 1) :
    IsMaxOn (g p b) (Ico 0 1) (kelly p b) := by
  rw [isMaxOn_iff]
  intro f hf
  obtain ⟨hA, hB⟩ := admissible_of_mem_Ico hb hf
  exact g_le_g_kelly hb h0 h1 hA hB

/-- (2) `f*` maximizes the refunded growth `ε g` on `[0,1)` for every `ε > 0`. -/
theorem kelly_isMaxOn_refund {ε p b : ℝ} (hε : 0 < ε) (hb : 0 < b) (h0 : 0 < kelly p b)
    (h1 : kelly p b < 1) : IsMaxOn (refundGrowth ε p b) (Ico 0 1) (kelly p b) :=
  (isMaxOn_refund_iff hε _).2 (kelly_isMaxOn_g hb h0 h1)

/-- (2) For every `ε > 0`, `f*` is the unique maximizer of `ε g` on `[0,1)`. -/
theorem isMaxOn_refund_iff_eq_kelly {ε p b f : ℝ} (hε : 0 < ε) (hb : 0 < b)
    (h0 : 0 < kelly p b) (h1 : kelly p b < 1) (hf : f ∈ Ico (0 : ℝ) 1) :
    IsMaxOn (refundGrowth ε p b) (Ico 0 1) f ↔ f = kelly p b := by
  constructor
  · intro h
    rw [isMaxOn_refund_iff hε, isMaxOn_iff] at h
    by_contra hne
    obtain ⟨hA, hB⟩ := admissible_of_mem_Ico hb hf
    have hlt := g_lt_g_kelly hb h0 h1 hA hB hne
    have hle := h (kelly p b) (kelly_mem_Ico h0 h1)
    linarith
  · rintro rfl
    exact kelly_isMaxOn_refund hε hb h0 h1

/-- (3) The optimal refunded growth over `[0,1)` is attained and equals `ε g(f*)`. -/
theorem optimal_refund_growth {ε p b : ℝ} (hε : 0 < ε) (hb : 0 < b) (h0 : 0 < kelly p b)
    (h1 : kelly p b < 1) :
    IsGreatest (refundGrowth ε p b '' Ico 0 1) (ε * g p b (kelly p b)) := by
  refine ⟨⟨kelly p b, kelly_mem_Ico h0 h1, refundGrowth_eq _ _ _ _⟩, ?_⟩
  rintro y ⟨f, hf, rfl⟩
  rw [← refundGrowth_eq]
  exact (isMaxOn_iff.1 (kelly_isMaxOn_refund hε hb h0 h1)) f hf

theorem sSup_refund_growth {ε p b : ℝ} (hε : 0 < ε) (hb : 0 < b) (h0 : 0 < kelly p b)
    (h1 : kelly p b < 1) :
    sSup (refundGrowth ε p b '' Ico 0 1) = ε * g p b (kelly p b) :=
  (optimal_refund_growth hε hb h0 h1).csSup_eq

/-- (3) Linearity in `ε`: one constant `C = g(f*)`, independent of `ε`, gives the optimal
growth `ε * C` for every `ε ∈ (0,1]`. -/
theorem optimal_growth_linear_in_eps {p b : ℝ} (hb : 0 < b) (h0 : 0 < kelly p b)
    (h1 : kelly p b < 1) :
    ∃ C : ℝ, C = g p b (kelly p b) ∧
      ∀ ε ∈ Ioc (0 : ℝ) 1, sSup (refundGrowth ε p b '' Ico 0 1) = ε * C :=
  ⟨_, rfl, fun _ hε => sSup_refund_growth hε.1 hb h0 h1⟩

/-- Boundary case: if `f* ≤ 0` (and `0 ≤ p ≤ 1`), staking nothing maximizes `g` on `[0,1)`. -/
theorem zero_isMaxOn_of_kelly_nonpos {p b : ℝ} (hb : 0 < b) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hk : kelly p b ≤ 0) : IsMaxOn (g p b) (Ico 0 1) 0 := by
  rw [isMaxOn_iff]
  intro f hf
  obtain ⟨hA, hB⟩ := admissible_of_mem_Ico hb hf
  have hbk : b * kelly p b = p * b - (1 - p) := by
    unfold kelly
    field_simp
  have l1 := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hA) hp0
  have l2 := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (sub_pos.2 hB))
    (sub_nonneg.2 hp1)
  have hprod : f * (b * kelly p b) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hf.1 (by nlinarith)
  have hg0 : g p b 0 = 0 := by simp [g]
  rw [hg0]
  unfold g
  nlinarith [l1, l2, hprod, hbk]

theorem zero_isMaxOn_refund_of_kelly_nonpos {ε p b : ℝ} (hε : 0 < ε) (hb : 0 < b)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hk : kelly p b ≤ 0) :
    IsMaxOn (refundGrowth ε p b) (Ico 0 1) 0 :=
  (isMaxOn_refund_iff hε _).2 (zero_isMaxOn_of_kelly_nonpos hb hp0 hp1 hk)

end KellyRefundInvarianceA
