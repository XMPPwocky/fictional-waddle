import Mathlib

/-!
# Toxin producers in a well-mixed population: the frequency threshold c/k

Model (colicin producers, simplified from Chao & Levin 1981). Producers have frequency
`p ∈ (0,1)`, pay a cost `c ∈ (0,1)` (survival `1 - c`); each non-producer is killed with
probability `k * p`, `0 < k ≤ 1`. After selection the producer frequency is
`p' = p(1-c) / (p(1-c) + (1-p)(1-kp))`.

PROVED
* `denom_pos`: the denominator `p(1-c) + (1-p)(1-kp)` is positive.
* `next_gt_iff`: `p < p'  ↔  c < k p`.
* `next_lt_iff`: `p' < p  ↔  k p < c`.
* `next_eq_iff`: `p' = p  ↔  k p = c`.
* `threshold_mem`: if `c < k` then `c / k ∈ (0,1)`.
* `fixed_point`: if `c < k` then `next c k (c/k) = c/k`.
* `increase_above`: for every `p` with `c/k < p < 1`, `p < p'`.
* `decrease_below`: for every `p` with `0 < p < 1` and `p < c/k`, `p' < p`.
* `unstable`: if `c < k` there is `ε > 0` such that every `p` in `(c/k, c/k + ε)` lies in
  `(0,1)` and has `p < p'`, and every `p` in `(c/k - ε, c/k)` lies in `(0,1)` and has `p' < p`.

INTERPRETED
* (2) says producers spread exactly when their frequency exceeds `c/k`.
* (4) says the interior fixed point `c/k` is unstable: deviations above it grow and
  deviations below it shrink (one step of the map moves `p` away from `c/k` in the direction
  of the deviation). This is (2) restated on either side of the threshold; no claim about
  convergence to `0` or `1` is made here.
-/

namespace ToxinThresholdA

/-- Denominator of the selection map (mean fitness). -/
def denom (c k p : ℝ) : ℝ := p * (1 - c) + (1 - p) * (1 - k * p)

/-- Producer frequency after one round of selection. -/
noncomputable def next (c k p : ℝ) : ℝ := p * (1 - c) / denom c k p

theorem denom_pos {c k p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (_hc0 : 0 < c) (hc1 : c < 1)
    (_hk0 : 0 < k) (hk1 : k ≤ 1) : 0 < denom c k p := by
  unfold denom
  have h1 : 0 < p * (1 - c) := mul_pos hp0 (by linarith)
  have hkp : k * p ≤ p := by nlinarith
  have h2 : 0 < (1 - p) * (1 - k * p) := mul_pos (by linarith) (by linarith)
  linarith

/-- Key identity: `p' - p = p (1-p) (k p - c) / D`. -/
theorem next_sub {c k p : ℝ} (hD : denom c k p ≠ 0) :
    next c k p - p = p * (1 - p) * (k * p - c) / denom c k p := by
  unfold next
  field_simp
  unfold denom
  ring

theorem next_gt_iff {c k p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hc0 : 0 < c) (hc1 : c < 1)
    (hk0 : 0 < k) (hk1 : k ≤ 1) : p < next c k p ↔ c < k * p := by
  have hD := denom_pos hp0 hp1 hc0 hc1 hk0 hk1
  have hs := next_sub (c := c) (k := k) (p := p) hD.ne'
  have hpp : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  constructor
  · intro h
    have : 0 < next c k p - p := by linarith
    rw [hs] at this
    have h3 : 0 < p * (1 - p) * (k * p - c) := by
      by_contra hn
      rw [not_lt] at hn
      have : p * (1 - p) * (k * p - c) / denom c k p ≤ 0 := div_nonpos_of_nonpos_of_nonneg hn hD.le
      linarith
    have : 0 < k * p - c := by
      by_contra hn
      rw [not_lt] at hn
      nlinarith
    linarith
  · intro h
    have : 0 < next c k p - p := by
      rw [hs]
      exact div_pos (mul_pos hpp (by linarith)) hD
    linarith

theorem next_lt_iff {c k p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hc0 : 0 < c) (hc1 : c < 1)
    (hk0 : 0 < k) (hk1 : k ≤ 1) : next c k p < p ↔ k * p < c := by
  have hD := denom_pos hp0 hp1 hc0 hc1 hk0 hk1
  have hs := next_sub (c := c) (k := k) (p := p) hD.ne'
  have hpp : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  constructor
  · intro h
    have : next c k p - p < 0 := by linarith
    rw [hs] at this
    have h3 : p * (1 - p) * (k * p - c) < 0 := by
      by_contra hn
      rw [not_lt] at hn
      have : 0 ≤ p * (1 - p) * (k * p - c) / denom c k p := div_nonneg hn hD.le
      linarith
    have : k * p - c < 0 := by
      by_contra hn
      rw [not_lt] at hn
      nlinarith
    linarith
  · intro h
    have : next c k p - p < 0 := by
      rw [hs]
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hpp (by linarith)) hD
    linarith

theorem next_eq_iff {c k p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hc0 : 0 < c) (hc1 : c < 1)
    (hk0 : 0 < k) (hk1 : k ≤ 1) : next c k p = p ↔ k * p = c := by
  have hD := denom_pos hp0 hp1 hc0 hc1 hk0 hk1
  have hs := next_sub (c := c) (k := k) (p := p) hD.ne'
  have hpp : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  constructor
  · intro h
    have h0 : next c k p - p = 0 := by linarith
    rw [hs, div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · rcases mul_eq_zero.mp h0 with h0 | h0
      · exact absurd h0 hpp.ne'
      · linarith
    · exact absurd h0 hD.ne'
  · intro h
    have : next c k p - p = 0 := by
      rw [hs, show k * p - c = 0 by linarith]
      simp
    linarith

theorem threshold_mem {c k : ℝ} (hc0 : 0 < c) (hk0 : 0 < k) (hck : c < k) :
    0 < c / k ∧ c / k < 1 :=
  ⟨div_pos hc0 hk0, (div_lt_one hk0).mpr hck⟩

theorem fixed_point {c k : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hck : c < k) : next c k (c / k) = c / k := by
  obtain ⟨h0, h1⟩ := threshold_mem hc0 hk0 hck
  rw [next_eq_iff h0 h1 hc0 hc1 hk0 hk1]
  field_simp

theorem increase_above {c k p : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hp : c / k < p) (hp1 : p < 1) : p < next c k p := by
  have hp0 : 0 < p := lt_trans (div_pos hc0 hk0) hp
  rw [next_gt_iff hp0 hp1 hc0 hc1 hk0 hk1]
  rw [div_lt_iff₀ hk0] at hp
  linarith

theorem decrease_below {c k p : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hp0 : 0 < p) (hp1 : p < 1) (hp : p < c / k) : next c k p < p := by
  rw [next_lt_iff hp0 hp1 hc0 hc1 hk0 hk1]
  rw [lt_div_iff₀ hk0] at hp
  linarith

theorem unstable {c k : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hck : c < k) :
    ∃ ε > 0,
      (∀ p, c / k < p → p < c / k + ε → 0 < p ∧ p < 1 ∧ p < next c k p) ∧
      (∀ p, c / k - ε < p → p < c / k → 0 < p ∧ p < 1 ∧ next c k p < p) := by
  obtain ⟨h0, h1⟩ := threshold_mem hc0 hk0 hck
  refine ⟨min (c / k) (1 - c / k), lt_min h0 (by linarith), ?_, ?_⟩
  · intro p hpl hpu
    have hm : min (c / k) (1 - c / k) ≤ 1 - c / k := min_le_right _ _
    have hp1 : p < 1 := by linarith
    exact ⟨by linarith, hp1, increase_above hc0 hc1 hk0 hk1 hpl hp1⟩
  · intro p hpl hpu
    have hm : min (c / k) (1 - c / k) ≤ c / k := min_le_left _ _
    have hp0 : 0 < p := by linarith
    have hp1 : p < 1 := by linarith
    exact ⟨hp0, hp1, decrease_below hc0 hc1 hk0 hk1 hp0 hp1 hpu⟩

end ToxinThresholdA
