import Mathlib

/-!
# Toxin-producer threshold (colicin model, simplified)

Producers at frequency `p ∈ (0,1)` pay a cost `c ∈ (0,1)` (survive with probability `1 - c`);
each non-producer is killed with probability `k * p`, `0 < k ≤ 1`. After selection
`p' = p(1-c) / (p(1-c) + (1-p)(1-kp))`.

PROVED
* `denom_pos`: the denominator `p(1-c) + (1-p)(1-kp)` is positive.
* `next_sub_self`: the identity `p' - p = p(1-p)(kp - c) / D`.
* `next_gt_iff`: `p < p' ↔ c < k p`.
* `next_lt_iff`: `p' < p ↔ k p < c`.
* `next_eq_iff`: `p' = p ↔ k p = c`.
* `fixed_point`: if `c < k` then `p* = c/k ∈ (0,1)` and `p' = p*` at `p*`.
* `increase_above` / `decrease_below`: for `c/k < p < 1` the frequency increases,
  for `0 < p < c/k` (with `p < 1`) it decreases.
* `unstable`: for `c < k`, `c/k` is fixed and for every `δ > 0` there is `0 < η ≤ δ` such that
  points in `(c/k, c/k + η)` increase and points in `(c/k - η, c/k)` decrease.

INTERPRETED
* The threshold `c/k` separates a basin in which producers are lost (`p` decreases) from a
  basin in which they spread (`p` increases); the interior fixed point is unstable.
-/

namespace ToxinThresholdB

/-- Denominator of the selection map. -/
noncomputable def denom (c k p : ℝ) : ℝ := p * (1 - c) + (1 - p) * (1 - k * p)

/-- Producer frequency after one round of selection. -/
noncomputable def next (c k p : ℝ) : ℝ := p * (1 - c) / denom c k p

theorem denom_pos {c k p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hc1 : c < 1)
    (hk0 : 0 < k) (hk1 : k ≤ 1) : 0 < denom c k p := by
  unfold denom
  have h1 : 0 < 1 - c := by linarith
  have hkp : k * p < 1 := by nlinarith
  have h2 : 0 < 1 - k * p := by linarith
  have h3 : 0 < 1 - p := by linarith
  positivity

theorem next_sub_self {c k p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hc1 : c < 1)
    (hk0 : 0 < k) (hk1 : k ≤ 1) :
    next c k p - p = p * (1 - p) * (k * p - c) / denom c k p := by
  have hD := denom_pos hp0 hp1 hc1 hk0 hk1
  unfold next
  rw [eq_div_iff hD.ne', sub_mul, div_mul_cancel₀ _ hD.ne']
  unfold denom
  ring

theorem next_gt_iff {c k p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hc0 : 0 < c) (hc1 : c < 1)
    (hk0 : 0 < k) (hk1 : k ≤ 1) : p < next c k p ↔ c < k * p := by
  have hD := denom_pos hp0 hp1 hc1 hk0 hk1
  have hs := next_sub_self hp0 hp1 hc1 hk0 hk1
  have hpp : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  constructor
  · intro h
    have : 0 < next c k p - p := by linarith
    rw [hs] at this
    have h2 : 0 < p * (1 - p) * (k * p - c) := by
      have := (div_pos_iff_of_pos_right hD).1 this
      exact this
    have : 0 < k * p - c := (pos_iff_pos_of_mul_pos h2).1 hpp
    linarith
  · intro h
    have : 0 < next c k p - p := by
      rw [hs]
      apply div_pos _ hD
      exact mul_pos hpp (by linarith)
    linarith

theorem next_lt_iff {c k p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hc0 : 0 < c) (hc1 : c < 1)
    (hk0 : 0 < k) (hk1 : k ≤ 1) : next c k p < p ↔ k * p < c := by
  have hD := denom_pos hp0 hp1 hc1 hk0 hk1
  have hs := next_sub_self hp0 hp1 hc1 hk0 hk1
  have hpp : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  constructor
  · intro h
    have h1 : next c k p - p < 0 := by linarith
    rw [hs, div_neg_iff] at h1
    rcases h1 with ⟨_, h1⟩ | ⟨h1, _⟩
    · linarith
    · have : k * p - c < 0 := by
        by_contra hne
        rw [not_lt] at hne
        have := mul_nonneg hpp.le hne
        linarith
      linarith
  · intro h
    have : next c k p - p < 0 := by
      rw [hs]
      apply div_neg_of_neg_of_pos _ hD
      exact mul_neg_of_pos_of_neg hpp (by linarith)
    linarith

theorem next_eq_iff {c k p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hc1 : c < 1)
    (hk0 : 0 < k) (hk1 : k ≤ 1) : next c k p = p ↔ k * p = c := by
  have hD := denom_pos hp0 hp1 hc1 hk0 hk1
  have hs := next_sub_self hp0 hp1 hc1 hk0 hk1
  have hpp : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  constructor
  · intro h
    have h1 : next c k p - p = 0 := by linarith
    rw [hs, div_eq_zero_iff] at h1
    rcases h1 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hpp.ne'
      · linarith
    · exact absurd h1 hD.ne'
  · intro h
    have : next c k p - p = 0 := by
      rw [hs]
      have : k * p - c = 0 := by linarith
      rw [this]; simp
    linarith

theorem fixed_point {c k : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hck : c < k) :
    0 < c / k ∧ c / k < 1 ∧ next c k (c / k) = c / k := by
  have h0 : 0 < c / k := div_pos hc0 hk0
  have h1 : c / k < 1 := (div_lt_one hk0).2 hck
  refine ⟨h0, h1, ?_⟩
  rw [next_eq_iff h0 h1 hc1 hk0 hk1]
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

/-- Instability of the interior fixed point `c/k`: on each side of it, every point within
distance `δ` (and inside `(0,1)`) moves away from `c/k` under one step of selection. -/
theorem unstable {c k : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hck : c < k) :
    next c k (c / k) = c / k ∧
    ∀ δ > 0, ∃ η > 0, η ≤ δ ∧
      (∀ p, c / k < p → p < c / k + η → p < next c k p) ∧
      (∀ p, c / k - η < p → p < c / k → next c k p < p) := by
  obtain ⟨h0, h1, hfix⟩ := fixed_point hc0 hc1 hk0 hk1 hck
  refine ⟨hfix, fun δ hδ => ?_⟩
  refine ⟨min δ (min (c / k) (1 - c / k)), ?_, min_le_left _ _, ?_, ?_⟩
  · exact lt_min hδ (lt_min h0 (by linarith))
  · intro p hp hpη
    have : min δ (min (c / k) (1 - c / k)) ≤ 1 - c / k :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    exact increase_above hc0 hc1 hk0 hk1 hp (by linarith)
  · intro p hpη hp
    have : min δ (min (c / k) (1 - c / k)) ≤ c / k :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    exact decrease_below hc0 hc1 hk0 hk1 (by linarith) (by linarith) hp

end ToxinThresholdB
