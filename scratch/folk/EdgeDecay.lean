import Mathlib

/-!
# A method's edge lasts until everyone has it

A total edge `V > 0` (what a new method is worth) is split equally among the `k` agents who pay a cost `c > 0` to
learn it. Agents keep learning while the share still covers the cost (Grossman–Stiglitz style free entry).

PROVED:
* `entry_stops`: with `k = ⌊V / c⌋` learners (and `c ≤ V`, so `k ≥ 1`), each learner's share covers the cost,
  `c ≤ V / k`, and one more learner would not, `V / (k + 1) < c`.
* `edge_squeezed`: so each learner's net edge `V / k − c` is at least 0 and less than `V / k − V / (k + 1)`, which
  shrinks as more agents learn.
* `free_method_no_edge`: as the cost of learning goes to 0, the share each learner keeps goes to 0: for every
  `ε > 0` there is a cost below which every equilibrium share is under `ε`.
INTERPRETED (not formalized): the private edge of a published heuristic decays to its learning cost, while the
shared value stays; ideas are non-rival.
-/

namespace EdgeDecay

theorem entry_stops (V c : ℝ) (hc : 0 < c) (hcV : c ≤ V) :
    let k : ℕ := ⌊V / c⌋₊
    1 ≤ k ∧ c ≤ V / k ∧ V / (k + 1) < c := by
  intro k
  have hV : 0 < V := lt_of_lt_of_le hc hcV
  have h1 : (1 : ℝ) ≤ V / c := by rw [le_div_iff₀ hc]; linarith
  have hk1 : 1 ≤ k := Nat.le_floor (by exact_mod_cast h1)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hfl : (k : ℝ) ≤ V / c := Nat.floor_le (div_nonneg hV.le hc.le)
  have hlt : V / c < (k : ℝ) + 1 := Nat.lt_floor_add_one (V / c)
  refine ⟨hk1, ?_, ?_⟩
  · rw [le_div_iff₀ hkpos]
    have := mul_le_mul_of_nonneg_left hfl hc.le
    rw [mul_div_cancel₀ V hc.ne'] at this
    linarith [mul_comm c (k : ℝ)]
  · rw [div_lt_iff₀ (by positivity)]
    have := mul_lt_mul_of_pos_left hlt hc
    rw [mul_div_cancel₀ V hc.ne'] at this
    linarith [mul_comm c ((k : ℝ) + 1)]

theorem edge_squeezed (V c : ℝ) (hc : 0 < c) (hcV : c ≤ V) :
    let k : ℕ := ⌊V / c⌋₊
    0 ≤ V / k - c ∧ V / k - c < V / k - V / (k + 1) := by
  intro k
  obtain ⟨_, h2, h3⟩ := entry_stops V c hc hcV
  exact ⟨by linarith, by linarith⟩

theorem free_method_no_edge (V : ℝ) (hV : 0 < V) (ε : ℝ) (hε : 0 < ε) :
    ∃ c₀ > 0, ∀ c, 0 < c → c < c₀ → c ≤ V → V / (⌊V / c⌋₊ : ℝ) < ε + c := by
  refine ⟨ε, hε, fun c hc _ hcV => ?_⟩
  obtain ⟨hk1, _, h3⟩ := entry_stops V c hc hcV
  have hkpos : (0 : ℝ) < (⌊V / c⌋₊ : ℝ) := by exact_mod_cast hk1
  have hsplit : V / (⌊V / c⌋₊ : ℝ) - V / ((⌊V / c⌋₊ : ℝ) + 1) =
      V / ((⌊V / c⌋₊ : ℝ) * ((⌊V / c⌋₊ : ℝ) + 1)) := by field_simp; ring
  have hsmall : V / ((⌊V / c⌋₊ : ℝ) * ((⌊V / c⌋₊ : ℝ) + 1)) ≤ V / ((⌊V / c⌋₊ : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left hV.le (by positivity)
    nlinarith [show (1 : ℝ) ≤ (⌊V / c⌋₊ : ℝ) by exact_mod_cast hk1]
  linarith

end EdgeDecay
