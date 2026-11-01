import Mathlib

/-!
# Who can money-pump a discretizer?

A continuous quantity `x t` (a price, a probability, an energy increment) is settled on the integer grid each step.
The counterparty may choose the inputs adversarially. Gain to the counterparty after `t` steps = Σ (x − settled).

* P1 `memoryless_pumpable`: memoryless deterministic rounding is pumped linearly: feed it 2/5 every step.
* P2 `ef_bounded`, `ef_ledger_exact`, `ef_unpumpable`: an error-feedback (sigma–delta) ledger carries the rounding
  error forward. Against EVERY input sequence its total discrepancy stays within half a unit forever. It is deterministic
  and public, and still unpumpable at any horizon: memory beats the pump (Law).
* P3 `stochastic_round_unbiased`: stochastic rounding (round up with probability frac x) is exactly unbiased: privacy beats
  the pump in expectation (Chaos).
* P4 `veto_pumps_stochastic`: if the counterparty may veto one unfavourable draw and re-roll, the same rounding is pumped
  by frac·(1 − frac) per step. Commitment is what makes the randomness count (selective abort / grinding).
-/

open Finset

namespace DiscretizePump

/-- **P1.** Memoryless rounding is pumpable: every step the counterparty gains 2/5. -/
theorem memoryless_pumpable (t : ℕ) :
    ∑ _s ∈ range t, ((2 / 5 : ℝ) - round (2 / 5 : ℝ)) = (2 / 5) * t := by
  have h : round (2 / 5 : ℝ) = 0 := by
    rw [round_eq, Int.floor_eq_iff]; norm_num
  simp [h]; ring

/-- The error-feedback ledger's carried error. -/
noncomputable def ef (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => (x t + ef x t) - round (x t + ef x t)

/-- What the error-feedback ledger settles at step `t`. -/
noncomputable def efOut (x : ℕ → ℝ) (t : ℕ) : ℝ := round (x t + ef x t)

/-- **P2a.** The carried error never exceeds half a unit. -/
theorem ef_bounded (x : ℕ → ℝ) (t : ℕ) : |ef x t| ≤ 1 / 2 := by
  cases t with
  | zero => simp [ef]
  | succ k => simp only [ef]; exact abs_sub_round _

/-- **P2b.** The ledger is exact up to the current carried error. -/
theorem ef_ledger_exact (x : ℕ → ℝ) (t : ℕ) :
    ∑ s ∈ range t, efOut x s = ∑ s ∈ range t, x s - ef x t := by
  induction t with
  | zero => simp [ef]
  | succ k ih => rw [sum_range_succ, sum_range_succ, ih]; simp only [efOut, ef]; ring

/-- **P2c.** Unpumpable at every horizon, against every input sequence. -/
theorem ef_unpumpable (x : ℕ → ℝ) (t : ℕ) : |∑ s ∈ range t, (x s - efOut x s)| ≤ 1 / 2 := by
  rw [sum_sub_distrib, ef_ledger_exact]
  simpa using ef_bounded x t

/-- **P3.** Stochastic rounding (up with probability `fract x`) is exactly unbiased. -/
theorem stochastic_round_unbiased (x : ℝ) :
    (1 - Int.fract x) * ⌊x⌋ + Int.fract x * (⌊x⌋ + 1) = x := by
  unfold Int.fract; ring

/-- **P4.** One veto-and-re-roll turns unbiased stochastic rounding into a pump of `f·(1 − f)` per step: the settled
value rounds up only if both draws do. -/
theorem veto_pumps_stochastic (n f : ℝ) :
    (1 - f ^ 2) * n + f ^ 2 * (n + 1) = (n + f) - f * (1 - f) := by
  ring

/-! ## Exploitation is postselection over unrecognized copies of the exploiter

Q1: a deterministic memoryless settlement (anonymous: each transaction treated as a fresh party) is always pumpable by
at least 1/2 per transaction, whichever integer rule it uses. Q2: a ledger caps extraction at 1/2 per identity, and the
cap is attained: N unrecognized identities extract exactly N/2 (copies in space). Q3: identities costing ≥ 1/2 make
Sybils unprofitable. Q4: k unrecognized re-rolls (copies in time) extract f − f^(k+1) per transaction, which is positive
iff k ≥ 1. One recognized self extracts nothing. -/

/-- **Q1.** Any deterministic integer settlement rule, used anonymously, concedes at least 1/2 on one side at x = 1/2. -/
theorem anonymous_rule_pumpable (Q : ℝ → ℤ) :
    (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) - Q (1 / 2) ∨ (1 / 2 : ℝ) ≤ (Q (1 / 2) : ℝ) - 1 / 2 := by
  rcases le_or_gt (Q (1 / 2)) 0 with h | h
  · left; have : ((Q (1 / 2) : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
    linarith
  · right; have h' : (1 : ℤ) ≤ Q (1 / 2) := by omega
    have : (1 : ℝ) ≤ ((Q (1 / 2) : ℤ) : ℝ) := by exact_mod_cast h'
    linarith

/-- **Q2a.** N ledgers, one per identity: total extraction over any inputs and horizons is at most N/2. -/
theorem sybil_extraction_le (N : ℕ) (x : Fin N → ℕ → ℝ) (t : Fin N → ℕ) :
    |∑ i, ∑ s ∈ range (t i), (x i s - efOut (x i) s)| ≤ N / 2 := by
  calc |∑ i, ∑ s ∈ range (t i), (x i s - efOut (x i) s)|
      ≤ ∑ i, |∑ s ∈ range (t i), (x i s - efOut (x i) s)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1 / 2 : ℝ) := sum_le_sum (fun i _ => ef_unpumpable _ _)
    _ = N / 2 := by simp; ring

/-- **Q2b.** The bound is attained: on each fresh ledger, sell 1/2 once and collect 1/2. -/
theorem sybil_extraction_attained (N : ℕ) :
    ∑ _i : Fin N, (efOut (fun _ => (1 / 2 : ℝ)) 0 - 1 / 2) = N / 2 := by
  have h : efOut (fun _ => (1 / 2 : ℝ)) 0 = 1 := by
    simp only [efOut, ef, round_eq]; norm_num
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Q3.** If minting an identity costs at least 1/2, Sybil extraction never pays. -/
theorem identity_cost_deters (N : ℕ) (c : ℝ) (hc : 1 / 2 ≤ c) (gain : ℝ) (hg : gain ≤ N / 2) :
    gain - N * c ≤ 0 := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- **Q4.** Keeping the best of `k + 1` private draws (k unrecognized re-rolls) shifts stochastic rounding down by
`f − f^(k+1)`; for `0 < f < 1` that is positive iff `k ≥ 1`. -/
theorem rerolls_pump (n f : ℝ) (k : ℕ) :
    (1 - f ^ (k + 1)) * n + f ^ (k + 1) * (n + 1) = (n + f) - (f - f ^ (k + 1)) := by
  ring

theorem rerolls_pump_pos_iff (f : ℝ) (h0 : 0 < f) (h1 : f < 1) (k : ℕ) :
    0 < f - f ^ (k + 1) ↔ 1 ≤ k := by
  constructor
  · intro h; by_contra hk; push Not at hk
    have : k = 0 := by omega
    subst this; simp at h
  · intro hk
    have h2 : f ^ (k + 1) ≤ f ^ 2 := pow_le_pow_of_le_one h0.le h1.le (by omega)
    nlinarith

/-- **Q5.** Why a quarter: one re-roll harvests exactly half the spread between two independent copies of the rounding
coin, `½·E|X − X'| = ½·2f(1 − f)`, and that is at most `(1/2)·(1/2) = 1/4`, attained at f = 1/2. A deterministic copy
harvests the full half-step instead (Q1, Q2b). -/
theorem one_reroll_is_half_the_spread (f : ℝ) : f - f ^ 2 = (1 / 2) * (2 * f * (1 - f)) := by ring

theorem one_reroll_le_quarter (f : ℝ) : f - f ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (f - 1 / 2)]

end DiscretizePump
