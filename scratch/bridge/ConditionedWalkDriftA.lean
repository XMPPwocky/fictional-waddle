import Mathlib

/-!
# Conditioned simple random walk: drift toward the endpoint

Simple random walk on `ℤ` with steps `±1`, each of probability `1/2`.
`N x m` is the number of `m`-step paths from `x` to `0`: it is `C(m, d)` with
`d = (m + x) / 2` (the number of down-steps) when `m + x` is even and `|x| ≤ m`,
and `0` otherwise. Since every `m`-step path has probability `2^(-m)`, conditioning on
ending at `0` makes the probability that the next step is up equal to
`N (x+1) (m-1) / N x m`, and down `N (x-1) (m-1) / N x m`; these are the definitions
`pUp` and `pDown` below.

PROVED
* `choose_pred_mul`: `C(m-1, k) * m = C(m, k) * (m - k)` (in `ℕ`, for all `m k`;
  in particular for `k ≤ m`).
* `choose_pred_pred_mul`: `C(m-1, k-1) * m = C(m, k) * k` for `1 ≤ k`.
* `N_two_mul_sub`: in the down-step parametrization `x = 2d - m`,
  `N (2d - m) m = C(m, d)` if `0 ≤ d ≤ m`, else `0`.
* `N_pos`: `0 < N x m` under the hypotheses `|x| ≤ m`, `m + x` even.
* `pUp_eq`: for `1 ≤ m`, `|x| ≤ m`, `m + x` even: `pUp x m = (m - x) / (2m)`.
* `pDown_eq`: same hypotheses: `pDown x m = (m + x) / (2m)`.
* `pUp_add_pDown`: `pUp x m + pDown x m = 1`.
* `N_pascal`: `N (x+1) (m-1) + N (x-1) (m-1) = N x m` (the two conditional
  probabilities are the path-count fractions of a partition).
* `drift_eq`: `pUp x m * 1 + pDown x m * (-1) = pUp x m - pDown x m = -x / m`.

The proofs pass internally through the down-step count `d` (`x = 2d - m`); the
headline statements are in terms of `x` with real division and explicit hypotheses.

INTERPRETED
Selecting the ensemble of paths that end at `0` at time `m` produces a conditional
step law with mean `-x / m`: a pull toward `0` proportional to the distance and inversely
proportional to the time remaining (discrete Brownian bridge; Doob h-transform with
`h(x, m) = N x m`). The apparent attraction to a future point comes entirely from
conditioning on the endpoint; no backward influence is involved.
-/

namespace ConditionedWalkDriftA

/-- Number of `m`-step `±1` paths from `x` to `0`. -/
def N (x : ℤ) (m : ℕ) : ℕ :=
  if Even ((m : ℤ) + x) ∧ |x| ≤ (m : ℤ) then Nat.choose m (((m : ℤ) + x) / 2).toNat else 0

/-- Probability that the next step is up, conditioned on reaching `0` after `m` steps. -/
noncomputable def pUp (x : ℤ) (m : ℕ) : ℝ := (N (x + 1) (m - 1) : ℝ) / (N x m : ℝ)

/-- Probability that the next step is down, conditioned on reaching `0` after `m` steps. -/
noncomputable def pDown (x : ℤ) (m : ℕ) : ℝ := (N (x - 1) (m - 1) : ℝ) / (N x m : ℝ)

theorem choose_pred_mul (m k : ℕ) :
    (m - 1).choose k * m = m.choose k * (m - k) := by
  rcases m with _ | n
  · simp
  · simpa using Nat.choose_mul_succ_eq n k

theorem choose_pred_mul_of_le (m k : ℕ) (_hk : k ≤ m) :
    (m - 1).choose k * m = m.choose k * (m - k) :=
  choose_pred_mul m k

theorem choose_pred_pred_mul (m k : ℕ) (hk : 1 ≤ k) :
    (m - 1).choose (k - 1) * m = m.choose k * k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases m with _ | n
  · simp
  · have := Nat.add_one_mul_choose_eq n j
    simp only [Nat.add_sub_cancel]
    rw [mul_comm]; exact this

theorem N_two_mul_sub (d : ℤ) (m : ℕ) :
    N (2 * d - m) m = if 0 ≤ d ∧ d ≤ m then m.choose d.toNat else 0 := by
  unfold N
  have h1 : (m : ℤ) + (2 * d - m) = 2 * d := by ring
  have h2 : |2 * d - (m : ℤ)| ≤ m ↔ 0 ≤ d ∧ d ≤ m := by rw [abs_le]; omega
  rw [h1, Int.mul_ediv_cancel_left _ two_ne_zero]
  simp only [even_two_mul, true_and, h2]

/-- Extract the down-step count `k` with `x = 2k - m`, `k ≤ m`. -/
theorem exists_down_count (x : ℤ) (m : ℕ) (habs : |x| ≤ m) (hev : Even ((m : ℤ) + x)) :
    ∃ k : ℕ, k ≤ m ∧ x = 2 * (k : ℤ) - m := by
  obtain ⟨r, hr⟩ := hev
  rw [abs_le] at habs
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ r by omega)
  exact ⟨k, by omega, by omega⟩

theorem N_down_count (k m : ℕ) (hk : k ≤ m) : N (2 * (k : ℤ) - m) m = m.choose k := by
  rw [N_two_mul_sub]
  simp [hk]

theorem N_pos (x : ℤ) (m : ℕ) (habs : |x| ≤ m) (hev : Even ((m : ℤ) + x)) :
    0 < N x m := by
  obtain ⟨k, hk, rfl⟩ := exists_down_count x m habs hev
  rw [N_down_count k m hk]
  exact Nat.choose_pos hk

theorem N_up_next (k m : ℕ) (hm : 1 ≤ m) :
    N (2 * (k : ℤ) - m + 1) (m - 1) = (m - 1).choose k := by
  have e : 2 * (k : ℤ) - m + 1 = 2 * (k : ℤ) - ((m - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hm]; ring
  rw [e, N_two_mul_sub]
  split_ifs with h
  · simp
  · have : m - 1 < k := by omega
    rw [Nat.choose_eq_zero_of_lt this]

theorem N_down_next (k m : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) :
    N (2 * (k : ℤ) - m - 1) (m - 1) = if 1 ≤ k then (m - 1).choose (k - 1) else 0 := by
  have e : 2 * (k : ℤ) - m - 1 = 2 * ((k : ℤ) - 1) - ((m - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hm]; ring
  rw [e, N_two_mul_sub]
  by_cases h1 : 1 ≤ k
  · have hc : 0 ≤ (k : ℤ) - 1 ∧ (k : ℤ) - 1 ≤ ((m - 1 : ℕ) : ℤ) := by omega
    simp only [hc, h1, and_self, ite_true]
    congr 1
    omega
  · have hc : ¬ (0 ≤ (k : ℤ) - 1 ∧ (k : ℤ) - 1 ≤ ((m - 1 : ℕ) : ℤ)) := by omega
    simp only [hc, h1, ite_false]

/-- Conditioned probability of an up-step: `(m - x) / (2m)`. -/
theorem pUp_eq (x : ℤ) (m : ℕ) (hm : 1 ≤ m) (habs : |x| ≤ m) (hev : Even ((m : ℤ) + x)) :
    pUp x m = ((m : ℝ) - x) / (2 * m) := by
  obtain ⟨k, hk, rfl⟩ := exists_down_count x m habs hev
  unfold pUp
  rw [N_up_next k m hm, N_down_count k m hk]
  have hid : ((m - 1).choose k : ℝ) * m = (m.choose k : ℝ) * ((m : ℝ) - k) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) (choose_pred_mul m k)
    push_cast [Nat.cast_sub hk] at this
    exact this
  have hC : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hk
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_eq_div_iff hC.ne' (by positivity)]
  push_cast
  linear_combination 2 * hid

/-- Conditioned probability of a down-step: `(m + x) / (2m)`. -/
theorem pDown_eq (x : ℤ) (m : ℕ) (hm : 1 ≤ m) (habs : |x| ≤ m) (hev : Even ((m : ℤ) + x)) :
    pDown x m = ((m : ℝ) + x) / (2 * m) := by
  obtain ⟨k, hk, rfl⟩ := exists_down_count x m habs hev
  unfold pDown
  rw [N_down_next k m hm hk, N_down_count k m hk]
  have hC : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hk
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  split_ifs with h1
  · have hid : ((m - 1).choose (k - 1) : ℝ) * m = (m.choose k : ℝ) * k := by
      exact_mod_cast choose_pred_pred_mul m k h1
    rw [div_eq_div_iff hC.ne' (by positivity)]
    push_cast
    linear_combination 2 * hid
  · have : k = 0 := by omega
    subst this
    push_cast
    simp

theorem pUp_add_pDown (x : ℤ) (m : ℕ) (hm : 1 ≤ m) (habs : |x| ≤ m)
    (hev : Even ((m : ℤ) + x)) : pUp x m + pDown x m = 1 := by
  rw [pUp_eq x m hm habs hev, pDown_eq x m hm habs hev]
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp
  ring

theorem N_pascal (x : ℤ) (m : ℕ) (hm : 1 ≤ m) (habs : |x| ≤ m) (hev : Even ((m : ℤ) + x)) :
    N (x + 1) (m - 1) + N (x - 1) (m - 1) = N x m := by
  have h := pUp_add_pDown x m hm habs hev
  have hN : (0 : ℝ) < N x m := by exact_mod_cast N_pos x m habs hev
  unfold pUp pDown at h
  rw [← add_div, div_eq_one_iff_eq hN.ne'] at h
  exact_mod_cast h

/-- Conditioned expected step: `pUp - pDown = -x / m`. -/
theorem drift_eq (x : ℤ) (m : ℕ) (hm : 1 ≤ m) (habs : |x| ≤ m) (hev : Even ((m : ℤ) + x)) :
    pUp x m * 1 + pDown x m * (-1) = -(x : ℝ) / m ∧ pUp x m - pDown x m = -(x : ℝ) / m := by
  rw [pUp_eq x m hm habs hev, pDown_eq x m hm habs hev]
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · field_simp; ring
  · field_simp; ring

end ConditionedWalkDriftA
