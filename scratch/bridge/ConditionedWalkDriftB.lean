import Mathlib

/-!
# Conditioned simple random walk: drift toward the endpoint

Simple random walk on `ℤ`, steps `±1` with probability `1/2` each.
`N x m` is the number of `m`-step paths from `x` to `0`: `C(m, d)` with
`d = (m + x)/2` down-steps when `m + x` is even and `|x| ≤ m`, and `0` otherwise.
Conditioned on ending at `0` after `m` steps, the probability that the next
step is up is `N (x+1) (m-1) / N x m` and down is `N (x-1) (m-1) / N x m`
(each `±1` step has weight `1/2`, which cancels in the ratio).

PROVED
* `choose_pred_mul` : `C(m-1, k) * m = C(m, k) * (m - k)` for all `m k : ℕ`
  (the hypothesis `k ≤ m` is not needed; both sides vanish for `k > m`).
* `choose_pred_pred_mul` : `C(m-1, k-1) * m = C(m, k) * k` for `1 ≤ m`, `1 ≤ k`.
* `N_of_down` : `N (2d - m) m = C(m, d)` for `d ≤ m`; `N_eq_zero` : `N x m = 0` if `m < |x|`.
* `pUp_eq_d`, `pDown_eq_d` : with `x = 2d - m`, `d ≤ m`, `1 ≤ m`:
  `P(up) = (m - d)/m`, `P(down) = d/m` (parametrized by the number `d` of down-steps).
* `pUp_eq` : `P(up | x, m) = (m - x)/(2m)` under `1 ≤ m`, `|x| ≤ m`, `Even (m + x)`.
* `pDown_eq` : `P(down | x, m) = (m + x)/(2m)` under the same hypotheses.
* `pUp_add_pDown` : `P(up) + P(down) = 1` (both defined from path counts; this is Pascal's rule).
* `drift_eq` : `P(up) - P(down) = -x/m`.

INTERPRETED (not formalized)
Selecting the paths that end at `0` makes the ensemble look attracted to a future
point: the conditioned walk has drift `-x/m`, proportional to the distance from the
target and inversely proportional to the time left (discrete Brownian bridge, Doob
h-transform with `h(x, m) = N x m / 2^m`). No backward influence is involved: the
conditional step law is a ratio of forward path counts.
-/

namespace ConditionedWalkDriftB

/-- Number of `m`-step `±1` paths from `x` to `0`. -/
def N (x : ℤ) (m : ℕ) : ℕ :=
  if Even ((m : ℤ) + x) ∧ |x| ≤ (m : ℤ) then Nat.choose m (((m : ℤ) + x) / 2).toNat else 0

/-- Probability that the next step is up, conditioned on reaching `0` in `m` steps. -/
noncomputable def pUp (x : ℤ) (m : ℕ) : ℝ := (N (x + 1) (m - 1) : ℝ) / (N x m : ℝ)

/-- Probability that the next step is down, conditioned on reaching `0` in `m` steps. -/
noncomputable def pDown (x : ℤ) (m : ℕ) : ℝ := (N (x - 1) (m - 1) : ℝ) / (N x m : ℝ)

/-- (1) `C(m-1, k) * m = C(m, k) * (m - k)`. -/
theorem choose_pred_mul (m k : ℕ) : (m - 1).choose k * m = m.choose k * (m - k) := by
  rcases m with _ | n
  · simp
  · simpa using Nat.choose_mul_succ_eq n k

/-- Companion identity: `C(m-1, k-1) * m = C(m, k) * k` for `1 ≤ m`, `1 ≤ k`. -/
theorem choose_pred_pred_mul (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    (m - 1).choose (k - 1) * m = m.choose k * k := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have := Nat.add_one_mul_choose_eq n j
  simp only [Nat.add_sub_cancel]
  linarith [mul_comm (n + 1) (n.choose j)]

theorem N_of_down (m d : ℕ) (hd : d ≤ m) : N (2 * (d : ℤ) - m) m = m.choose d := by
  have h2 : |2 * (d : ℤ) - m| ≤ (m : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
  simp [N, h2]

theorem N_eq_zero (x : ℤ) (m : ℕ) (h : (m : ℤ) < |x|) : N x m = 0 := by
  simp [N, not_le.mpr h]

theorem pUp_eq_d (m d : ℕ) (hm : 1 ≤ m) (hd : d ≤ m) :
    pUp (2 * (d : ℤ) - m) m = ((m : ℝ) - d) / m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hpos : (0 : ℝ) < ((n + 1).choose d : ℕ) := by exact_mod_cast Nat.choose_pos hd
  unfold pUp
  rw [N_of_down _ _ hd]
  simp only [Nat.add_sub_cancel]
  rcases Nat.lt_or_ge d (n + 1) with hlt | hge
  · have hx : 2 * (d : ℤ) - ((n + 1 : ℕ) : ℤ) + 1 = 2 * (d : ℤ) - (n : ℤ) := by push_cast; ring
    rw [hx, N_of_down n d (by omega)]
    have key := choose_pred_mul (n + 1) d
    simp only [Nat.add_sub_cancel] at key
    have key' : ((n.choose d : ℕ) : ℝ) * ((n : ℝ) + 1) =
        (((n + 1).choose d : ℕ) : ℝ) * ((n : ℝ) + 1 - d) := by
      have := congrArg (fun t : ℕ => (t : ℝ)) key
      simp only [Nat.cast_mul, Nat.cast_sub (by omega : d ≤ n + 1)] at this
      push_cast at this
      linarith
    rw [div_eq_div_iff (ne_of_gt hpos) (by positivity)]
    push_cast
    linarith
  · have hdn : d = n + 1 := le_antisymm hd hge
    subst hdn
    rw [N_eq_zero]
    · simp
    · rw [abs_of_nonneg (by push_cast; omega)]
      push_cast; omega

theorem pDown_eq_d (m d : ℕ) (hm : 1 ≤ m) (hd : d ≤ m) :
    pDown (2 * (d : ℤ) - m) m = (d : ℝ) / m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hpos : (0 : ℝ) < ((n + 1).choose d : ℕ) := by exact_mod_cast Nat.choose_pos hd
  unfold pDown
  rw [N_of_down _ _ hd]
  simp only [Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos d with h0 | hpos'
  · subst h0
    rw [N_eq_zero]
    · simp
    · push_cast
      rw [abs_of_neg (by omega)]
      omega
  · have hx : 2 * (d : ℤ) - ((n + 1 : ℕ) : ℤ) - 1 = 2 * ((d - 1 : ℕ) : ℤ) - (n : ℤ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ d)]; ring
    rw [hx, N_of_down n (d - 1) (by omega)]
    have key := choose_pred_pred_mul (n + 1) d (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at key
    have key' : ((n.choose (d - 1) : ℕ) : ℝ) * ((n : ℝ) + 1) =
        (((n + 1).choose d : ℕ) : ℝ) * (d : ℝ) := by
      have := congrArg (fun t : ℕ => (t : ℝ)) key
      push_cast at this
      linarith
    rw [div_eq_div_iff (ne_of_gt hpos) (by positivity)]
    push_cast
    linarith

/-- From the hypotheses on `x`, extract the number of down-steps `d`. -/
theorem exists_down (x : ℤ) (m : ℕ) (hx : |x| ≤ m) (hp : Even ((m : ℤ) + x)) :
    ∃ d : ℕ, d ≤ m ∧ x = 2 * (d : ℤ) - m := by
  obtain ⟨r, hr⟩ := hp
  have := abs_le.mp hx
  refine ⟨r.toNat, ?_, ?_⟩ <;> omega

/-- (2) `P(up | x, m) = (m - x)/(2m)`. -/
theorem pUp_eq (x : ℤ) (m : ℕ) (hm : 1 ≤ m) (hx : |x| ≤ m) (hp : Even ((m : ℤ) + x)) :
    pUp x m = ((m : ℝ) - x) / (2 * m) := by
  obtain ⟨d, hd, rfl⟩ := exists_down x m hx hp
  rw [pUp_eq_d m d hm hd]
  have : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp
  push_cast
  ring

/-- (2) `P(down | x, m) = (m + x)/(2m)`. -/
theorem pDown_eq (x : ℤ) (m : ℕ) (hm : 1 ≤ m) (hx : |x| ≤ m) (hp : Even ((m : ℤ) + x)) :
    pDown x m = ((m : ℝ) + x) / (2 * m) := by
  obtain ⟨d, hd, rfl⟩ := exists_down x m hx hp
  rw [pDown_eq_d m d hm hd]
  have : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp
  push_cast
  ring

/-- (2) The two conditioned step probabilities sum to `1`. -/
theorem pUp_add_pDown (x : ℤ) (m : ℕ) (hm : 1 ≤ m) (hx : |x| ≤ m)
    (hp : Even ((m : ℤ) + x)) : pUp x m + pDown x m = 1 := by
  rw [pUp_eq x m hm hx hp, pDown_eq x m hm hx hp]
  have : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp
  ring

/-- (3) Conditioned expected step: `P(up) - P(down) = -x/m`. -/
theorem drift_eq (x : ℤ) (m : ℕ) (hm : 1 ≤ m) (hx : |x| ≤ m) (hp : Even ((m : ℤ) + x)) :
    pUp x m - pDown x m = -(x : ℝ) / m := by
  rw [pUp_eq x m hm hx hp, pDown_eq x m hm hx hp]
  have : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp
  ring

end ConditionedWalkDriftB
