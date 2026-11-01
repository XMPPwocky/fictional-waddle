import Mathlib

open Nat

namespace Erdos849

/-! ### Erdős problem 849 (open): conjecture and partial results

* CONJECTURE, stated as a `Prop` with no proof claimed: `Erdos849Conjecture`.
* Unconditional: `erdos_849_of_le_four`, the cases `t = 1, 2, 3, 4`
  (witnesses `a = 2, 6, 120, 3003`). No example with `t ≥ 5` is known. -/

/-- CONJECTURE (Erdős problem 849, open), stated as a `Prop` with no proof claimed:
for every `t ≥ 1` there is `a` such that `choose n k = a` with `1 ≤ k ≤ n/2` has exactly `t`
solutions `n`. -/
def Erdos849Conjecture : Prop :=
    ∀ t ≥ 1, ∃ a : ℕ,
      {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = t

/-! ### Partial results: the cases `t = 1, 2, 3, 4`

The witnesses are `a = 2, 6, 120, 3003`, with solution sets
`{2}`, `{4, 6}`, `{10, 16, 120}`, `{14, 15, 78, 3003}` respectively. -/

/-- The solution set of the problem for a given value `a`. -/
def sols (a : ℕ) : Set ℕ := {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}

/-- `choose n j ≤ choose n k` whenever `j ≤ k` and `2 * k ≤ n`. -/
theorem choose_le_choose_of_le_half {n j k : ℕ} (hjk : j ≤ k) (hk : 2 * k ≤ n) :
    choose n j ≤ choose n k := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ m hjm ih =>
    have h1 : 2 * m ≤ n := by omega
    have h2 : m < n / 2 := by omega
    exact (ih h1).trans (choose_le_succ_of_lt_half_left h2)

/-- Every solution `n` of `choose n k = a` with `1 ≤ k ≤ n / 2` satisfies `n ≤ a`. -/
theorem le_of_mem_sols {a n : ℕ} (h : n ∈ sols a) : n ≤ a := by
  obtain ⟨k, hk1, hk2, hk⟩ := h
  have := choose_le_choose_of_le_half hk1 hk2
  rwa [choose_one_right, hk] at this

/-- The solution set is finite for every `a`. -/
theorem sols_finite (a : ℕ) : (sols a).Finite :=
  (Set.finite_Iic a).subset fun _ h => le_of_mem_sols h

/-- Case analysis on a solution: either `k = 1` (so `n = a`), or `k = 2`, or `k ≥ 3`
(in which case `choose n 3 ≤ a`). -/
theorem cases_of_mem_sols {a n : ℕ} (h : n ∈ sols a) :
    n = a ∨ (4 ≤ n ∧ choose n 2 = a) ∨
      (∃ k, 3 ≤ k ∧ 2 * k ≤ n ∧ choose n k = a ∧ choose n 3 ≤ a) := by
  obtain ⟨k, hk1, hk2, hk⟩ := h
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · interval_cases k
    · left; rw [← hk, choose_one_right]
    · right; left; exact ⟨by omega, hk⟩
  · right; right
    refine ⟨k, hk3, hk2, hk, ?_⟩
    rw [← hk]
    exact choose_le_choose_of_le_half hk3 hk2

/-- Membership of `n = a` in `sols a` for `a ≥ 2`. -/
theorem self_mem_sols {a : ℕ} (ha : 2 ≤ a) : a ∈ sols a :=
  ⟨1, le_rfl, by omega, choose_one_right a⟩

/-- `choose n 2 = 6` forces `n = 4`. -/
theorem eq_four_of_choose_two {n : ℕ} (h : choose n 2 = 6) : n = 4 := by
  rcases lt_trichotomy n 4 with h1 | h1 | h1
  · have := choose_le_choose 2 (Nat.le_of_lt_succ h1)
    have h3 : choose 3 2 = 3 := by decide
    omega
  · exact h1
  · have := choose_le_choose 2 (show 5 ≤ n by omega)
    have h5 : choose 5 2 = 10 := by decide
    omega

/-- `choose n 2 = 120` forces `n = 16`. -/
theorem eq_sixteen_of_choose_two {n : ℕ} (h : choose n 2 = 120) : n = 16 := by
  rcases lt_trichotomy n 16 with h1 | h1 | h1
  · have := choose_le_choose 2 (Nat.le_of_lt_succ h1)
    have h3 : choose 15 2 = 105 := by decide
    omega
  · exact h1
  · have := choose_le_choose 2 (show 17 ≤ n by omega)
    have h5 : choose 17 2 = 136 := by decide
    omega

/-- `choose n 2 = 3003` forces `n = 78`. -/
theorem eq_78_of_choose_two {n : ℕ} (h : choose n 2 = 3003) : n = 78 := by
  rcases lt_trichotomy n 78 with h1 | h1 | h1
  · have := choose_le_choose 2 (Nat.le_of_lt_succ h1)
    have h3 : choose 77 2 = 2926 := by decide
    omega
  · exact h1
  · have := choose_le_choose 2 (show 79 ≤ n by omega)
    have h5 : choose 79 2 = 3081 := by decide
    omega

/-- Finite check for `a = 120`, `k ≥ 3`: only `n = 10` (with `k = 3`). -/
theorem small_120 : ∀ n ∈ Finset.range 11, ∀ k ∈ Finset.range 6, 3 ≤ k → 2 * k ≤ n →
    n.descFactorial k / k ! = 120 → n = 10 := by decide

/-- Finite check for `a = 3003`, `k ≥ 3`: only `n = 14` or `n = 15`. -/
theorem small_3003 : ∀ n ∈ Finset.range 29, ∀ k ∈ Finset.range 15, 3 ≤ k → 2 * k ≤ n →
    n.descFactorial k / k ! = 3003 → (n = 14 ∨ n = 15) := by decide

/-- `t = 1`: the solution set for `a = 2` is `{2}`. -/
theorem sols_two : sols 2 = ↑({2} : Finset ℕ) := by
  ext n
  simp only [Finset.coe_singleton, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases cases_of_mem_sols h with h1 | ⟨hn, h1⟩ | ⟨k, hk3, hk2, hk, h3⟩
    · exact h1
    · have := choose_le_choose 2 hn
      have h4 : choose 4 2 = 6 := by decide
      omega
    · have := choose_le_choose 3 (show 6 ≤ n by omega)
      have h6 : choose 6 3 = 20 := by decide
      omega
  · rintro rfl
    exact self_mem_sols le_rfl

/-- `t = 2`: the solution set for `a = 6` is `{4, 6}`. -/
theorem sols_six : sols 6 = ↑({4, 6} : Finset ℕ) := by
  ext n
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases cases_of_mem_sols h with h1 | ⟨_, h1⟩ | ⟨k, hk3, hk2, hk, h3⟩
    · right; exact h1
    · left; exact eq_four_of_choose_two h1
    · have := choose_le_choose 3 (show 6 ≤ n by omega)
      have h6 : choose 6 3 = 20 := by decide
      omega
  · rintro (rfl | rfl)
    · exact ⟨2, by norm_num, by norm_num, by decide⟩
    · exact self_mem_sols (by norm_num)

/-- `t = 3`: the solution set for `a = 120` is `{10, 16, 120}`. -/
theorem sols_120 : sols 120 = ↑({10, 16, 120} : Finset ℕ) := by
  ext n
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases cases_of_mem_sols h with h1 | ⟨_, h1⟩ | ⟨k, hk3, hk2, hk, h3⟩
    · right; right; exact h1
    · right; left; exact eq_sixteen_of_choose_two h1
    · left
      have hn : n < 11 := by
        by_contra hn
        have := choose_le_choose 3 (show 11 ≤ n by omega)
        have h11 : choose 11 3 = 165 := by decide
        omega
      rw [choose_eq_descFactorial_div_factorial] at hk
      exact small_120 n (Finset.mem_range.mpr hn) k (Finset.mem_range.mpr (by omega)) hk3 hk2 hk
  · rintro (rfl | rfl | rfl)
    · exact ⟨3, by norm_num, by norm_num, by decide⟩
    · exact ⟨2, by norm_num, by norm_num, by decide⟩
    · exact self_mem_sols (by norm_num)

/-- `t = 4`: the solution set for `a = 3003` is `{14, 15, 78, 3003}`. -/
theorem sols_3003 : sols 3003 = ↑({14, 15, 78, 3003} : Finset ℕ) := by
  ext n
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases cases_of_mem_sols h with h1 | ⟨_, h1⟩ | ⟨k, hk3, hk2, hk, h3⟩
    · right; right; right; exact h1
    · right; right; left; exact eq_78_of_choose_two h1
    · have hn : n < 29 := by
        by_contra hn
        have := choose_le_choose 3 (show 29 ≤ n by omega)
        have h29 : choose 29 3 = 3654 := by decide
        omega
      rw [choose_eq_descFactorial_div_factorial] at hk
      rcases small_3003 n (Finset.mem_range.mpr hn) k (Finset.mem_range.mpr (by omega)) hk3 hk2 hk
        with rfl | rfl
      · left; rfl
      · right; left; rfl
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨6, by norm_num, by norm_num, by decide⟩
    · exact ⟨5, by norm_num, by norm_num, by decide⟩
    · exact ⟨2, by norm_num, by norm_num, by decide⟩
    · exact self_mem_sols (by norm_num)

/-- Partial result: the statement of Erdős problem 849 holds for `t = 1, 2, 3, 4`
(witnesses `a = 2, 6, 120, 3003`). -/
theorem erdos_849_of_le_four :
    ∀ t ≥ 1, t ≤ 4 → ∃ a : ℕ,
      {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = t := by
  intro t ht1 ht4
  interval_cases t
  · exact ⟨2, by rw [show {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = 2} = sols 2 from rfl,
      sols_two, Set.ncard_coe_finset]; rfl⟩
  · exact ⟨6, by rw [show {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = 6} = sols 6 from rfl,
      sols_six, Set.ncard_coe_finset]; rfl⟩
  · exact ⟨120, by rw [show {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = 120} = sols 120 from rfl,
      sols_120, Set.ncard_coe_finset]; rfl⟩
  · exact ⟨3003, by rw [show {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = 3003} = sols 3003 from rfl,
      sols_3003, Set.ncard_coe_finset]; rfl⟩

end Erdos849
