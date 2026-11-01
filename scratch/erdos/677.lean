import Mathlib

/-- The least common multiple of `{n+1, ..., n+k}`. -/
def Finset.lcmInterval {α : Type*} [CommSemiring α] [NormalizedGCDMonoid α]
    [Preorder α] [LocallyFiniteOrder α] (n k : α) : α := (Finset.Ioc n (n + k)).lcm id

namespace Erdos677

open Finset

/-! ### Erdős problem 677 (open): conjecture and partial results

Erdős problem 677 asks whether `lcm{n+1..n+k} ≠ lcm{m+1..m+k}` whenever `m ≥ n + k`.
The general case is open; for fixed `k` finiteness of exceptions follows from Siegel's theorem
on integral points, which is not elementary.

* CONJECTURE, stated as a `Prop` with no proof claimed: `Erdos677Conjecture`.
* Unconditional: `erdos_677_of_prod_lt` (trivial size bound), `erdos_677_k_one`,
  `erdos_677_k_two`, `erdos_677_k_le_two` (the cases `k ≤ 2`), and
  `erdos_677_k_three_reduction` (the case `k = 3` reduced to a Diophantine equation). -/

/-- Every element of `{n+1, ..., n+k}` divides `lcmInterval n k`. -/
lemma dvd_lcmInterval {n k i : ℕ} (hi : i ∈ Ioc n (n + k)) : i ∣ lcmInterval n k :=
  Finset.dvd_lcm hi

/-- `lcmInterval n k` divides the product `(n+1) ⋯ (n+k)`. -/
lemma lcmInterval_dvd_prod (n k : ℕ) : lcmInterval n k ∣ ∏ i ∈ Ioc n (n + k), i :=
  Finset.lcm_dvd fun _i hi => Finset.dvd_prod_of_mem _ hi

/-- The product `(n+1) ⋯ (n+k)` is positive. -/
lemma prod_Ioc_pos (n k : ℕ) : 0 < ∏ i ∈ Ioc n (n + k), i :=
  Finset.prod_pos fun _i hi => by
    simp only [Finset.mem_Ioc] at hi
    omega

/-- `lcmInterval n k` is positive. -/
lemma lcmInterval_pos (n k : ℕ) : 0 < lcmInterval n k :=
  Nat.pos_of_dvd_of_pos (lcmInterval_dvd_prod n k) (prod_Ioc_pos n k)

/-- `lcmInterval n k ≤ (n+1) ⋯ (n+k)`. -/
lemma lcmInterval_le_prod (n k : ℕ) : lcmInterval n k ≤ ∏ i ∈ Ioc n (n + k), i :=
  Nat.le_of_dvd (prod_Ioc_pos n k) (lcmInterval_dvd_prod n k)

/-- For `k > 0`, `n + k ≤ lcmInterval n k`. -/
lemma add_le_lcmInterval (n k : ℕ) (hk : 0 < k) : n + k ≤ lcmInterval n k :=
  Nat.le_of_dvd (lcmInterval_pos n k)
    (dvd_lcmInterval (by simp only [Finset.mem_Ioc]; omega))

/-- Partial result (trivial size bound): if `m + k` exceeds the product `(n+1) ⋯ (n+k)`,
then the two lcms differ. -/
theorem erdos_677_of_prod_lt (m n k : ℕ) (hk : 0 < k)
    (h : ∏ i ∈ Ioc n (n + k), i < m + k) : lcmInterval m k ≠ lcmInterval n k := by
  have h1 := lcmInterval_le_prod n k
  have h2 := add_le_lcmInterval m k hk
  omega

/-- `lcmInterval n 1 = n + 1`. -/
lemma lcmInterval_one (n : ℕ) : lcmInterval n 1 = n + 1 := by
  unfold lcmInterval
  rw [Nat.Ioc_succ_singleton, Finset.lcm_singleton]
  simp

/-- `Ioc n (n+2) = {n+1, n+2}`. -/
lemma Ioc_two (n : ℕ) : Ioc n (n + 2) = {n + 1, n + 2} := by
  ext i
  simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- `lcmInterval n 2 = (n+1)(n+2)`, since consecutive integers are coprime. -/
lemma lcmInterval_two (n : ℕ) : lcmInterval n 2 = (n + 1) * (n + 2) := by
  unfold lcmInterval
  rw [Ioc_two, Finset.lcm_insert, Finset.lcm_singleton]
  simp only [id, normalize_eq]
  have hc : Nat.Coprime (n + 1) (n + 2) := by
    rw [show n + 2 = (n + 1) + 1 from rfl, Nat.coprime_self_add_right]
    exact Nat.coprime_one_right _
  exact hc.lcm_eq_mul

/-- Partial result: the case `k = 1` of Erdős problem 677. -/
theorem erdos_677_k_one (m n : ℕ) (h : m ≥ n + 1) : lcmInterval m 1 ≠ lcmInterval n 1 := by
  rw [lcmInterval_one, lcmInterval_one]
  omega

/-- Partial result: the case `k = 2` of Erdős problem 677. -/
theorem erdos_677_k_two (m n : ℕ) (h : m ≥ n + 2) : lcmInterval m 2 ≠ lcmInterval n 2 := by
  rw [lcmInterval_two, lcmInterval_two]
  have : (n + 1) * (n + 2) < (m + 1) * (m + 2) := by nlinarith
  omega

/-- Partial result: Erdős problem 677 holds for `k ≤ 2`. -/
theorem erdos_677_k_le_two (m n k : ℕ) (hk : k > 0) (hk2 : k ≤ 2) (h : m ≥ n + k) :
    lcmInterval m k ≠ lcmInterval n k := by
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  · exact erdos_677_k_one m n h
  · exact erdos_677_k_two m n h

/-- For any `a`, either `gcd a 2 = 1` and `a` is odd, or `gcd a 2 = 2` and `a` is even. -/
lemma gcd_two_cases (a : ℕ) : (Nat.gcd a 2 = 1 ∧ ¬ 2 ∣ a) ∨ (Nat.gcd a 2 = 2 ∧ 2 ∣ a) := by
  by_cases h : 2 ∣ a
  · right
    exact ⟨Nat.gcd_eq_right h, h⟩
  · left
    refine ⟨?_, h⟩
    have hd : Nat.gcd a 2 ∣ 2 := Nat.gcd_dvd_right a 2
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
    · exact h1
    · exact absurd (h2 ▸ Nat.gcd_dvd_left a 2) h

/-- `Ioc n (n+3) = {n+1, n+2, n+3}`. -/
lemma Ioc_three (n : ℕ) : Ioc n (n + 3) = {n + 1, n + 2, n + 3} := by
  ext i
  simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- `lcmInterval n 3 = lcm (n+1) ((n+2)(n+3))`. -/
lemma lcmInterval_three_eq (n : ℕ) :
    lcmInterval n 3 = Nat.lcm (n + 1) ((n + 2) * (n + 3)) := by
  unfold lcmInterval
  rw [Ioc_three, Finset.lcm_insert, Finset.lcm_insert, Finset.lcm_singleton]
  simp only [id, normalize_eq]
  have hc : Nat.Coprime (n + 2) (n + 3) := by
    rw [show n + 3 = (n + 2) + 1 from rfl, Nat.coprime_self_add_right]
    exact Nat.coprime_one_right _
  have : Nat.lcm (n + 2) (n + 3) = (n + 2) * (n + 3) := hc.lcm_eq_mul
  rw [← this]
  rfl

/-- `gcd (n+1) ((n+2)(n+3)) = gcd (n+1) 2`. -/
lemma gcd_three (n : ℕ) : Nat.gcd (n + 1) ((n + 2) * (n + 3)) = Nat.gcd (n + 1) 2 := by
  have hc : Nat.Coprime (n + 2) (n + 1) := by
    rw [Nat.coprime_comm, show n + 2 = (n + 1) + 1 from rfl, Nat.coprime_self_add_right]
    exact Nat.coprime_one_right _
  rw [Nat.Coprime.gcd_mul_left_cancel_right _ hc, show n + 3 = 2 + (n + 1) by ring,
    Nat.gcd_add_self_right]

/-- `lcmInterval n 3 · gcd (n+1) 2 = (n+1)(n+2)(n+3)`. -/
lemma lcmInterval_three_mul_gcd (n : ℕ) :
    lcmInterval n 3 * Nat.gcd (n + 1) 2 = (n + 1) * (n + 2) * (n + 3) := by
  rw [lcmInterval_three_eq, ← gcd_three, mul_comm, Nat.gcd_mul_lcm, ← mul_assoc]

/-- Partial result for `k = 3`: an equality `lcmInterval m 3 = lcmInterval n 3` with
`m ≥ n + 3` forces `(m+1)(m+2)(m+3) = 2 (n+1)(n+2)(n+3)` with `m` odd and `n` even.
(Whether this Diophantine equation has such solutions is not resolved here.) -/
theorem erdos_677_k_three_reduction (m n : ℕ) (h : m ≥ n + 3)
    (heq : lcmInterval m 3 = lcmInterval n 3) :
    (m + 1) * (m + 2) * (m + 3) = 2 * ((n + 1) * (n + 2) * (n + 3)) ∧
      2 ∣ m + 1 ∧ ¬ 2 ∣ n + 1 := by
  have hm := lcmInterval_three_mul_gcd m
  have hn := lcmInterval_three_mul_gcd n
  have hlt : (n + 1) * (n + 2) * (n + 3) < (m + 1) * (m + 2) * (m + 3) :=
    Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (by omega) (by omega)) (by omega)
  rw [heq] at hm
  generalize lcmInterval n 3 = L at hm hn
  generalize (m + 1) * (m + 2) * (m + 3) = Pm at hm hlt ⊢
  generalize (n + 1) * (n + 2) * (n + 3) = Pn at hn hlt ⊢
  rcases gcd_two_cases (m + 1) with ⟨gm, pm⟩ | ⟨gm, pm⟩ <;>
  rcases gcd_two_cases (n + 1) with ⟨gn, pn⟩ | ⟨gn, pn⟩ <;>
  rw [gm] at hm <;> rw [gn] at hn
  · omega
  · omega
  · exact ⟨by omega, pm, pn⟩
  · omega

/-- CONJECTURE (Erdős problem 677, open), stated as a `Prop` with no proof claimed:
`M(m,k) ≠ M(n,k)` whenever `m ≥ n + k`. -/
def Erdos677Conjecture : Prop :=
    ∀ (m n k : ℕ), k > 0 → m ≥ n + k → lcmInterval m k ≠ lcmInterval n k

end Erdos677
