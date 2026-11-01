import Mathlib

namespace Erdos850

/-! ### Erdős problem 850 (open): conjecture and partial results

* CONJECTURE, stated as a `Prop` with no proof claimed: `Erdos850Conjecture`.
* Unconditional: `two_term_75_1215` and `two_term_family` (solutions of the two-term
  version), `two_term_family_fails_third` (that family never satisfies the third condition),
  and `solution_ge_two` (any solution has `x, y ≥ 2`). -/

/-- CONJECTURE (Erdős problem 850, open), stated as a `Prop` with no proof claimed:
there exist distinct `x y` such that each of the pairs `x, y`, `x+1, y+1` and `x+2, y+2`
has the same set of prime factors. -/
def Erdos850Conjecture : Prop :=
    ∃ x y : ℕ, x ≠ y ∧ x.primeFactors = y.primeFactors
      ∧ (x + 1).primeFactors = (y + 1).primeFactors
      ∧ (x + 2).primeFactors = (y + 2).primeFactors

/-! ## Partial results -/

/-- The two-term version has the sporadic solution `(75, 1215)`:
`75 = 3 * 5^2`, `1215 = 3^5 * 5`, `76 = 2^2 * 19`, `1216 = 2^6 * 19`. -/
theorem two_term_75_1215 :
    (75 : ℕ).primeFactors = (1215 : ℕ).primeFactors
      ∧ (75 + 1 : ℕ).primeFactors = (1215 + 1 : ℕ).primeFactors := by
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h2 : Nat.Prime 2 := by norm_num
  have h19 : Nat.Prime 19 := by norm_num
  constructor
  · rw [show (75 : ℕ) = 3 * 5 ^ 2 by norm_num, show (1215 : ℕ) = 3 ^ 5 * 5 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) h5, Nat.primeFactors_prime_pow (by norm_num) h3,
      h3.primeFactors, h5.primeFactors]
  · rw [show (75 + 1 : ℕ) = 2 ^ 2 * 19 by norm_num, show (1215 + 1 : ℕ) = 2 ^ 6 * 19 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) h2, Nat.primeFactors_prime_pow (by norm_num) h2]

/-- The classical infinite family for the two-term version: for `k ≥ 2`,
`x = 2^k - 2` and `y = 2^k * (2^k - 2)` are distinct, with `x, y` and `x+1, y+1` having
the same prime factors (`y + 1 = (x + 1)^2`). -/
theorem two_term_family (k : ℕ) (hk : 2 ≤ k) :
    (2 ^ k - 2) ≠ 2 ^ k * (2 ^ k - 2)
      ∧ (2 ^ k - 2).primeFactors = (2 ^ k * (2 ^ k - 2)).primeFactors
      ∧ (2 ^ k - 2 + 1).primeFactors = (2 ^ k * (2 ^ k - 2) + 1).primeFactors := by
  have hk0 : k ≠ 0 := by omega
  have h4dvd : 4 ∣ 2 ^ k := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 2 hk
  have hpf : (2 ^ k).primeFactors = {2} := Nat.primeFactors_prime_pow hk0 Nat.prime_two
  have ha4 : 4 ≤ 2 ^ k := Nat.le_of_dvd (by positivity) h4dvd
  obtain ⟨b, hb⟩ : ∃ b, 2 ^ k = b + 2 := ⟨2 ^ k - 2, by omega⟩
  rw [hb] at hpf h4dvd ha4 ⊢
  simp only [Nat.add_sub_cancel]
  have hb0 : b ≠ 0 := by omega
  have h2b : 2 ∣ b := by
    have : 2 ∣ b + 2 := dvd_trans (by norm_num) h4dvd
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : 1 * b = (b + 2) * b := by rw [one_mul]; exact h
    have := Nat.eq_of_mul_eq_mul_right (by omega) this
    omega
  · rw [Nat.primeFactors_mul (by omega) hb0, hpf]
    have h2mem : 2 ∈ b.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2b, hb0⟩
    exact (Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr h2mem)).symm
  · rw [show (b + 2) * b + 1 = (b + 1) ^ 2 by ring, Nat.primeFactors_pow _ (by norm_num)]

/-- The family `x = 2^k - 2`, `y = 2^k * (2^k - 2)` (`k ≥ 2`) never satisfies the third
condition: `x + 2 = 2^k` has prime factors `{2}`, while `y + 2 ≡ 2 (mod 4)` and `y + 2 > 4`,
so `y + 2` is not a power of `2` and has an odd prime factor. -/
theorem two_term_family_fails_third (k : ℕ) (hk : 2 ≤ k) :
    (2 ^ k - 2 + 2).primeFactors ≠ (2 ^ k * (2 ^ k - 2) + 2).primeFactors := by
  have hk0 : k ≠ 0 := by omega
  have h4dvd : 4 ∣ 2 ^ k := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 2 hk
  have hpf : (2 ^ k).primeFactors = {2} := Nat.primeFactors_prime_pow hk0 Nat.prime_two
  have ha4 : 4 ≤ 2 ^ k := Nat.le_of_dvd (by positivity) h4dvd
  obtain ⟨b, hb⟩ : ∃ b, 2 ^ k = b + 2 := ⟨2 ^ k - 2, by omega⟩
  rw [hb] at hpf h4dvd ha4 ⊢
  simp only [Nat.add_sub_cancel]
  rw [hpf]
  intro h
  obtain ⟨c, hc⟩ := h4dvd
  have hn0 : (b + 2) * b + 2 ≠ 0 := by omega
  -- every prime factor of `(b + 2) * b + 2` is `2`, so it is a power of `2`
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hn0 (p := 2) (by
    intro d hd hdn
    have : d ∈ ((b + 2) * b + 2).primeFactors := Nat.mem_primeFactors.mpr ⟨hd, hdn, hn0⟩
    rw [← h] at this
    simpa using this)
  -- `(b + 2) * b + 2 ≡ 2 (mod 4)`, since `4 ∣ b + 2`
  have hmul : (b + 2) * b = 4 * (c * b) := by rw [hc, mul_assoc]
  have hn_gt : 4 < (b + 2) * b + 2 := by
    have : 4 * 2 ≤ (b + 2) * b := Nat.mul_le_mul ha4 (by omega)
    omega
  -- a power of `2` exceeding `4` is divisible by `4`
  generalize hj : ((b + 2) * b + 2).primeFactorsList.length = j at hpow
  have hj2 : 2 ≤ j := by
    by_contra hj'
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp at hpow <;> omega
  have h4 : 4 ∣ (b + 2) * b + 2 := by
    rw [hpow, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 2 hj2
  omega

/-- Any solution of the three-term problem has `x ≥ 2` and `y ≥ 2`
(already the first two conditions force this: `0` and `1` both have empty prime factor
set, while `2` has prime factor set `{2}`). -/
theorem solution_ge_two {x y : ℕ} (hxy : x ≠ y) (h0 : x.primeFactors = y.primeFactors)
    (h1 : (x + 1).primeFactors = (y + 1).primeFactors) : 2 ≤ x ∧ 2 ≤ y := by
  have h2 : Nat.primeFactors 2 = {2} := Nat.prime_two.primeFactors
  have key : ∀ u v : ℕ, u ≠ v → u.primeFactors = v.primeFactors →
      (u + 1).primeFactors = (v + 1).primeFactors → 2 ≤ u := by
    intro u v huv h0 h1
    by_contra hu
    have hv : v.primeFactors = ∅ := by
      rw [← h0]; interval_cases u <;> simp
    rw [Nat.primeFactors_eq_empty] at hv
    have hu' : u = 0 ∨ u = 1 := by omega
    rcases hv with rfl | rfl <;> rcases hu' with rfl | rfl
    · exact huv rfl
    · simp [h2] at h1
    · simp [h2] at h1
    · exact huv rfl
  exact ⟨key x y hxy h0 h1, key y x (Ne.symm hxy) h0.symm h1.symm⟩

end Erdos850
