import Mathlib

open Nat

/-!
# Erdős problem 396

* CONJECTURE (open, no proof claimed): `Erdos396Conjecture`.
* Unconditional: `works_of_le`, `dvd_45153`, and `erdos_396_le_four` (the instance of the
  conjecture for every `k ≤ 4`).
-/

namespace Erdos396

/-- CONJECTURE (Erdős problem 396, open): for every `k` there is `n` with
`∏_{0 ≤ i ≤ k} (n - i)` dividing `binom(2n, n)`. -/
def Erdos396Conjecture : Prop := ∀ k : ℕ, ∃ n : ℕ, descFactorial n (k + 1) ∣ centralBinom n

/-! ## Partial results -/

/-- If `n` works for `k`, it works for every `j ≤ k`. -/
theorem works_of_le {n j k : ℕ} (hjk : j ≤ k)
    (h : descFactorial n (k + 1) ∣ centralBinom n) :
    descFactorial n (j + 1) ∣ centralBinom n :=
  (Dvd.intro_left _ (descFactorial_mul_descFactorial (n := n) (by omega : j + 1 ≤ k + 1))).trans h

/-- `n = 45153` (the smallest witness for `k = 4`, found by computer search):
`45153 · 45152 · 45151 · 45150 · 45149 ∣ binom(90306, 45153)`. Checked by kernel computation. -/
theorem dvd_45153 : descFactorial 45153 5 ∣ centralBinom 45153 := by
  rw [centralBinom_eq_two_mul_choose, choose_eq_factorial_div_factorial (by norm_num)]
  decide +kernel

/-- The instance of `Erdos396Conjecture` holds for every `k ≤ 4`, with the single witness `n = 45153`. -/
theorem erdos_396_le_four (k : ℕ) (hk : k ≤ 4) :
    ∃ n : ℕ, descFactorial n (k + 1) ∣ centralBinom n :=
  ⟨45153, works_of_le hk dvd_45153⟩

end Erdos396
