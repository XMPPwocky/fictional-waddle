import Mathlib

/-!
# Irrational `a`, `b` with `a ^ b` rational

PROVED:
* `exists_irrational_rpow_rat` : `∃ a b : ℝ, Irrational a ∧ Irrational b ∧ ∃ q : ℚ, a ^ b = q`,
  by the classical case split on `Irrational (√2 ^ √2)`. If `√2 ^ √2` is rational, take
  `a = b = √2`. Otherwise take `a = √2 ^ √2`, `b = √2`; then
  `(√2 ^ √2) ^ √2 = √2 ^ (√2 * √2) = √2 ^ 2 = 2` (`Real.rpow_mul`, `0 ≤ √2`).
* `irrational_logb_two_three` : `Irrational (Real.logb 2 3)`
  (if `logb 2 3 = n / d` with `d > 0` then `n > 0` and `2 ^ n = 3 ^ d` in `ℕ`, contradicting parity).
* `irrational_two_mul_logb_two_three` : `Irrational (2 * Real.logb 2 3)`.
* `sqrt_two_rpow_two_mul_logb_two_three` : `√2 ^ (2 * Real.logb 2 3) = 3`.
* `exists_irrational_rpow_rat_explicit` : the same existential as `exists_irrational_rpow_rat`,
  with the witnesses `a = √2`, `b = 2 * logb 2 3`, `q = 3` written into the proof term.

INTERPRETED:
* `exists_irrational_rpow_rat` uses `by_cases` on `Irrational (√2 ^ √2)`, i.e. excluded middle
  (`Classical.em`, derived from `Classical.choice`). The proof term contains both candidate pairs
  and does not determine which one is the witness. `#print axioms exists_irrational_rpow_rat`
  reports `[propext, Classical.choice, Quot.sound]`.
* The explicit companion also reports `[propext, Classical.choice, Quot.sound]`: Mathlib's `ℝ`,
  `Real.rpow`, `Real.log` and `Irrational` are built with classical logic throughout, so the axiom
  list does not separate the two proofs. The difference is in the witness: in the companion the pair
  `(√2, 2 * logb 2 3)` and the value `3` are explicit terms, and no case split on an undecided
  proposition is made. (Gelfond–Schneider would show `√2 ^ √2` is irrational, so the second branch
  is the true one; that theorem is not used here.)
-/

namespace NonconstructiveWitnessB

open Real

/-- There exist irrational reals `a`, `b` with `a ^ b` rational (classical case split). -/
theorem exists_irrational_rpow_rat :
    ∃ a b : ℝ, Irrational a ∧ Irrational b ∧ ∃ q : ℚ, a ^ b = q := by
  by_cases h : Irrational (√2 ^ √2)
  · refine ⟨√2 ^ √2, √2, h, irrational_sqrt_two, 2, ?_⟩
    rw [← Real.rpow_mul (Real.sqrt_nonneg 2), Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_two, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  · obtain ⟨q, hq⟩ := exists_rat_of_not_irrational h
    exact ⟨√2, √2, irrational_sqrt_two, irrational_sqrt_two, q, hq⟩

/-- `log₂ 3` is irrational. -/
theorem irrational_logb_two_three : Irrational (Real.logb 2 3) := by
  rintro ⟨q, hq⟩
  have hpos : (0 : ℝ) < q := hq ▸ Real.logb_pos (by norm_num) (by norm_num)
  have hnum : 0 < q.num := Rat.num_pos.mpr (by exact_mod_cast hpos)
  have h1 : (2 : ℝ) ^ (q : ℝ) = 3 := by
    rw [hq]; exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  have h2 : (2 : ℝ) ^ ((q : ℝ) * (q.den : ℝ)) = 3 ^ q.den := by
    rw [Real.rpow_mul (by norm_num), h1, Real.rpow_natCast]
  have h3 : (q : ℝ) * (q.den : ℝ) = ((q.num.toNat : ℕ) : ℝ) := by
    have e : ((q * q.den : ℚ) : ℝ) = (q.num : ℝ) := by
      rw [Rat.mul_den_eq_num]; simp
    have e2 : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg hnum.le
    rw [← e2] at e
    push_cast at e
    exact e
  rw [h3, Real.rpow_natCast] at h2
  have h4 : (2 : ℕ) ^ q.num.toNat = 3 ^ q.den := by exact_mod_cast h2
  have hn : q.num.toNat ≠ 0 := by omega
  have hev : Even ((2 : ℕ) ^ q.num.toNat) := Nat.even_pow.mpr ⟨even_two, hn⟩
  rw [h4] at hev
  have := (Nat.even_pow.mp hev).1
  exact absurd this (by decide)

/-- `2 * log₂ 3` is irrational. -/
theorem irrational_two_mul_logb_two_three : Irrational (2 * Real.logb 2 3) := by
  have := irrational_logb_two_three.natCast_mul (m := 2) two_ne_zero
  simpa using this

/-- `√2 ^ (2 * log₂ 3) = 3`. -/
theorem sqrt_two_rpow_two_mul_logb_two_three : √2 ^ (2 * Real.logb 2 3) = 3 := by
  rw [Real.rpow_mul (Real.sqrt_nonneg 2), Real.rpow_two, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]

/-- Explicit witnesses: `a = √2`, `b = 2 * log₂ 3`, `a ^ b = 3`. -/
theorem exists_irrational_rpow_rat_explicit :
    ∃ a b : ℝ, Irrational a ∧ Irrational b ∧ ∃ q : ℚ, a ^ b = q :=
  ⟨√2, 2 * Real.logb 2 3, irrational_sqrt_two, irrational_two_mul_logb_two_three, 3, by
    rw [sqrt_two_rpow_two_mul_logb_two_three]; norm_num⟩

end NonconstructiveWitnessB
