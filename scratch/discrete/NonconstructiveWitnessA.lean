import Mathlib

/-!
# Irrational powers with rational value: nonconstructive and explicit witnesses

PROVED
* `sqrt_two_pow_sqrt_two_pow_sqrt_two` : `(√2 ^ √2) ^ √2 = 2` (real `rpow`).
* `witness_dichotomy` : either `(√2, √2)` is a witness (`√2 ^ √2` rational), or
  `(√2 ^ √2, √2)` is a witness (`√2 ^ √2` irrational and `(√2 ^ √2) ^ √2 = 2`).
* `exists_irrational_rpow_rat` (target) :
  `∃ a b : ℝ, Irrational a ∧ Irrational b ∧ ∃ q : ℚ, a ^ b = q`,
  proved by the excluded-middle case split on `Irrational (√2 ^ √2)`.
* `irrational_logb_two_three` : `Irrational (Real.logb 2 3)` (not in Mathlib; proved here
  from `2 ^ n ≠ 3 ^ d` for `n ≥ 1` by parity).
* `irrational_two_mul_logb_two_three` : `Irrational (2 * Real.logb 2 3)`.
* `sqrt_two_rpow_two_mul_logb_two_three` : `√2 ^ (2 * Real.logb 2 3) = 3`.
* `explicit_irrational_rpow_rat` (constructive companion) :
  `Irrational √2 ∧ Irrational (2 * Real.logb 2 3) ∧ √2 ^ (2 * Real.logb 2 3) = ((3 : ℚ) : ℝ)`.

INTERPRETED
* `#print axioms exists_irrational_rpow_rat` reports `propext, Classical.choice, Quot.sound`.
  `Classical.choice` enters in two ways: through Mathlib's classical construction of `ℝ`
  and `rpow` (present in every theorem in this file), and through the `by_cases` on the
  undecided proposition `Irrational (√2 ^ √2)`, which is an appeal to excluded middle
  (`Classical.em`, derived from `Classical.choice`). The second use is the one that makes
  the proof nonconstructive: the proof term is a case analysis on a proof of
  `P ∨ ¬P` that carries no information about which disjunct holds, so the theorem
  establishes existence without identifying which of the two pairs is the witness.
  The axiom printout cannot separate the two sources, since both reduce to the same axiom.
* Which branch actually holds (`√2 ^ √2` is irrational, indeed transcendental) follows from
  the Gelfond-Schneider theorem, which is not in Mathlib; this file does not decide it.
* The companion `explicit_irrational_rpow_rat` names the pair `a = √2`, `b = 2 * log₂ 3`
  outright. Its axiom footprint is the same (`Classical.choice` via classical `ℝ`), but no
  case split on an undecided proposition is used to choose the witness: the witness is a
  definite term and the value `3` is computed.
-/

namespace NonconstructiveWitnessA

open Real

theorem sqrt_two_pow_sqrt_two_pow_sqrt_two : ((√2 : ℝ) ^ (√2 : ℝ)) ^ (√2 : ℝ) = 2 := by
  rw [← Real.rpow_mul (Real.sqrt_nonneg 2), Real.mul_self_sqrt (by norm_num),
    Real.rpow_two, Real.sq_sqrt (by norm_num)]

theorem witness_dichotomy :
    (Irrational (√2 : ℝ) ∧ Irrational (√2 : ℝ) ∧ ∃ q : ℚ, (√2 : ℝ) ^ (√2 : ℝ) = q) ∨
    (Irrational ((√2 : ℝ) ^ (√2 : ℝ)) ∧ Irrational (√2 : ℝ) ∧
      ∃ q : ℚ, ((√2 : ℝ) ^ (√2 : ℝ)) ^ (√2 : ℝ) = q) := by
  by_cases h : Irrational ((√2 : ℝ) ^ (√2 : ℝ))
  · refine Or.inr ⟨h, irrational_sqrt_two, 2, ?_⟩
    rw [sqrt_two_pow_sqrt_two_pow_sqrt_two]
    norm_num
  · refine Or.inl ⟨irrational_sqrt_two, irrational_sqrt_two, ?_⟩
    unfold Irrational at h
    rw [not_not] at h
    obtain ⟨q, hq⟩ := h
    exact ⟨q, hq.symm⟩

theorem exists_irrational_rpow_rat :
    ∃ a b : ℝ, Irrational a ∧ Irrational b ∧ ∃ q : ℚ, a ^ b = q := by
  rcases witness_dichotomy with ⟨ha, hb, hq⟩ | ⟨ha, hb, hq⟩
  · exact ⟨_, _, ha, hb, hq⟩
  · exact ⟨_, _, ha, hb, hq⟩

theorem irrational_logb_two_three : Irrational (Real.logb 2 3) := by
  rintro ⟨q, hq⟩
  have hpos : (0 : ℝ) < q := hq ▸ Real.logb_pos (by norm_num) (by norm_num)
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hpos
  have hnum : 0 < q.num := Rat.num_pos.mpr hq0
  have h3 : (2 : ℝ) ^ (q : ℝ) = 3 := by
    rw [hq]
    exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  have hcast : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
    have e : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg hnum.le
    rw [← Int.cast_natCast, e]
  have hqd : (q : ℝ) * (q.den : ℝ) = ((q.num.toNat : ℕ) : ℝ) := by
    rw [hcast]
    exact_mod_cast Rat.mul_den_eq_num q
  have key : (2 : ℝ) ^ q.num.toNat = 3 ^ q.den := by
    rw [← Real.rpow_natCast, ← hqd, Real.rpow_mul (by norm_num), h3, Real.rpow_natCast]
  have keyN : 2 ^ q.num.toNat = 3 ^ q.den := by exact_mod_cast key
  have hn : q.num.toNat ≠ 0 := by omega
  have h2 : 2 ∣ 3 ^ q.den := keyN ▸ dvd_pow_self 2 hn
  have : 2 ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
  omega

theorem irrational_two_mul_logb_two_three : Irrational (2 * Real.logb 2 3) := by
  simpa using irrational_logb_two_three.natCast_mul (m := 2) two_ne_zero

theorem sqrt_two_rpow_two_mul_logb_two_three : (√2 : ℝ) ^ (2 * Real.logb 2 3) = 3 := by
  rw [Real.rpow_mul (Real.sqrt_nonneg 2), Real.rpow_two, Real.sq_sqrt (by norm_num)]
  exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

theorem explicit_irrational_rpow_rat :
    Irrational (√2 : ℝ) ∧ Irrational (2 * Real.logb 2 3) ∧
      (√2 : ℝ) ^ (2 * Real.logb 2 3) = ((3 : ℚ) : ℝ) := by
  refine ⟨irrational_sqrt_two, irrational_two_mul_logb_two_three, ?_⟩
  rw [sqrt_two_rpow_two_mul_logb_two_three]
  norm_num

end NonconstructiveWitnessA
