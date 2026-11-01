import Mathlib

/-!
# Fermat's Last Theorem for exponents 3, 4 and multiples of 4, from Mathlib

All results are derived from Mathlib v4.35 lemmas; nothing is reproved from scratch.

Mathlib names used:
* `FermatLastTheoremFor`, `FermatLastTheoremWith` (Mathlib.NumberTheory.FLT.Basic)
* `fermatLastTheoremFour : FermatLastTheoremFor 4` (Mathlib.NumberTheory.FLT.Four)
* `not_fermat_42 : a ≠ 0 → b ≠ 0 → a ^ 4 + b ^ 4 ≠ c ^ 2` over `ℤ` (Mathlib.NumberTheory.FLT.Four)
* `fermatLastTheoremThree : FermatLastTheoremFor 3` (Mathlib.NumberTheory.FLT.Three)
* `FermatLastTheoremFor.mono : m ∣ n → FermatLastTheoremFor m → FermatLastTheoremFor n`
* `fermatLastTheoremFor_iff_int`, `fermatLastTheoremFor_iff_rat`

PROVED:
* `flt_four` : `FermatLastTheoremFor 4`.
* `flt_four_pos` : no positive naturals `x y z` with `x ^ 4 + y ^ 4 = z ^ 4`.
* `flt_four_int` : no nonzero integers `x y z` with `x ^ 4 + y ^ 4 = z ^ 4`.
* `no_quartic_sum_square` : no integers `x y z` with `x ≠ 0`, `y ≠ 0` and
  `x ^ 4 + y ^ 4 = z ^ 2` (in particular none in nonzero integers).
* `no_quartic_sum_square_nonzero` : the same with all three nonzero.
* `flt_three` : `FermatLastTheoremFor 3`.
* `flt_three_pos` : no positive naturals `x y z` with `x ^ 3 + y ^ 3 = z ^ 3`.
* `flt_three_int` : no nonzero integers `x y z` with `x ^ 3 + y ^ 3 = z ^ 3`.
* `flt_four_mul` : `FermatLastTheoremFor (4 * k)` for every `k ≥ 1`, via `FermatLastTheoremFor.mono`.
* `flt_four_mul_direct` : the same, by the direct reduction `x ^ (4k) = (x ^ k) ^ 4`.
* `flt_three_mul` : `FermatLastTheoremFor (3 * k)` for every `k ≥ 1`.

INTERPRETED:
* "positive integers" in (1) is read over `ℕ` with `0 < x` etc.; Mathlib's
  `FermatLastTheoremFor n` is the statement over `ℕ` with nonzero entries, which is equivalent.
  The integer version is also given.
* (2) is Mathlib's `not_fermat_42`, which needs only `x ≠ 0` and `y ≠ 0`; the
  three-nonzero form is a weakening.
* In (4) the hypothesis `k ≥ 1` is kept as stated, although the proofs do not use it
  (`k = 0` gives exponent `0`, which is `fermatLastTheoremFor_zero`).
-/

namespace FermatFourAndThreeB

/-- (1) Fermat's Last Theorem for exponent 4 (Mathlib: `fermatLastTheoremFour`). -/
theorem flt_four : FermatLastTheoremFor 4 := fermatLastTheoremFour

/-- (1) No positive naturals with `x ^ 4 + y ^ 4 = z ^ 4`. -/
theorem flt_four_pos :
    ¬ ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 4 + y ^ 4 = z ^ 4 := by
  rintro ⟨x, y, z, hx, hy, hz, h⟩
  exact fermatLastTheoremFour x y z hx.ne' hy.ne' hz.ne' h

/-- (1) No nonzero integers with `x ^ 4 + y ^ 4 = z ^ 4`. -/
theorem flt_four_int (x y z : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x ^ 4 + y ^ 4 ≠ z ^ 4 :=
  (fermatLastTheoremFor_iff_int.mp fermatLastTheoremFour) x y z hx hy hz

/-- (2) `x ^ 4 + y ^ 4 = z ^ 2` has no integer solution with `x, y` nonzero
(Mathlib: `not_fermat_42`). -/
theorem no_quartic_sum_square (x y z : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ 4 + y ^ 4 ≠ z ^ 2 :=
  not_fermat_42 hx hy

/-- (2) `x ^ 4 + y ^ 4 = z ^ 2` has no solution in nonzero integers. -/
theorem no_quartic_sum_square_nonzero :
    ¬ ∃ x y z : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x ^ 4 + y ^ 4 = z ^ 2 := by
  rintro ⟨x, y, z, hx, hy, _, h⟩
  exact not_fermat_42 hx hy h

/-- (3) Fermat's Last Theorem for exponent 3 (Mathlib: `fermatLastTheoremThree`). -/
theorem flt_three : FermatLastTheoremFor 3 := fermatLastTheoremThree

/-- (3) No positive naturals with `x ^ 3 + y ^ 3 = z ^ 3`. -/
theorem flt_three_pos :
    ¬ ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 3 + y ^ 3 = z ^ 3 := by
  rintro ⟨x, y, z, hx, hy, hz, h⟩
  exact fermatLastTheoremThree x y z hx.ne' hy.ne' hz.ne' h

/-- (3) No nonzero integers with `x ^ 3 + y ^ 3 = z ^ 3`. -/
theorem flt_three_int (x y z : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x ^ 3 + y ^ 3 ≠ z ^ 3 :=
  (fermatLastTheoremFor_iff_int.mp fermatLastTheoremThree) x y z hx hy hz

/-- (4) Every multiple of 4 is a Fermat exponent (Mathlib: `FermatLastTheoremFor.mono`). -/
theorem flt_four_mul (k : ℕ) (_hk : 1 ≤ k) : FermatLastTheoremFor (4 * k) :=
  FermatLastTheoremFor.mono (Dvd.intro k rfl) fermatLastTheoremFour

/-- (4) The same reduction proved directly: `x ^ (4k) = (x ^ k) ^ 4`. -/
theorem flt_four_mul_direct (k : ℕ) (_hk : 1 ≤ k) : FermatLastTheoremFor (4 * k) := by
  intro a b c ha hb hc h
  have h' : (a ^ k) ^ 4 + (b ^ k) ^ 4 = (c ^ k) ^ 4 := by
    simpa only [← pow_mul, Nat.mul_comm k 4] using h
  exact fermatLastTheoremFour (a ^ k) (b ^ k) (c ^ k)
    (pow_ne_zero k ha) (pow_ne_zero k hb) (pow_ne_zero k hc) h'

/-- Every multiple of 3 is a Fermat exponent. -/
theorem flt_three_mul (k : ℕ) (_hk : 1 ≤ k) : FermatLastTheoremFor (3 * k) :=
  FermatLastTheoremFor.mono (Dvd.intro k rfl) fermatLastTheoremThree

end FermatFourAndThreeB
