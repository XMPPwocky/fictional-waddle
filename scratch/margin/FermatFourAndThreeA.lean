import Mathlib

/-!
# Fermat's Last Theorem for exponents 3 and 4, and multiples of 4

All results are obtained from Mathlib (`Mathlib.NumberTheory.FLT.Basic`,
`Mathlib.NumberTheory.FLT.Four`, `Mathlib.NumberTheory.FLT.Three`).

Mathlib names used:
* `FermatLastTheoremFor`, `FermatLastTheoremWith` (definitions, FLT/Basic)
* `fermatLastTheoremFour : FermatLastTheoremFor 4` (FLT/Four)
* `not_fermat_42 : a ≠ 0 → b ≠ 0 → a ^ 4 + b ^ 4 ≠ c ^ 2` over `ℤ` (FLT/Four)
* `fermatLastTheoremThree : FermatLastTheoremFor 3` (FLT/Three)
* `FermatLastTheoremFor.mono : m ∣ n → FermatLastTheoremFor m → FermatLastTheoremFor n`
* `fermatLastTheoremFor_iff_int` (FLT/Basic)

PROVED:
* `flt_four` : `FermatLastTheoremFor 4`.
* `flt_four_pos` : no positive naturals `x y z` with `x ^ 4 + y ^ 4 = z ^ 4`.
* `flt_four_int` : no nonzero integers `x y z` with `x ^ 4 + y ^ 4 = z ^ 4`.
* `no_four_four_two` : no integers `x y z` with `x, y ≠ 0` and `x ^ 4 + y ^ 4 = z ^ 2`
  (then `z ≠ 0` automatically; `no_four_four_two_nonzero` is the all-nonzero form).
* `flt_three` : `FermatLastTheoremFor 3`.
* `flt_three_pos` : no positive naturals `x y z` with `x ^ 3 + y ^ 3 = z ^ 3`.
* `flt_four_mul` : `FermatLastTheoremFor (4 * k)` for every `k ≥ 1`
  (via `FermatLastTheoremFor.mono`).
* `flt_four_mul_direct` : the same, by a direct reduction `x^(4k) = (x^k)^4`
  without `FermatLastTheoremFor.mono`.
* `flt_three_mul` : `FermatLastTheoremFor (3 * k)` for every `k ≥ 1`.

INTERPRETED:
* "positive integers x, y, z" in (1) is read both as positive naturals (`flt_four_pos`,
  which is Mathlib's `FermatLastTheoremFor 4` with `≠ 0` replaced by `0 <`) and as nonzero
  integers (`flt_four_int`, a strictly stronger statement).
* "nonzero integers" in (2) is read as `x y z : ℤ` all nonzero; the stronger form needing
  only `x, y ≠ 0` is also proved.
-/

namespace FermatFourAndThreeA

/-- (1) Fermat's Last Theorem for exponent 4. -/
theorem flt_four : FermatLastTheoremFor 4 := fermatLastTheoremFour

/-- (1) No positive naturals `x, y, z` satisfy `x ^ 4 + y ^ 4 = z ^ 4`. -/
theorem flt_four_pos :
    ¬ ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 4 + y ^ 4 = z ^ 4 := by
  rintro ⟨x, y, z, hx, hy, hz, h⟩
  exact fermatLastTheoremFour x y z hx.ne' hy.ne' hz.ne' h

/-- (1) No nonzero integers `x, y, z` satisfy `x ^ 4 + y ^ 4 = z ^ 4`. -/
theorem flt_four_int :
    ∀ x y z : ℤ, x ≠ 0 → y ≠ 0 → z ≠ 0 → x ^ 4 + y ^ 4 ≠ z ^ 4 :=
  fermatLastTheoremFor_iff_int.mp fermatLastTheoremFour

/-- (2) `x ^ 4 + y ^ 4 = z ^ 2` has no integer solutions with `x, y ≠ 0`. -/
theorem no_four_four_two :
    ∀ x y z : ℤ, x ≠ 0 → y ≠ 0 → x ^ 4 + y ^ 4 ≠ z ^ 2 :=
  fun _ _ _ hx hy => not_fermat_42 hx hy

/-- (2) `x ^ 4 + y ^ 4 = z ^ 2` has no solutions in nonzero integers. -/
theorem no_four_four_two_nonzero :
    ¬ ∃ x y z : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x ^ 4 + y ^ 4 = z ^ 2 := by
  rintro ⟨x, y, z, hx, hy, -, h⟩
  exact not_fermat_42 hx hy h

/-- (3) Fermat's Last Theorem for exponent 3. -/
theorem flt_three : FermatLastTheoremFor 3 := fermatLastTheoremThree

/-- (3) No positive naturals `x, y, z` satisfy `x ^ 3 + y ^ 3 = z ^ 3`. -/
theorem flt_three_pos :
    ¬ ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 3 + y ^ 3 = z ^ 3 := by
  rintro ⟨x, y, z, hx, hy, hz, h⟩
  exact fermatLastTheoremThree x y z hx.ne' hy.ne' hz.ne' h

/-- (4) Fermat's Last Theorem for every exponent `4 * k` with `k ≥ 1`. -/
theorem flt_four_mul (k : ℕ) (_hk : 1 ≤ k) : FermatLastTheoremFor (4 * k) :=
  FermatLastTheoremFor.mono (Dvd.intro k rfl) fermatLastTheoremFour

/-- (4) The same reduction to exponent 4, done directly. -/
theorem flt_four_mul_direct (k : ℕ) (_hk : 1 ≤ k) : FermatLastTheoremFor (4 * k) := by
  intro a b c ha hb hc h
  refine fermatLastTheoremFour (a ^ k) (b ^ k) (c ^ k)
    (pow_ne_zero _ ha) (pow_ne_zero _ hb) (pow_ne_zero _ hc) ?_
  simpa only [← pow_mul, mul_comm k 4] using h

/-- Fermat's Last Theorem for every exponent `3 * k` with `k ≥ 1`. -/
theorem flt_three_mul (k : ℕ) (_hk : 1 ≤ k) : FermatLastTheoremFor (3 * k) :=
  FermatLastTheoremFor.mono (Dvd.intro k rfl) fermatLastTheoremThree

end FermatFourAndThreeA
