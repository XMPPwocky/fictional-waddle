import Mathlib

/-!
# Why a piano can't be tuned perfectly

PROVED:
* `fifths_never_close`: no positive number of perfect fifths (3/2) equals a whole number of octaves (2), because
  3^a is odd and 2^(a + b) is even: (3/2)^a = 2^b is impossible for a > 0.
* `pythagorean_comma`: twelve perfect fifths overshoot seven octaves by exactly 531441/524288.
* `log_three_div_two_irrational`: log₂(3/2), the size of a fifth in octaves, is irrational, so no equal division of the
  octave contains an exact perfect fifth.
INTERPRETED (not formalized): equal temperament spreads the comma over twelve fifths, each about 2 cents flat.
-/

namespace PianoTuning

theorem three_pow_ne_two_pow (a b : ℕ) (hb : 0 < b) : 3 ^ a ≠ 2 ^ b := by
  intro h
  have h1 : (3 ^ a) % 2 = 1 := by rw [Nat.pow_mod]; norm_num
  have h2 : (2 ^ b) % 2 = 0 := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'; rw [pow_succ]; simp
  omega

theorem fifths_never_close (a b : ℕ) (ha : 0 < a) : ((3 : ℚ) / 2) ^ a ≠ 2 ^ b := by
  intro h
  have : (3 : ℚ) ^ a = 2 ^ (a + b) := by
    rw [div_pow] at h; rw [pow_add]; field_simp at h; linarith [h]
  exact three_pow_ne_two_pow a (a + b) (by omega) (by exact_mod_cast this)

theorem pythagorean_comma : ((3 : ℚ) / 2) ^ 12 / 2 ^ 7 = 531441 / 524288 := by norm_num

theorem log_three_div_two_irrational : Irrational (Real.logb 2 (3 / 2)) := by
  rintro ⟨q, hq⟩
  have hpos : (0 : ℝ) < Real.logb 2 (3 / 2) := Real.logb_pos (by norm_num) (by norm_num)
  rw [← hq] at hpos
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hpos
  have hn : 0 < q.num := Rat.num_pos.mpr hqpos
  obtain ⟨m, hm⟩ : ∃ m : ℕ, q.num = m := ⟨q.num.toNat, (Int.toNat_of_nonneg hn.le).symm⟩
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hqd : (q : ℝ) = (m : ℝ) / q.den := by rw [Rat.cast_def, hm]; push_cast; ring
  have h1 : Real.logb 2 (3 / 2) * q.den = m := by rw [← hq, hqd]; field_simp
  have h2 : ((2 : ℝ) ^ Real.logb 2 (3 / 2)) ^ (q.den : ℝ) = (2 : ℝ) ^ (m : ℝ) := by
    rw [← Real.rpow_mul (by norm_num), h1]
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), Real.rpow_natCast, Real.rpow_natCast] at h2
  have key : ((3 : ℚ) / 2) ^ q.den = 2 ^ m := Rat.cast_injective (α := ℝ) (by push_cast; exact h2)
  exact fifths_never_close q.den m q.den_pos key

end PianoTuning
