import Mathlib

/-!
# Lagged autocorrelation of a discrete sinusoid

Setting: an `N`-periodic sequence `x t = cos (2π k t / N)` and its copy delayed by `d`
steps, `x (t - d)`. The lag `d` and frequency `k` are integers; `N > 0`.

## PROVED
* `sum_cos_vanish`: if `N ∤ m` then `∑_{t<N} cos (2π m t / N + b) = 0` for every real `b`.
* `lagged_autocov`: if `N ∤ 2k` then
  `(1/N) ∑_{t<N} cos (2π k t / N) * cos (2π k (t - d) / N) = cos (2π k d / N) / 2`.
  The hypothesis `N ∤ 2k` is exactly what is used. It holds whenever `0 < 2k < N`
  (`lagged_autocov_of_lt`).
* `lagged_autocorr`: under the same hypothesis, the normalised value
  `autocov d / autocov 0` equals `cos (2π k d / N)`.
* `cos_two_pi_mul_neg_iff`: for every real `x`,
  `cos (2π x) < 0 ↔ 1/4 < fract x ∧ fract x < 3/4`.
* `lagged_autocov_neg_iff`: under `N ∤ 2k`, the lagged average is negative iff the lag,
  measured in periods (`k d / N = d / T` with `T = N / k`), has fractional part strictly
  between `1/4` and `3/4`.

## Remarks (true but not stated as theorems here)
* For `k ≡ 0` or `2k ≡ 0 (mod N)` the sequence is constant or alternating and the average
  is `cos (2π k d / N)` rather than half of it; the hypothesis `N ∤ 2k` excludes these.
* The proof of `lagged_autocov` does not use integrality of `d`; `d : ℤ` is chosen because
  it is the case of a delayed copy of a sequence.

## INTERPRETED (not formalized)
If a fast series is driven by a slow layer through a delayed negative feedback, and the
resulting motion is close to a single sinusoid of period `T`, the cross-correlation of the
series with its own delayed copy oscillates as `cos (2π τ / T)` in the lag `τ`, and is
negative exactly for lags between a quarter and three quarters of a period (mod `T`).
Nothing here models the feedback loop itself, noise, damping, finite samples, multiple
frequencies, or the cross-correlation between two different series.
-/

open Real Finset

namespace PaceLayers

/-- A sum of a cosine over one period vanishes when the frequency is not a multiple of `N`. -/
theorem sum_cos_vanish (N : ℕ) (hN : 0 < N) (m : ℤ) (hm : ¬ (N : ℤ) ∣ m) (b : ℝ) :
    ∑ t ∈ range N, Real.cos (2 * π * m * t / N + b) = 0 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set ζ : ℂ := Complex.exp (2 * π * m / N * Complex.I) with hζ
  have hpow : ∀ t : ℕ, ζ ^ t = Complex.exp (((2 * π * m * t / N : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hζN : ζ ^ N = 1 := by
    rw [hpow]
    have : ((2 * π * m * (N : ℕ) / N : ℝ) : ℂ) * Complex.I = (m : ℂ) * (2 * π * Complex.I) := by
      push_cast
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [hζ, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    apply hm
    refine ⟨n, ?_⟩
    have hpiC : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h3 : (m : ℂ) = (N : ℂ) * n := by
      calc (m : ℂ) = (2 * π * m / N * Complex.I) * N / (2 * π * Complex.I) := by
            field_simp
        _ = (n * (2 * π * Complex.I)) * N / (2 * π * Complex.I) := by rw [hn]
        _ = (N : ℂ) * n := by field_simp
    exact_mod_cast h3
  have hgeom : ∑ t ∈ range N, ζ ^ t = 0 := by
    rw [geom_sum_eq hζ1, hζN, sub_self, zero_div]
  have hsum : ∑ t ∈ range N,
      Complex.exp (((2 * π * m * t / N + b : ℝ) : ℂ) * Complex.I) = 0 := by
    have : ∀ t ∈ range N, Complex.exp (((2 * π * m * t / N + b : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((b : ℂ) * Complex.I) * ζ ^ t := by
      intro t _
      rw [hpow, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [sum_congr rfl this, ← mul_sum, hgeom, mul_zero]
  have := congrArg Complex.re hsum
  rw [Complex.re_sum] at this
  simp only [Complex.exp_ofReal_mul_I_re] at this
  exact this

/-- The lagged average of a discrete sinusoid over one period. -/
noncomputable def autocov (N : ℕ) (k d : ℤ) : ℝ :=
  (1 / N) * ∑ t ∈ range N, Real.cos (2 * π * k * t / N) * Real.cos (2 * π * k * (t - d) / N)

theorem lagged_autocov (N : ℕ) (hN : 0 < N) (k : ℤ) (hk : ¬ (N : ℤ) ∣ 2 * k) (d : ℤ) :
    autocov N k d = Real.cos (2 * π * k * d / N) / 2 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold autocov
  have hterm : ∀ t ∈ range N,
      Real.cos (2 * π * k * t / N) * Real.cos (2 * π * k * (t - d) / N)
        = Real.cos (2 * π * k * d / N) / 2
          + Real.cos (2 * π * ((2 * k : ℤ) : ℝ) * t / N + (-(2 * π * k * d / N))) / 2 := by
    intro t _
    have e1 : 2 * π * k * d / N
        = 2 * π * k * t / N - 2 * π * k * (t - d) / N := by ring
    have e2 : 2 * π * ((2 * k : ℤ) : ℝ) * t / N + (-(2 * π * k * d / N))
        = 2 * π * k * t / N + 2 * π * k * (t - d) / N := by push_cast; ring
    rw [e2, e1, Real.cos_add, Real.cos_sub]
    ring
  rw [sum_congr rfl hterm, sum_add_distrib, ← sum_div, ← sum_div,
    sum_cos_vanish N hN (2 * k) hk, sum_const, card_range, nsmul_eq_mul]
  field_simp
  ring

theorem lagged_autocov_of_lt (N : ℕ) (k : ℤ) (hk0 : 0 < k) (hkN : 2 * k < N) (d : ℤ) :
    autocov N k d = Real.cos (2 * π * k * d / N) / 2 := by
  have hN : 0 < N := by exact_mod_cast (show (0 : ℤ) < N by omega)
  apply lagged_autocov N hN k _ d
  intro h
  have := Int.le_of_dvd (by omega) h
  omega

theorem lagged_autocorr (N : ℕ) (hN : 0 < N) (k : ℤ) (hk : ¬ (N : ℤ) ∣ 2 * k) (d : ℤ) :
    autocov N k d / autocov N k 0 = Real.cos (2 * π * k * d / N) := by
  rw [lagged_autocov N hN k hk, lagged_autocov N hN k hk]
  simp

theorem cos_two_pi_mul_neg_iff (x : ℝ) :
    Real.cos (2 * π * x) < 0 ↔ 1 / 4 < Int.fract x ∧ Int.fract x < 3 / 4 := by
  have hred : Real.cos (2 * π * x) = Real.cos (2 * π * Int.fract x) := by
    conv_lhs => rw [← Int.fract_add_floor x]
    rw [show 2 * π * (Int.fract x + ⌊x⌋) = 2 * π * Int.fract x + (⌊x⌋ : ℝ) * (2 * π) by ring,
      Real.cos_add_int_mul_two_pi]
  rw [hred]
  set y := Int.fract x
  have hy0 : 0 ≤ y := Int.fract_nonneg x
  have hy1 : y < 1 := Int.fract_lt_one x
  have hpi := Real.pi_pos
  constructor
  · intro hneg
    by_contra hcon
    rcases not_and_or.mp hcon with h | h
    · push Not at h
      have : 0 ≤ Real.cos (2 * π * y) :=
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by nlinarith) (by nlinarith)
      linarith
    · push Not at h
      have : 0 ≤ Real.cos (2 * π * y - 2 * π) :=
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by nlinarith) (by nlinarith)
      rw [Real.cos_sub_two_pi] at this
      linarith
  · rintro ⟨h1, h2⟩
    exact Real.cos_neg_of_pi_div_two_lt_of_lt (by nlinarith) (by nlinarith)

theorem lagged_autocov_neg_iff (N : ℕ) (hN : 0 < N) (k : ℤ) (hk : ¬ (N : ℤ) ∣ 2 * k)
    (d : ℤ) :
    autocov N k d < 0 ↔
      1 / 4 < Int.fract ((k * d : ℝ) / N) ∧ Int.fract ((k * d : ℝ) / N) < 3 / 4 := by
  rw [lagged_autocov N hN k hk, ← cos_two_pi_mul_neg_iff]
  rw [show 2 * π * k * d / N = 2 * π * ((k * d : ℝ) / N) by ring]
  constructor <;> intro h <;> linarith

end PaceLayers
