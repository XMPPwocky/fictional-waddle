import Mathlib

/-!
# Whose models collapse with whose; the phase dies at the sampling boundary

**Linear coupling has no threshold.** Two models, anchors `a₁, a₂` (fraction `l` of private data) and coupling `c`
(fraction of the rest trained on the other's outputs). The gap `d = m₁ − m₂` obeys
`d (t+1) = l Δa + (1 − l)(1 − 2c) d t`.
* W1 `linear_gap_converges`: with `0 < l ≤ 1`, `0 ≤ c ≤ 1`, `d t − d⋆ = q^t (d 0 − d⋆)`, with
  `q = (1 − l)(1 − 2c)` and `d⋆ = l Δa / (l + 2c(1 − l))`.
* W2 `anchored_never_merge`: with `l > 0` and `Δa ≠ 0`, `d⋆ ≠ 0` for EVERY coupling `c ∈ [0, 1]`: no critical coupling.
* W3 `unanchored_merge`: with `l = 0` and `0 < c < 1`, `d t = (1 − 2c)^t d 0` (geometric merger).

**Bounded (phase) coupling has a threshold.** Adler / two-oscillator Kuramoto: `φ̇ = Δω − K sin φ`.
* W4 `adler_lock_iff`: a locked state (`φ̇ = 0`) exists iff `|Δω| ≤ K`.

**The boundary.** Samples carry `|amplitude|²` per outcome; the phase lives only in cross terms.
* W5 `phase_invisible`: `normSq (z · e^{iθ}) = normSq z`.
* W6 `phase_lives_in_cross_term`: `normSq (a + b) = normSq a + normSq b + 2 Re (a · conj b)`.
* W7 `phase_visible_to_interference`: `normSq (1 + e^{iπ}) = 0` and `normSq (1 + 1) = 4`, though every summand has
  `normSq = 1`.

**Selection from outside feels like a potential.** Doob h-transform of a kernel `P` by a positive harmonic `h`.
* W8 `doob_kernel_stochastic`: `∑ y, P x y * h y / h x = 1`.
* W9 `doob_is_potential`: `P x y * h y / h x = P x y * exp (log h y − log h x)`.
-/

namespace WhoseCollapse

/-- The gap between two models' means across generations. -/
def gap (l c Δa d0 : ℝ) : ℕ → ℝ
  | 0 => d0
  | t + 1 => l * Δa + (1 - l) * (1 - 2 * c) * gap l c Δa d0 t

/-- **W1.** -/
theorem linear_gap_converges (l c Δa d0 : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (t : ℕ) :
    gap l c Δa d0 t - l * Δa / (l + 2 * c * (1 - l))
      = ((1 - l) * (1 - 2 * c)) ^ t * (d0 - l * Δa / (l + 2 * c * (1 - l))) := by
  have hd : 0 < l + 2 * c * (1 - l) := by nlinarith
  induction t with
  | zero => simp [gap]
  | succ k ih =>
    rw [pow_succ]
    have : gap l c Δa d0 (k + 1) = l * Δa + (1 - l) * (1 - 2 * c) * gap l c Δa d0 k := rfl
    rw [this, show gap l c Δa d0 k = ((1 - l) * (1 - 2 * c)) ^ k * (d0 - l * Δa / (l + 2 * c * (1 - l)))
      + l * Δa / (l + 2 * c * (1 - l)) by linarith]
    field_simp
    ring

/-- **W2.** -/
theorem anchored_never_merge (l c Δa : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ha : Δa ≠ 0) :
    l * Δa / (l + 2 * c * (1 - l)) ≠ 0 := by
  have hd : 0 < l + 2 * c * (1 - l) := by nlinarith
  exact div_ne_zero (mul_ne_zero hl0.ne' ha) hd.ne'

/-- **W3.** -/
theorem unanchored_merge (c Δa d0 : ℝ) (t : ℕ) : gap 0 c Δa d0 t = (1 - 2 * c) ^ t * d0 := by
  induction t with
  | zero => simp [gap]
  | succ k ih => simp only [gap, ih]; ring

/-- **W4.** -/
theorem adler_lock_iff (Δω K : ℝ) (hK : 0 < K) : (∃ φ : ℝ, Δω - K * Real.sin φ = 0) ↔ |Δω| ≤ K := by
  constructor
  · rintro ⟨φ, hφ⟩
    have h1 := Real.abs_sin_le_one φ
    have : Δω = K * Real.sin φ := by linarith
    rw [this, abs_mul, abs_of_pos hK]
    nlinarith
  · intro h
    have h1 : -1 ≤ Δω / K := by rw [le_div_iff₀ hK]; linarith [neg_abs_le Δω]
    have h2 : Δω / K ≤ 1 := by rw [div_le_iff₀ hK]; linarith [le_abs_self Δω]
    refine ⟨Real.arcsin (Δω / K), ?_⟩
    rw [Real.sin_arcsin h1 h2]
    field_simp
    ring

/-- **W5.** -/
theorem phase_invisible (z : ℂ) (θ : ℝ) : Complex.normSq (z * Complex.exp (θ * Complex.I)) = Complex.normSq z := by
  rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq (Complex.exp _), Complex.norm_exp_ofReal_mul_I]
  ring

/-- **W6.** -/
theorem phase_lives_in_cross_term (a b : ℂ) :
    Complex.normSq (a + b) = Complex.normSq a + Complex.normSq b + 2 * (a * (starRingEnd ℂ) b).re := by
  exact Complex.normSq_add a b

/-- **W7.** -/
theorem phase_visible_to_interference :
    Complex.normSq (1 + Complex.exp (Real.pi * Complex.I)) = 0 ∧ Complex.normSq ((1 : ℂ) + 1) = 4 ∧
      Complex.normSq (Complex.exp (Real.pi * Complex.I)) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.exp_pi_mul_I]; simp
  · rw [show (1 : ℂ) + 1 = 2 by norm_num, Complex.normSq_ofNat]; norm_num
  · rw [Complex.exp_pi_mul_I]; simp

/-- **W8.** -/
theorem doob_kernel_stochastic {S : Type*} [Fintype S] (P : S → S → ℝ) (h : S → ℝ) (x : S) (hx : 0 < h x)
    (harm : ∑ y, P x y * h y = h x) : ∑ y, P x y * h y / h x = 1 := by
  rw [← Finset.sum_div, harm, div_self hx.ne']

/-- **W9.** -/
theorem doob_is_potential {S : Type*} (P : S → S → ℝ) (h : S → ℝ) (x y : S) (hx : 0 < h x) (hy : 0 < h y) :
    P x y * h y / h x = P x y * Real.exp (Real.log (h y) - Real.log (h x)) := by
  rw [Real.exp_sub, Real.exp_log hy, Real.exp_log hx]
  ring

end WhoseCollapse
