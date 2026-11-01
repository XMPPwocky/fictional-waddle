import Mathlib

/-!
# Where the boundary pins the interior, and where interference unpins it

1-D interior `[0, L]`, boundary values `u 0 = a`, `u L = b`.
* Oscillating (phase present), `u'' = −k² u`: `u = A cos kx + B sin kx`.
* Evanescent (no phase), `u'' = κ² u`: `u = A cosh κx + B sinh κx`.

* E1 `wave_boundary_pins_iff`: the boundary determines an oscillating interior uniquely iff `sin (kL) ≠ 0`.
* E2 `resonances_quantized`: the failures are exactly `kL = nπ`, the standing-wave (interference) condition.
* E3 `resonant_mode_invisible`: at a resonance, `sin (nπx/L)` is a nonzero interior with ZERO boundary data. The boundary
  cannot see it.
* E4 `evanescent_always_pinned`: with no phase, the boundary always determines the interior uniquely.
-/

namespace WhereBoundaryPins

open Real

/-- **E1.** -/
theorem wave_boundary_pins_iff (k L a b : ℝ) :
    (∃! p : ℝ × ℝ, p.1 = a ∧ p.1 * cos (k * L) + p.2 * sin (k * L) = b) ↔ sin (k * L) ≠ 0 := by
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, huniq⟩ hs
    have := huniq (p.1, p.2 + 1) ⟨h1, by simp only [hs] at h2 ⊢; linarith⟩
    have h := congrArg Prod.snd this
    simp at h
  · intro hs
    refine ⟨(a, (b - a * cos (k * L)) / sin (k * L)), ⟨rfl, by simp only; field_simp; ring⟩, ?_⟩
    rintro ⟨x, y⟩ ⟨h1, h2⟩
    simp only at h1 h2
    subst h1
    ext
    · rfl
    · simp only; field_simp; linarith

/-- **E2.** -/
theorem resonances_quantized (k L : ℝ) : sin (k * L) = 0 ↔ ∃ n : ℤ, k * L = n * π := by
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, hn.symm⟩
  · rintro ⟨n, hn⟩; exact ⟨n, hn.symm⟩

/-- **E3.** -/
theorem resonant_mode_invisible (n : ℤ) (L : ℝ) (hL : L ≠ 0) (hn : n ≠ 0) :
    sin (n * π * 0 / L) = 0 ∧ sin (n * π * L / L) = 0 ∧ sin (n * π * (L / (2 * n)) / L) = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  refine ⟨by simp, ?_, ?_⟩
  · rw [mul_div_assoc, div_self hL, mul_one]; exact Real.sin_int_mul_pi n
  · rw [show (n : ℝ) * π * (L / (2 * n)) / L = π / 2 by field_simp]; exact Real.sin_pi_div_two

/-- **E4.** -/
theorem evanescent_always_pinned (κ L a b : ℝ) (hκ : 0 < κ) (hL : 0 < L) :
    ∃! p : ℝ × ℝ, p.1 = a ∧ p.1 * cosh (κ * L) + p.2 * sinh (κ * L) = b := by
  have hs : 0 < sinh (κ * L) := Real.sinh_pos_iff.2 (mul_pos hκ hL)
  refine ⟨(a, (b - a * cosh (κ * L)) / sinh (κ * L)), ⟨rfl, by simp only; field_simp; ring⟩, ?_⟩
  rintro ⟨x, y⟩ ⟨h1, h2⟩
  simp only at h1 h2
  subst h1
  ext
  · rfl
  · simp only; field_simp; linarith

end WhereBoundaryPins
