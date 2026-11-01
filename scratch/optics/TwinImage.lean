import Mathlib

/-!
# Twin image of an intensity hologram, and three-step phase shifting

## PROVED

* `normSq_real_add_conj`: for every complex `a` and real `r`,
  `normSq (r + a) = normSq (r + conj a)`.
* `twin_phase`: for every real `φ`,
  `normSq (1 + exp (φ i)) = normSq (1 + exp (-φ i))`.
* `twin_only_ambiguity`: for real `r ≠ 0` and complex `a, b` with `normSq a = normSq b`,
  `normSq (r + a) = normSq (r + b)` holds if and only if `b = a` or `b = conj a`.
* `normSq_one_add_exp`: for every real `θ`, `normSq (1 + exp (θ i)) = 2 + 2 cos θ`.
* `zonePlate_eq_normSq`: the function `zonePlate λ z ρ := 2 + 2 cos (π ρ² / (λ z))` equals
  `normSq (1 + exp (i π ρ² / (λ z)))`.
* `zonePlate_neg`: `zonePlate λ (-z) ρ = zonePlate λ z ρ` for all real `λ, z, ρ`;
  `zonePlate_abs`: `zonePlate λ |z| ρ = zonePlate λ z ρ`.
* `cos_two_pi_div_three`, `sin_two_pi_div_three`: `cos (2π/3) = -1/2`, `sin (2π/3) = √3/2`.
* `zonePlate_eq_zero_at`, `zonePlate_eq_four_at`: for `λ > 0`, `z ≠ 0`,
  `zonePlate λ z (√(λ |z|)) = 0` and `zonePlate λ z (√(2 λ |z|)) = 4`.
* `cos_not_const_on_Ioo`: for `p < q`, `Real.cos` is not constant on the open interval `(p, q)`.
* `zonePlate_not_const`: for `λ ≠ 0`, `z ≠ 0` and `0 ≤ a < b`, there are `ρ₁, ρ₂ ∈ (a, b)` with
  `zonePlate λ z ρ₁ ≠ zonePlate λ z ρ₂`.
* `three_step_sin`, `three_step_cos`: with `I_m = A + B cos (φ - θ_m)` and
  `θ_1 = -2π/3, θ_2 = 0, θ_3 = 2π/3`, one has `√3 (I_3 - I_1) = 3 B sin φ` and
  `2 I_2 - I_1 - I_3 = 3 B cos φ` (for all real `A, B, φ`).
* `three_step_arg`: if moreover `B > 0` and `φ ∈ (-π, π]`, then
  `arg ((2 I_2 - I_1 - I_3) + i √3 (I_3 - I_1)) = φ`.

## INTERPRETED (not formalized)

* An intensity hologram records `|r + a|²` where `r` is a real (zero-phase, unit or constant amplitude)
  reference and `a` is the object wave at a plate point. The identities above say the record is
  unchanged when the object wave is replaced by its complex conjugate; with known modulus this is
  the only ambiguity at a single point. The conjugate wave is the twin image.
* `exp (i π ρ² / (λ z))` is used as the paraxial (Fresnel) phase of a point source at axial
  distance `z` with unit amplitude, measured at plate radius `ρ`; amplitude fall-off, obliquity,
  and the constant phase `exp (i k z)` are dropped. Under that model a point at `z` (diverging,
  virtual focus) and at `-z` (converging, real focus) give the same plate. Nothing about
  diffraction from the plate or reconstruction is formalized.
* The three-step formulas are the standard algebraic identities behind phase-shifting
  interferometry; noise, miscalibrated shifts, and unwrapping are not modelled.
-/

namespace TwinImage

open Complex

/-- The record of a real reference `r` plus object wave `a` is invariant under `a ↦ conj a`. -/
theorem normSq_real_add_conj (r : ℝ) (a : ℂ) :
    normSq ((r : ℂ) + a) = normSq ((r : ℂ) + (starRingEnd ℂ) a) := by
  rw [← normSq_conj ((r : ℂ) + a), map_add, conj_ofReal]

/-- A phase and its negative give the same record against a unit real reference. -/
theorem twin_phase (φ : ℝ) :
    normSq (1 + exp ((φ : ℂ) * I)) = normSq (1 + exp (-(φ : ℂ) * I)) := by
  have h : exp (-(φ : ℂ) * I) = (starRingEnd ℂ) (exp ((φ : ℂ) * I)) := by
    rw [← Complex.exp_conj, map_mul, conj_ofReal, conj_I]; ring_nf
  have := normSq_real_add_conj 1 (exp ((φ : ℂ) * I))
  rw [h]; simpa using this

/-- With known object modulus and a nonzero real reference, conjugation is the only ambiguity. -/
theorem twin_only_ambiguity (r : ℝ) (hr : r ≠ 0) (a b : ℂ) (hab : normSq a = normSq b) :
    normSq ((r : ℂ) + a) = normSq ((r : ℂ) + b) ↔ b = a ∨ b = (starRingEnd ℂ) a := by
  rw [normSq_apply, normSq_apply] at hab
  simp only [normSq_apply, add_re, add_im, ofReal_re, ofReal_im, zero_add]
  constructor
  · intro h
    have hre : b.re = a.re := by
      have : 2 * r * (b.re - a.re) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd (by linarith : r = 0) hr
      · linarith
    have him : (b.im - a.im) * (b.im + a.im) = 0 := by rw [hre] at hab; nlinarith
    rcases mul_eq_zero.mp him with h1 | h1
    · left; exact Complex.ext hre (by linarith)
    · right; exact Complex.ext (by simpa using hre) (by simp; linarith)
  · rintro (h | h)
    · rw [h]
    · subst h; simp

/-- Intensity of unit reference plus unit-amplitude wave of phase `θ`. -/
theorem normSq_one_add_exp (θ : ℝ) : normSq (1 + exp ((θ : ℂ) * I)) = 2 + 2 * Real.cos θ := by
  rw [normSq_apply]
  simp only [add_re, add_im, one_re, one_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, zero_add]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Paraxial point-source hologram (Fresnel zone plate) intensity at radius `ρ`. -/
noncomputable def zonePlate (lam z ρ : ℝ) : ℝ := 2 + 2 * Real.cos (Real.pi * ρ ^ 2 / (lam * z))

theorem zonePlate_eq_normSq (lam z ρ : ℝ) :
    zonePlate lam z ρ = normSq (1 + exp (((Real.pi * ρ ^ 2 / (lam * z) : ℝ) : ℂ) * I)) := by
  rw [normSq_one_add_exp]; rfl

/-- A point at `z` and a point at `-z` record the same zone plate. -/
theorem zonePlate_neg (lam z ρ : ℝ) : zonePlate lam (-z) ρ = zonePlate lam z ρ := by
  unfold zonePlate
  rw [mul_neg, div_neg, Real.cos_neg]

theorem zonePlate_abs (lam z ρ : ℝ) : zonePlate lam |z| ρ = zonePlate lam z ρ := by
  rcases abs_choice z with h | h <;> rw [h]
  exact zonePlate_neg lam z ρ

theorem zonePlate_eq_zero_at (lam z : ℝ) (hl : 0 < lam) (hz : z ≠ 0) :
    zonePlate lam z (Real.sqrt (lam * |z|)) = 0 := by
  rw [← zonePlate_abs]
  have hpos : 0 < lam * |z| := mul_pos hl (abs_pos.mpr hz)
  unfold zonePlate
  rw [Real.sq_sqrt hpos.le, mul_div_assoc, div_self hpos.ne', mul_one, Real.cos_pi]; ring

theorem zonePlate_eq_four_at (lam z : ℝ) (hl : 0 < lam) (hz : z ≠ 0) :
    zonePlate lam z (Real.sqrt (2 * lam * |z|)) = 4 := by
  rw [← zonePlate_abs]
  have hpos : 0 < lam * |z| := mul_pos hl (abs_pos.mpr hz)
  unfold zonePlate
  have : Real.pi * (2 * lam * |z|) / (lam * |z|) = 2 * Real.pi := by
    field_simp
  rw [Real.sq_sqrt (by positivity), this, Real.cos_two_pi]; ring

/-- The cosine is not constant on any nonempty open interval. -/
theorem cos_not_const_on_Ioo (p q : ℝ) (hpq : p < q) :
    ¬ ∃ c, ∀ t ∈ Set.Ioo p q, Real.cos t = c := by
  rintro ⟨c, hc⟩
  have hmem : ∀ t ∈ Set.Ioo p q, Set.Ioo p q ∈ nhds t := fun t ht => isOpen_Ioo.mem_nhds ht
  have hsin : ∀ t ∈ Set.Ioo p q, Real.sin t = 0 := by
    intro t ht
    have hev : Real.cos =ᶠ[nhds t] fun _ => c :=
      Filter.mem_of_superset (hmem t ht) (fun s hs => hc s hs)
    have := hev.deriv_eq
    rw [Real.deriv_cos, deriv_const] at this
    linarith
  obtain ⟨t, ht⟩ : (Set.Ioo p q).Nonempty := Set.nonempty_Ioo.mpr hpq
  have hev : Real.sin =ᶠ[nhds t] fun _ => (0 : ℝ) :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hsin s hs)
  have h1 := hev.deriv_eq
  rw [Real.deriv_sin, deriv_const] at h1
  have h2 := Real.sin_sq_add_cos_sq t
  rw [hsin t ht, show Real.cos t = 0 from h1] at h2
  norm_num at h2

/-- The zone-plate intensity is not constant on any interval of radii `(a, b)` with `0 ≤ a < b`. -/
theorem zonePlate_not_const (lam z : ℝ) (hl : lam ≠ 0) (hz : z ≠ 0) (a b : ℝ) (ha : 0 ≤ a)
    (hab : a < b) :
    ∃ ρ₁ ∈ Set.Ioo a b, ∃ ρ₂ ∈ Set.Ioo a b, zonePlate lam z ρ₁ ≠ zonePlate lam z ρ₂ := by
  by_contra hcon
  push Not at hcon
  set k : ℝ := |Real.pi / (lam * z)| with hk
  have kpos : 0 < k := abs_pos.mpr (div_ne_zero Real.pi_ne_zero (mul_ne_zero hl hz))
  -- cos (π ρ² / (λ z)) = cos (k ρ²)
  have hcosk : ∀ ρ, Real.cos (Real.pi * ρ ^ 2 / (lam * z)) = Real.cos (k * ρ ^ 2) := by
    intro ρ
    rw [hk, mul_div_right_comm]
    rcases abs_choice (Real.pi / (lam * z)) with h | h <;> rw [h]
    rw [neg_mul, Real.cos_neg]
  obtain ⟨ρ₀, hρ₀⟩ : (Set.Ioo a b).Nonempty := Set.nonempty_Ioo.mpr hab
  apply cos_not_const_on_Ioo (k * a ^ 2) (k * b ^ 2)
    (mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hab ha two_ne_zero) kpos)
  refine ⟨Real.cos (k * ρ₀ ^ 2), fun t ht => ?_⟩
  set ρ := Real.sqrt (t / k)
  have ht0 : 0 ≤ t / k := div_nonneg (le_trans (by positivity) ht.1.le) kpos.le
  have hρsq : k * ρ ^ 2 = t := by
    rw [Real.sq_sqrt ht0]; field_simp
  have hρmem : ρ ∈ Set.Ioo a b := by
    constructor
    · rw [← Real.sqrt_sq ha]
      apply Real.sqrt_lt_sqrt (sq_nonneg a)
      rw [lt_div_iff₀ kpos]; linarith [ht.1]
    · rw [← Real.sqrt_sq (ha.trans hab.le)]
      apply Real.sqrt_lt_sqrt ht0
      rw [div_lt_iff₀ kpos]; linarith [ht.2]
  have := hcon ρ hρmem ρ₀ hρ₀
  unfold zonePlate at this
  rw [hcosk, hcosk, hρsq] at this
  linarith

/-! ### Three-step phase shifting -/

/-- Recorded intensity at phase shift `θ`. -/
noncomputable def shotI (A B φ θ : ℝ) : ℝ := A + B * Real.cos (φ - θ)

theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

theorem sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = √3 / 2 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]

theorem three_step_sin (A B φ : ℝ) :
    √3 * (shotI A B φ (2 * Real.pi / 3) - shotI A B φ (-(2 * Real.pi / 3))) =
      3 * B * Real.sin φ := by
  unfold shotI
  rw [sub_neg_eq_add, Real.cos_sub, Real.cos_add, cos_two_pi_div_three, sin_two_pi_div_three]
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  linear_combination B * Real.sin φ * h3

theorem three_step_cos (A B φ : ℝ) :
    2 * shotI A B φ 0 - shotI A B φ (-(2 * Real.pi / 3)) - shotI A B φ (2 * Real.pi / 3) =
      3 * B * Real.cos φ := by
  unfold shotI
  rw [sub_neg_eq_add, sub_zero, Real.cos_sub, Real.cos_add, cos_two_pi_div_three,
    sin_two_pi_div_three]
  ring

theorem three_step_arg (A B φ : ℝ) (hB : 0 < B) (hφ : φ ∈ Set.Ioc (-Real.pi) Real.pi) :
    arg (((2 * shotI A B φ 0 - shotI A B φ (-(2 * Real.pi / 3)) - shotI A B φ (2 * Real.pi / 3) :
      ℝ) : ℂ) + ((√3 * (shotI A B φ (2 * Real.pi / 3) - shotI A B φ (-(2 * Real.pi / 3))) : ℝ) :
      ℂ) * I) = φ := by
  rw [three_step_cos, three_step_sin]
  have : (((3 * B * Real.cos φ : ℝ) : ℂ) + ((3 * B * Real.sin φ : ℝ) : ℂ) * I) =
      ((3 * B : ℝ) : ℂ) * (Real.cos φ + Real.sin φ * I) := by
    push_cast; ring
  rw [this, arg_real_mul _ (by positivity)]
  have := arg_cos_add_sin_mul_I hφ
  simpa [← ofReal_cos, ← ofReal_sin] using this

end TwinImage
