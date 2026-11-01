/-
# Amplitude sphere, arrow vs spinor, phase cancellation, and VNA calibration

PROVED
1. `amplitudes_on_sphere`: for a probability vector p, the amplitudes 2√pᵢ lie on the sphere of
   radius 2: ∑ (2√pᵢ)² = 4.
2. `fisher_pullback`: along a curve p(t) with p > 0, d/dt (2√p) = p'/√p and its square is p'²/p, the
   Fisher information term. So the map p ↦ 2√p carries the Fisher metric to the ordinary one.
3. `bc_nonneg`, `bc_le_one`, `bc_self`: the Bhattacharyya coefficient ∑ √(pᵢqᵢ) lies in [0, 1] and is
   1 when p = q. `frDist_self`, `frDist_nonneg`, `frDist_le_pi`: the angle distance
   2·arccos(∑ √(pᵢqᵢ)) is 0 from p to itself and lies in [0, π].
4. `arrow_vs_spinor`: a full turn e^{2πi} = 1 for an arrow; at half the angle, a spinor gives
   e^{iπ} = −1 after one full turn and e^{2πi} = 1 after two.
5. `root_sum`: ∑_{k<N} ζ^{km} = N if N ∣ m and 0 otherwise (ζ = e^{2πi/N}). In-phase terms add and
   out-of-phase terms cancel.
6. `delay_spike`: for 0 ≤ n, d < N, the inverse DFT of a pure delay d is a spike: ∑_k ζ^{k(n + N − d)}
   is N at n = d and 0 elsewhere.
7. `calibration_unique`: in the one-port error model Γₘ = e₀₀ + e₀₁Γ/(1 − e₁₁Γ), the three standards
   load (Γ = 0), open (Γ = 1) and short (Γ = −1) determine e₀₀, e₀₁, e₁₁.
8. `correct_meas`, `two_vnas_agree`: correcting with the calibrated error terms returns the true Γ,
   so two calibrated instruments with different error terms report the same Γ.

CITED, NOT PROVED HERE
- That 2·arccos(∑ √(pᵢqᵢ)) is the length of the shortest path in the Fisher metric (great circles
  on the sphere of item 1).
- Gauss's Theorema Egregium and holonomy: the rotation of a vector carried around a small loop
  equals the enclosed curvature.
- That a VNA's time-domain mode is an inverse DFT of the measured S₂₁ (item 6 is the arithmetic).
-/

import Mathlib

namespace AmplitudeSphere

open Finset Real

variable {ι : Type*} [Fintype ι]

/-! ## 1–3. The amplitude sphere -/

theorem amplitudes_on_sphere (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    ∑ i, (2 * Real.sqrt (p i)) ^ 2 = 4 := by
  calc ∑ i, (2 * Real.sqrt (p i)) ^ 2 = ∑ i, 4 * p i :=
        Finset.sum_congr rfl fun i _ => by rw [mul_pow, Real.sq_sqrt (hp i)]; norm_num
    _ = 4 * ∑ i, p i := by rw [Finset.mul_sum]
    _ = 4 := by rw [hs, mul_one]

theorem fisher_pullback (p : ℝ → ℝ) (p' t : ℝ) (hp : HasDerivAt p p' t) (hpos : 0 < p t) :
    HasDerivAt (fun s => 2 * Real.sqrt (p s)) (p' / Real.sqrt (p t)) t ∧
      (p' / Real.sqrt (p t)) ^ 2 = p' ^ 2 / p t := by
  have hs : 0 < Real.sqrt (p t) := Real.sqrt_pos.mpr hpos
  refine ⟨?_, ?_⟩
  · have h := (hp.sqrt hpos.ne').const_mul 2
    convert h using 1
    field_simp
  · rw [div_pow, Real.sq_sqrt hpos.le]

/-- Bhattacharyya coefficient. -/
noncomputable def bc (p q : ι → ℝ) : ℝ := ∑ i, Real.sqrt (p i * q i)

theorem bc_nonneg (p q : ι → ℝ) : 0 ≤ bc p q :=
  Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _

theorem bc_le_one (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsp : ∑ i, p i = 1) (hsq : ∑ i, q i = 1) : bc p q ≤ 1 := by
  have key : ∀ i, Real.sqrt (p i * q i) ≤ (p i + q i) / 2 := by
    intro i
    rw [Real.sqrt_mul (hp i)]
    nlinarith [sq_nonneg (Real.sqrt (p i) - Real.sqrt (q i)), Real.sq_sqrt (hp i),
      Real.sq_sqrt (hq i)]
  calc bc p q ≤ ∑ i, (p i + q i) / 2 := Finset.sum_le_sum fun i _ => key i
    _ = ((∑ i, p i) + ∑ i, q i) / 2 := by rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ = 1 := by rw [hsp, hsq]; norm_num

theorem bc_self (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsp : ∑ i, p i = 1) : bc p p = 1 := by
  unfold bc
  rw [← hsp]
  exact Finset.sum_congr rfl fun i _ => Real.sqrt_mul_self (hp i)

/-- Angle distance between two probability vectors. -/
noncomputable def frDist (p q : ι → ℝ) : ℝ := 2 * Real.arccos (bc p q)

theorem frDist_self (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsp : ∑ i, p i = 1) : frDist p p = 0 := by
  unfold frDist
  rw [bc_self p hp hsp, Real.arccos_one, mul_zero]

theorem frDist_nonneg (p q : ι → ℝ) : 0 ≤ frDist p q :=
  mul_nonneg zero_le_two (Real.arccos_nonneg _)

theorem frDist_le_pi (p q : ι → ℝ) : frDist p q ≤ Real.pi := by
  unfold frDist
  have := (Real.arccos_le_pi_div_two).mpr (bc_nonneg p q)
  linarith

/-! ## 4. Arrow and spinor -/

open Complex in
theorem arrow_vs_spinor :
    Complex.exp (2 * (Real.pi : ℂ) * I) = 1 ∧
      Complex.exp ((2 * (Real.pi : ℂ) / 2) * I) = -1 ∧
      Complex.exp ((4 * (Real.pi : ℂ) / 2) * I) = 1 := by
  refine ⟨Complex.exp_two_pi_mul_I, ?_, ?_⟩
  · rw [show 2 * (Real.pi : ℂ) / 2 = Real.pi by ring]
    exact Complex.exp_pi_mul_I
  · rw [show 4 * (Real.pi : ℂ) / 2 = 2 * Real.pi by ring]
    exact Complex.exp_two_pi_mul_I

/-! ## 5–6. Phases add or cancel -/

open Complex in
theorem root_sum (N : ℕ) (hN : 0 < N) (m : ℕ) :
    ∑ k ∈ range N, (Complex.exp (2 * Real.pi * I / N)) ^ (k * m) =
      if N ∣ m then (N : ℂ) else 0 := by
  set ζ := Complex.exp (2 * Real.pi * I / N)
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN.ne'
  have hterm : ∀ k, ζ ^ (k * m) = (ζ ^ m) ^ k := fun k => by rw [mul_comm, pow_mul]
  simp_rw [hterm]
  split_ifs with h
  · have h1 : ζ ^ m = 1 := (hζ.pow_eq_one_iff_dvd m).mpr h
    simp [h1]
  · have h1 : ζ ^ m ≠ 1 := fun e => h ((hζ.pow_eq_one_iff_dvd m).mp e)
    rw [geom_sum_eq h1]
    have h2 : (ζ ^ m) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [h2, sub_self, zero_div]

theorem dvd_shift_iff (N n d : ℕ) (hn : n < N) (hd : d < N) :
    N ∣ n + (N - d) ↔ n = d := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨e, he⟩ : ∃ e, e + d = N := ⟨N - d, by omega⟩
    have hc' : n + e = N * c := by rw [← hc]; omega
    rcases c with _ | _ | c
    · omega
    · omega
    · nlinarith
  · intro h
    subst h
    exact ⟨1, by omega⟩

open Complex in
theorem delay_spike (N : ℕ) (hN : 0 < N) (n d : ℕ) (hn : n < N) (hd : d < N) :
    ∑ k ∈ range N, (Complex.exp (2 * Real.pi * I / N)) ^ (k * (n + (N - d))) =
      if n = d then (N : ℂ) else 0 := by
  rw [root_sum N hN]
  simp only [dvd_shift_iff N n d hn hd]

/-! ## 7–8. VNA one-port calibration -/

/-- Measured reflection for true reflection Γ, with error terms e₀₀, e₀₁, e₁₁. -/
noncomputable def meas (e00 e01 e11 Γ : ℂ) : ℂ := e00 + e01 * Γ / (1 - e11 * Γ)

theorem meas_zero (e00 e01 e11 : ℂ) : meas e00 e01 e11 0 = e00 := by simp [meas]

theorem meas_one (e00 e01 e11 : ℂ) : meas e00 e01 e11 1 = e00 + e01 / (1 - e11) := by
  simp [meas]

theorem meas_neg_one (e00 e01 e11 : ℂ) : meas e00 e01 e11 (-1) = e00 - e01 / (1 + e11) := by
  unfold meas
  rw [show (1 : ℂ) - e11 * (-1) = 1 + e11 by ring]
  ring

theorem calibration_unique (e00 e01 e11 f00 f01 f11 : ℂ) (he : e01 ≠ 0)
    (he1 : 1 - e11 ≠ 0) (he2 : 1 + e11 ≠ 0) (hf1 : 1 - f11 ≠ 0) (hf2 : 1 + f11 ≠ 0)
    (hload : meas e00 e01 e11 0 = meas f00 f01 f11 0)
    (hopen : meas e00 e01 e11 1 = meas f00 f01 f11 1)
    (hshort : meas e00 e01 e11 (-1) = meas f00 f01 f11 (-1)) :
    e00 = f00 ∧ e01 = f01 ∧ e11 = f11 := by
  rw [meas_zero, meas_zero] at hload
  rw [meas_one, meas_one, hload, add_right_inj, div_eq_div_iff he1 hf1] at hopen
  rw [meas_neg_one, meas_neg_one, hload, sub_right_inj, div_eq_div_iff he2 hf2] at hshort
  have h01 : e01 = f01 := by linear_combination (hopen + hshort) / 2
  refine ⟨hload, h01, ?_⟩
  subst h01
  have : e01 * (e11 - f11) = 0 := by linear_combination (hopen - hshort) / 2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h he
  · linear_combination h

/-- Correct a measured reflection with calibrated error terms. -/
noncomputable def correct (e00 e01 e11 m : ℂ) : ℂ := (m - e00) / (e01 + e11 * (m - e00))

theorem correct_meas (e00 e01 e11 Γ : ℂ) (he : e01 ≠ 0) (hd : 1 - e11 * Γ ≠ 0) :
    correct e00 e01 e11 (meas e00 e01 e11 Γ) = Γ := by
  unfold correct meas
  rw [show e00 + e01 * Γ / (1 - e11 * Γ) - e00 = e01 * Γ / (1 - e11 * Γ) by ring]
  have hden : e01 + e11 * (e01 * Γ / (1 - e11 * Γ)) = e01 / (1 - e11 * Γ) := by
    field_simp
    ring
  rw [hden]
  have hd' : (1 : ℂ) - Γ * e11 ≠ 0 := by rwa [mul_comm] at hd
  field_simp

theorem two_vnas_agree (e00 e01 e11 f00 f01 f11 Γ : ℂ) (he : e01 ≠ 0) (hf : f01 ≠ 0)
    (hde : 1 - e11 * Γ ≠ 0) (hdf : 1 - f11 * Γ ≠ 0) :
    correct e00 e01 e11 (meas e00 e01 e11 Γ) = correct f00 f01 f11 (meas f00 f01 f11 Γ) := by
  rw [correct_meas e00 e01 e11 Γ he hde, correct_meas f00 f01 f11 Γ hf hdf]

end AmplitudeSphere

#print axioms AmplitudeSphere.amplitudes_on_sphere
#print axioms AmplitudeSphere.fisher_pullback
#print axioms AmplitudeSphere.bc_le_one
#print axioms AmplitudeSphere.frDist_self
#print axioms AmplitudeSphere.frDist_le_pi
#print axioms AmplitudeSphere.arrow_vs_spinor
#print axioms AmplitudeSphere.root_sum
#print axioms AmplitudeSphere.delay_spike
#print axioms AmplitudeSphere.calibration_unique
#print axioms AmplitudeSphere.correct_meas
#print axioms AmplitudeSphere.two_vnas_agree
