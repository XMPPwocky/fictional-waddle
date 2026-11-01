import Mathlib

/-!
# Global phase: invisible to readouts, and not storable in bits

PROVED
* `intensity_phase_invariant`: for `ψ : Fin n → ℂ`, `θ : ℝ`, every `k`,
  `‖exp (θ * I) * ψ k‖ ^ 2 = ‖ψ k‖ ^ 2`.
* `readout_phase_invariant`: every function of the intensity vector takes the same value
  on `exp (θ * I) • ψ` as on `ψ`.
* `interference_phase_invariant`: `(e ψ j) * conj (e ψ k) = ψ j * conj ψ k` with
  `e = exp (θ * I)`, for all `j k`.
* `no_phase_estimator_from_intensities`, `no_phase_estimator_from_interference`: for
  every `ψ` there is no function of the intensity data, resp. of the full interference matrix,
  returning `θ` on `exp (θ * I) • ψ` for every `θ ∈ [0, 2π)`.
* `no_roundtrip_fin_bits`: for every `n`, `encode : ℝ → (Fin n → Bool)`,
  `decode : (Fin n → Bool) → ℝ`, `decode ∘ encode` is not the identity on `[0, 2π)`.
* `no_injection_real_listBool`: no injective `ℝ → List Bool`.
* `no_injOn_Ico_listBool`: no `f : ℝ → List Bool` is injective on `[0, 2π)`.
* `no_roundtrip_listBool`: for every `encode : ℝ → List Bool`, `decode : List Bool → ℝ`,
  `decode ∘ encode` is not the identity on `[0, 2π)`.

INTERPRETED
* "Complex phase" of a program state is modelled as the global factor `exp (θ * I)` on an
  amplitude vector; "readouts" are arbitrary functions of the intensities `‖ψ k‖ ^ 2`, or of
  all interference terms `ψ j * conj ψ k`.
* "Round-trips through bits" is modelled as `decode (encode θ) = θ` for all `θ ∈ [0, 2π)`,
  with bit strings either of fixed length `n` or arbitrary finite length (`List Bool`).
  This is a cardinality obstruction only; it says nothing about approximate storage.
-/

namespace PhaseNoRoundTripA

open Complex

/-- The global phase factor. -/
noncomputable def phase (θ : ℝ) : ℂ := Complex.exp (θ * I)

/-- Phase-rotated amplitude vector. -/
noncomputable def rot (θ : ℝ) {n : ℕ} (ψ : Fin n → ℂ) : Fin n → ℂ := fun k => phase θ * ψ k

/-- Intensity vector. -/
noncomputable def intensity {n : ℕ} (ψ : Fin n → ℂ) : Fin n → ℝ := fun k => ‖ψ k‖ ^ 2

/-- Interference matrix `ψ_j * conj ψ_k`. -/
noncomputable def interference {n : ℕ} (ψ : Fin n → ℂ) : Fin n → Fin n → ℂ :=
  fun j k => ψ j * (starRingEnd ℂ) (ψ k)

lemma norm_phase (θ : ℝ) : ‖phase θ‖ = 1 := by
  simp [phase, Complex.norm_exp_ofReal_mul_I]

lemma phase_mul_conj (θ : ℝ) : phase θ * (starRingEnd ℂ) (phase θ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]
  simp

/-- (1) Intensities are unchanged by a global phase. -/
theorem intensity_phase_invariant {n : ℕ} (ψ : Fin n → ℂ) (θ : ℝ) (k : Fin n) :
    ‖Complex.exp (θ * I) * ψ k‖ ^ 2 = ‖ψ k‖ ^ 2 := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- (1') Every intensity-based readout is independent of the global phase. -/
theorem readout_phase_invariant {n : ℕ} {α : Type*} (R : (Fin n → ℝ) → α)
    (ψ : Fin n → ℂ) (θ : ℝ) : R (intensity (rot θ ψ)) = R (intensity ψ) := by
  congr 1
  funext k
  exact intensity_phase_invariant ψ θ k

/-- (4) All interference terms are unchanged by a global phase. -/
theorem interference_phase_invariant {n : ℕ} (ψ : Fin n → ℂ) (θ : ℝ) (j k : Fin n) :
    (Complex.exp (θ * I) * ψ j) * (starRingEnd ℂ) (Complex.exp (θ * I) * ψ k)
      = ψ j * (starRingEnd ℂ) (ψ k) := by
  have h := phase_mul_conj θ
  simp only [phase] at h
  rw [map_mul]
  calc (Complex.exp (θ * I) * ψ j) * ((starRingEnd ℂ) (Complex.exp (θ * I)) *
        (starRingEnd ℂ) (ψ k))
      = (Complex.exp (θ * I) * (starRingEnd ℂ) (Complex.exp (θ * I))) *
          (ψ j * (starRingEnd ℂ) (ψ k)) := by ring
    _ = ψ j * (starRingEnd ℂ) (ψ k) := by rw [h, one_mul]

theorem interference_rot {n : ℕ} (ψ : Fin n → ℂ) (θ : ℝ) :
    interference (rot θ ψ) = interference ψ := by
  funext j k
  exact interference_phase_invariant ψ θ j k

lemma pi_mem_Ico : Real.pi ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
  ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩

lemma zero_mem_Ico : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
  ⟨le_rfl, by linarith [Real.pi_pos]⟩

/-- No function of the interference matrix recovers the absolute phase on `[0, 2π)`. -/
theorem no_phase_estimator_from_interference {n : ℕ} {ψ : Fin n → ℂ}
    (g : (Fin n → Fin n → ℂ) → ℝ) :
    ¬ ∀ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), g (interference (rot θ ψ)) = θ := by
  intro h
  have h0 := h 0 zero_mem_Ico
  have hπ := h Real.pi pi_mem_Ico
  rw [interference_rot] at h0 hπ
  exact Real.pi_ne_zero (hπ.symm.trans h0)

/-- No function of the intensities recovers the absolute phase on `[0, 2π)`. -/
theorem no_phase_estimator_from_intensities {n : ℕ} {ψ : Fin n → ℂ}
    (g : (Fin n → ℝ) → ℝ) :
    ¬ ∀ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), g (intensity (rot θ ψ)) = θ := by
  intro h
  have h0 := h 0 zero_mem_Ico
  have hπ := h Real.pi pi_mem_Ico
  rw [readout_phase_invariant g ψ] at h0 hπ
  exact Real.pi_ne_zero (hπ.symm.trans h0)

lemma Ico_infinite : (Set.Ico (0 : ℝ) (2 * Real.pi)).Infinite :=
  Set.Ico_infinite (by linarith [Real.pi_pos])

/-- (2) No exact round trip of `[0, 2π)` through `n` bits. -/
theorem no_roundtrip_fin_bits (n : ℕ) (encode : ℝ → (Fin n → Bool))
    (decode : (Fin n → Bool) → ℝ) :
    ¬ ∀ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), decode (encode θ) = θ := by
  intro h
  have hsub : Set.Ico (0 : ℝ) (2 * Real.pi) ⊆ Set.range decode :=
    fun θ hθ => ⟨encode θ, h θ hθ⟩
  exact Ico_infinite ((Set.finite_range decode).subset hsub)

/-- (3) No injection `ℝ → List Bool`. -/
theorem no_injection_real_listBool : ¬ ∃ f : ℝ → List Bool, Function.Injective f := by
  rintro ⟨f, hf⟩
  have : Countable ℝ := hf.countable
  exact Cardinal.not_countable_real Set.countable_univ

lemma Ico_not_countable : ¬ (Set.Ico (0 : ℝ) (2 * Real.pi)).Countable := by
  intro hc
  have h1 := Cardinal.mk_Ico_real (show (0 : ℝ) < 2 * Real.pi by linarith [Real.pi_pos])
  have h2 := hc.le_aleph0
  rw [h1] at h2
  exact absurd h2 (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- (3') No map into `List Bool` is injective on `[0, 2π)`. -/
theorem no_injOn_Ico_listBool (f : ℝ → List Bool) :
    ¬ Set.InjOn f (Set.Ico (0 : ℝ) (2 * Real.pi)) := by
  intro hf
  exact Ico_not_countable
    ((Set.mapsTo_univ f _).countable_of_injOn hf Set.countable_univ)

/-- (3'') No exact round trip of `[0, 2π)` through finite bit strings of any length. -/
theorem no_roundtrip_listBool (encode : ℝ → List Bool) (decode : List Bool → ℝ) :
    ¬ ∀ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), decode (encode θ) = θ := by
  intro h
  apply no_injOn_Ico_listBool encode
  intro x hx y hy hxy
  rw [← h x hx, ← h y hy, hxy]

end PhaseNoRoundTripA
