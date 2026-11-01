import Mathlib

/-!
# Global phase: invisible to intensities and interference, and not storable in bits

PROVED
* `intensity_invariant`: `‖exp(θ i) ψ_k‖² = ‖ψ_k‖²` for every component `k`.
* `readout_invariant`: any function of the intensity vector takes the same value on
  `ψ` and on `exp(θ i) ψ`, for every real `θ`.
* `interference_invariant`: every pairwise product `ψ_j * conj ψ_k` is unchanged by
  `ψ ↦ exp(θ i) ψ`.
* `gram_readout_invariant`: any function of the full interference (Gram) matrix takes the
  same value on `ψ` and on `exp(θ i) ψ`.
* `no_phase_recovery`: there is no `g` such that `g (Gram (exp(θ i) ψ)) = θ` for all
  `θ ∈ [0, 2π)` (in particular absolute phase cannot be read off from intensities either,
  see `no_phase_recovery_intensity`).
* `no_finite_bit_round_trip`: for every `n`, `encode : ℝ → (Fin n → Bool)` and
  `decode : (Fin n → Bool) → ℝ`, `decode ∘ encode` is not the identity on `[0, 2π)`.
* `no_list_bool_round_trip`: the same with `List Bool` (unboundedly long finite bit
  strings) in place of `Fin n → Bool`.
* `no_injection_real_list_bool`: there is no injection `ℝ → List Bool`.
* `no_injection_Ico_list_bool`: there is no injection from `[0, 2π)` into `List Bool`.

INTERPRETED
* A "readout" is any function of the vector of intensities `‖ψ_k‖²`, or more generally of
  all interference terms `ψ_j * conj ψ_k`; such data cannot distinguish `ψ` from
  `exp(θ i) ψ`, so absolute phase is not identifiable from it.
* "Storing the phase in bits" is modelled as an exact round trip
  `decode (encode θ) = θ` for all `θ ∈ [0, 2π)`. This fails for any fixed finite number of
  bits (the image of `decode` is finite) and for arbitrary finite bit strings (`List Bool`
  is countable, `[0, 2π)` is not). Approximate storage to finite precision is not ruled out
  and is not addressed here.
-/

namespace PhaseNoRoundTripB

open Complex

/-- The global phase factor `exp(θ i)`. -/
noncomputable def phase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

lemma norm_phase (θ : ℝ) : ‖phase θ‖ = 1 := by
  unfold phase
  exact Complex.norm_exp_ofReal_mul_I θ

lemma phase_mul_conj (θ : ℝ) : phase θ * (starRingEnd ℂ) (phase θ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]
  simp

/-- Global phase rotation of an amplitude vector. -/
noncomputable def rotate {n : ℕ} (θ : ℝ) (ψ : Fin n → ℂ) : Fin n → ℂ :=
  fun k => phase θ * ψ k

/-- Intensity vector. -/
noncomputable def intensity {n : ℕ} (ψ : Fin n → ℂ) : Fin n → ℝ := fun k => ‖ψ k‖ ^ 2

/-- Interference (Gram) matrix `ψ_j * conj ψ_k`. -/
noncomputable def gram {n : ℕ} (ψ : Fin n → ℂ) : Fin n → Fin n → ℂ :=
  fun j k => ψ j * (starRingEnd ℂ) (ψ k)

theorem intensity_invariant {n : ℕ} (ψ : Fin n → ℂ) (θ : ℝ) (k : Fin n) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) * ψ k‖ ^ 2 = ‖ψ k‖ ^ 2 := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem intensity_rotate {n : ℕ} (ψ : Fin n → ℂ) (θ : ℝ) :
    intensity (rotate θ ψ) = intensity ψ := by
  funext k
  exact intensity_invariant ψ θ k

theorem readout_invariant {n : ℕ} {α : Type*} (f : (Fin n → ℝ) → α)
    (ψ : Fin n → ℂ) (θ : ℝ) :
    f (intensity (rotate θ ψ)) = f (intensity ψ) := by
  rw [intensity_rotate]

theorem interference_invariant {n : ℕ} (ψ : Fin n → ℂ) (θ : ℝ) (j k : Fin n) :
    (Complex.exp ((θ : ℂ) * Complex.I) * ψ j) *
        (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I) * ψ k) =
      ψ j * (starRingEnd ℂ) (ψ k) := by
  have h := phase_mul_conj θ
  unfold phase at h
  rw [map_mul]
  calc (Complex.exp ((θ : ℂ) * Complex.I) * ψ j) *
        ((starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) * (starRingEnd ℂ) (ψ k))
      = (Complex.exp ((θ : ℂ) * Complex.I) *
          (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))) *
          (ψ j * (starRingEnd ℂ) (ψ k)) := by ring
    _ = ψ j * (starRingEnd ℂ) (ψ k) := by rw [h, one_mul]

theorem gram_rotate {n : ℕ} (ψ : Fin n → ℂ) (θ : ℝ) :
    gram (rotate θ ψ) = gram ψ := by
  funext j k
  exact interference_invariant ψ θ j k

theorem gram_readout_invariant {n : ℕ} {α : Type*} (f : (Fin n → Fin n → ℂ) → α)
    (ψ : Fin n → ℂ) (θ : ℝ) :
    f (gram (rotate θ ψ)) = f (gram ψ) := by
  rw [gram_rotate]

lemma pi_mem_Ico : Real.pi ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
  constructor
  · exact Real.pi_pos.le
  · linarith [Real.pi_pos]

lemma zero_mem_Ico : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
  constructor
  · exact le_refl 0
  · linarith [Real.pi_pos]

/-- Absolute phase is not recoverable from the interference data. -/
theorem no_phase_recovery {n : ℕ} (ψ : Fin n → ℂ) (g : (Fin n → Fin n → ℂ) → ℝ) :
    ¬ ∀ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), g (gram (rotate θ ψ)) = θ := by
  intro h
  have h0 := h 0 zero_mem_Ico
  have hπ := h Real.pi pi_mem_Ico
  rw [gram_rotate] at h0 hπ
  rw [h0] at hπ
  exact Real.pi_pos.ne hπ

/-- Absolute phase is not recoverable from the intensities. -/
theorem no_phase_recovery_intensity {n : ℕ} (ψ : Fin n → ℂ) (g : (Fin n → ℝ) → ℝ) :
    ¬ ∀ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), g (intensity (rotate θ ψ)) = θ := by
  intro h
  have h0 := h 0 zero_mem_Ico
  have hπ := h Real.pi pi_mem_Ico
  rw [intensity_rotate] at h0 hπ
  rw [h0] at hπ
  exact Real.pi_pos.ne hπ

lemma Ico_infinite : (Set.Ico (0 : ℝ) (2 * Real.pi)).Infinite :=
  Set.Ico_infinite (by linarith [Real.pi_pos])

lemma Ico_not_countable : ¬ (Set.Ico (0 : ℝ) (2 * Real.pi)).Countable := by
  intro h
  have hle : Cardinal.mk (Set.Ico (0 : ℝ) (2 * Real.pi)) ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0_iff.mpr h.to_subtype
  rw [Cardinal.mk_Ico_real (by linarith [Real.pi_pos])] at hle
  exact absurd hle (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- No exact round trip of `[0, 2π)` through `n` bits. -/
theorem no_finite_bit_round_trip (n : ℕ) (encode : ℝ → (Fin n → Bool))
    (decode : (Fin n → Bool) → ℝ) :
    ¬ ∀ x ∈ Set.Ico (0 : ℝ) (2 * Real.pi), decode (encode x) = x := by
  intro h
  have hsub : Set.Ico (0 : ℝ) (2 * Real.pi) ⊆ Set.range decode :=
    fun x hx => ⟨encode x, h x hx⟩
  exact Ico_infinite ((Set.finite_range decode).subset hsub)

/-- No exact round trip of `[0, 2π)` through finite bit strings of any length. -/
theorem no_list_bool_round_trip (encode : ℝ → List Bool) (decode : List Bool → ℝ) :
    ¬ ∀ x ∈ Set.Ico (0 : ℝ) (2 * Real.pi), decode (encode x) = x := by
  intro h
  have hsub : Set.Ico (0 : ℝ) (2 * Real.pi) ⊆ Set.range decode :=
    fun x hx => ⟨encode x, h x hx⟩
  exact Ico_not_countable ((Set.countable_range decode).mono hsub)

/-- There is no injection from `ℝ` into `List Bool`. -/
theorem no_injection_real_list_bool : ¬ ∃ f : ℝ → List Bool, Function.Injective f := by
  rintro ⟨f, hf⟩
  have : Countable ℝ := hf.countable
  exact Cardinal.not_countable_real Set.countable_univ

/-- There is no injection from `[0, 2π)` into `List Bool`. -/
theorem no_injection_Ico_list_bool :
    ¬ ∃ f : Set.Ico (0 : ℝ) (2 * Real.pi) → List Bool, Function.Injective f := by
  rintro ⟨f, hf⟩
  have : Countable (Set.Ico (0 : ℝ) (2 * Real.pi)) := hf.countable
  exact Ico_not_countable (Set.to_countable _)

end PhaseNoRoundTripB
