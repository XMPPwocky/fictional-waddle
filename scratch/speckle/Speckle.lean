import Mathlib

/-!
# Speckle, quadratures and the opponent rotated by 90°

PROVED:
* `intensity_eq`: the intensity of a field with quadratures `I` and `Q` is `|I + iQ|² = I² + Q²`.
* `one_quadrature_contrast`: if a quadrature has `E[I²] = s` and the Gaussian fourth moment `E[I⁴] = 3s²`, an observer
  who sees only that quadrature sees "intensity" `I²` with squared contrast `Var/mean² = 2`.
* `full_speckle_contrast`: with two independent such quadratures, the intensity `I² + Q²` has squared contrast exactly 1
  (fully developed speckle).
* `average_contrast`: averaging `N` uncorrelated patterns with equal mean `μ` and variance `σ²` gives variance `σ²/N`,
  so squared contrast falls as `1/N`.
* `no_finite_quadratures`: no pair of `n × n` complex matrices (`n ≥ 1`) satisfies `XP − PX = (i/2)·1`; canonical
  quadratures need infinitely many dimensions.
* `robertson`: for symmetric operators `A`, `B`, a vector `ψ` and any real centres `a`, `b`,
  `|⟨ψ, (AB − BA)ψ⟩| ≤ 2 ‖(A − a)ψ‖ ‖(B − b)ψ‖`. With `[X, P] = i/2` this is `ΔX ΔP ≥ 1/4`: the observer rotated by
  90° cannot measure the other quadrature sharply on the same state.
NOT FORMALIZED: the Gaussian moments themselves (taken as hypotheses), the Arthurs–Kelly 3 dB penalty for measuring both
quadratures at once, and the few-photon security of optical physical unclonable functions.
-/

namespace Speckle
open Complex

theorem intensity_eq (I Q : ℝ) : Complex.normSq (⟨I, Q⟩ : ℂ) = I ^ 2 + Q ^ 2 := by
  simp [Complex.normSq_apply]; ring

theorem one_quadrature_contrast (s m4 : ℝ) (hs : 0 < s) (h4 : m4 = 3 * s ^ 2) :
    (m4 - s ^ 2) / s ^ 2 = 2 := by
  subst h4; field_simp; ring

theorem full_speckle_contrast (s m4 cross : ℝ) (hs : 0 < s) (h4 : m4 = 3 * s ^ 2) (hx : cross = s * s) :
    let mean := s + s
    let second := m4 + 2 * cross + m4
    (second - mean ^ 2) / mean ^ 2 = 1 := by
  intro mean second
  simp only [mean, second]; subst h4; subst hx; field_simp; ring

theorem average_contrast (N : ℕ) (hN : 0 < N) (σ2 : ℝ) :
    (1 / (N : ℝ) ^ 2) * ∑ j : Fin N, ∑ k : Fin N, (if j = k then σ2 else 0) = σ2 / N := by
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem no_finite_quadratures (n : ℕ) (hn : 0 < n) (X P : Matrix (Fin n) (Fin n) ℂ) :
    X * P - P * X ≠ (Complex.I / 2) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul] at ht
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : Complex.I / 2 ≠ 0 := div_ne_zero Complex.I_ne_zero two_ne_zero
  exact mul_ne_zero this hn' ht.symm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

lemma commutator_as_inner (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) :
    ⟪ψ, A (B ψ)⟫ - ⟪ψ, B (A ψ)⟫ =
      ⟪A ψ - (a : ℂ) • ψ, B ψ - (b : ℂ) • ψ⟫ - ⟪B ψ - (b : ℂ) • ψ, A ψ - (a : ℂ) • ψ⟫ := by
  have h1 : ⟪ψ, A (B ψ)⟫ = ⟪A ψ, B ψ⟫ := (hA ψ (B ψ)).symm
  have h2 : ⟪ψ, B (A ψ)⟫ = ⟪B ψ, A ψ⟫ := (hB ψ (A ψ)).symm
  have h3 : ⟪A ψ, ψ⟫ = ⟪ψ, A ψ⟫ := hA ψ ψ
  have h4 : ⟪B ψ, ψ⟫ = ⟪ψ, B ψ⟫ := hB ψ ψ
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal, h1, h2, h3, h4]
  ring

theorem robertson (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : E) (a b : ℝ) :
    ‖⟪ψ, A (B ψ)⟫ - ⟪ψ, B (A ψ)⟫‖ ≤ 2 * ‖A ψ - (a : ℂ) • ψ‖ * ‖B ψ - (b : ℂ) • ψ‖ := by
  rw [commutator_as_inner A B hA hB ψ a b]
  set u := A ψ - (a : ℂ) • ψ
  set v := B ψ - (b : ℂ) • ψ
  have hc : ⟪v, u⟫ = (starRingEnd ℂ) ⟪u, v⟫ := (inner_conj_symm v u).symm
  calc ‖⟪u, v⟫ - ⟪v, u⟫‖ ≤ ‖⟪u, v⟫‖ + ‖⟪v, u⟫‖ := norm_sub_le _ _
    _ = 2 * ‖⟪u, v⟫‖ := by rw [hc, Complex.norm_conj]; ring
    _ ≤ 2 * (‖u‖ * ‖v‖) := by gcongr; exact norm_inner_le_norm u v
    _ = 2 * ‖u‖ * ‖v‖ := by ring

end Speckle
