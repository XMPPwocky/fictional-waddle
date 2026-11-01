import Mathlib

/-!
# Cycle vs clock

Fidelity record: `FIDELITY_cycle_clock.md`. All 13 statements below were approved as statements
first (`scratch/CycleClockStatements.lean`) and are proved here without changes.

Part R  — positive weights (rates of a continuous-time Markov / mutation–selection generator).
Part A  — norm-preserving amplitudes, over ℝ and over ℂ.
Simplification: Part R works on the COMPLETE graph (every off-diagonal rate > 0).
-/

open Matrix Complex

namespace CycleClock

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Part R: positive weights -/

/-- Every off-diagonal rate is strictly positive (complete graph). The diagonal is arbitrary
(e.g. minus the exit rate, or a fitness term). -/
def PosRates (M : Matrix ι ι ℝ) : Prop := ∀ i j, i ≠ j → 0 < M i j

/-- Detailed balance at weights `π`: every probability current `π i M i j - π j M j i` vanishes. -/
def DetailedBalance (M : Matrix ι ι ℝ) (π : ι → ℝ) : Prop := ∀ i j, π i * M i j = π j * M j i

/-- Zero cycle affinity on every triangle (Kolmogorov's criterion). Read with exchange rates
`r i j = M i j / M j i`, it says no triangular arbitrage exists. -/
def NoArbitrage (M : Matrix ι ι ℝ) : Prop := ∀ i j k, M i j * M j k * M k i = M i k * M k j * M j i

/-- R1 (Kolmogorov, complete graph): a positive detailed-balance weighting exists iff no triangle
has nonzero affinity. -/
theorem kolmogorov [Nonempty ι] (M : Matrix ι ι ℝ) (hM : PosRates M) :
    (∃ π : ι → ℝ, (∀ i, 0 < π i) ∧ DetailedBalance M π) ↔ NoArbitrage M := by
  constructor
  · rintro ⟨π, hπ, hdb⟩ i j k
    have h1 := hdb i j
    have h2 := hdb j k
    have h3 := hdb k i
    have hprod : (π i * π j * π k) * (M i j * M j k * M k i)
        = (π i * π j * π k) * (M i k * M k j * M j i) := by
      calc (π i * π j * π k) * (M i j * M j k * M k i)
          = (π i * M i j) * (π j * M j k) * (π k * M k i) := by ring
        _ = (π j * M j i) * (π k * M k j) * (π i * M i k) := by rw [h1, h2, h3]
        _ = (π i * π j * π k) * (M i k * M k j * M j i) := by ring
    have hpi := hπ i
    have hpj := hπ j
    have hpk := hπ k
    have hpos : π i * π j * π k ≠ 0 := by positivity
    exact mul_left_cancel₀ hpos hprod
  · intro h
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine ⟨fun j => if j = i₀ then 1 else M i₀ j / M j i₀, ?_, ?_⟩
    · intro j
      dsimp only
      split_ifs with hj
      · exact one_pos
      · exact div_pos (hM _ _ (Ne.symm hj)) (hM _ _ hj)
    · intro i j
      dsimp only
      by_cases hij : i = j
      · subst hij; rfl
      by_cases hi : i = i₀
      · subst hi
        have hj : j ≠ i := Ne.symm hij
        have := (hM j i hj).ne'
        simp only [hj, ↓reduceIte, one_mul]
        field_simp
      by_cases hj : j = i₀
      · subst hj
        have := (hM i j hi).ne'
        simp only [hi, ↓reduceIte]
        field_simp
      simp only [hi, hj, ↓reduceIte]
      have a := (hM i i₀ hi).ne'
      have b := (hM j i₀ hj).ne'
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff a b]
      linear_combination h i₀ i j

/-- Schnakenberg entropy production of weights `π` (sum over ordered pairs; diagonal terms vanish). -/
noncomputable def entropyProduction (M : Matrix ι ι ℝ) (π : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, (π i * M i j - π j * M j i) * (Real.log (π i * M i j) - Real.log (π j * M j i))

/-- Helper: `(a - b)(log a - log b) ≥ 0` for positive `a, b`. -/
lemma sub_mul_log_sub_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a - b) * (Real.log a - Real.log b) := by
  rcases le_total a b with hab | hab
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith)
      (by linarith [Real.log_le_log ha hab])
  · exact mul_nonneg (by linarith) (by linarith [Real.log_le_log hb hab])

/-- Helper: `(a - b)(log a - log b) = 0` iff `a = b`, for positive `a, b`. -/
lemma sub_mul_log_sub_eq_zero_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) * (Real.log a - Real.log b) = 0 ↔ a = b := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · exact Real.log_injOn_pos (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb) (by linarith)
  · rintro rfl; simp

/-- Helper: every summand of the entropy production is nonnegative. -/
lemma entropyProduction_term_nonneg (M : Matrix ι ι ℝ) (hM : PosRates M) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (i j : ι) :
    0 ≤ (π i * M i j - π j * M j i) * (Real.log (π i * M i j) - Real.log (π j * M j i)) := by
  by_cases hij : i = j
  · subst hij; simp
  · exact sub_mul_log_sub_nonneg (mul_pos (hπ i) (hM i j hij))
      (mul_pos (hπ j) (hM j i (Ne.symm hij)))

/-- Helper: a summand vanishes iff the current on that pair vanishes. -/
lemma entropyProduction_term_eq_zero_iff (M : Matrix ι ι ℝ) (hM : PosRates M) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (i j : ι) :
    (π i * M i j - π j * M j i) * (Real.log (π i * M i j) - Real.log (π j * M j i)) = 0 ↔
      π i * M i j = π j * M j i := by
  by_cases hij : i = j
  · subst hij; simp
  · exact sub_mul_log_sub_eq_zero_iff (mul_pos (hπ i) (hM i j hij))
      (mul_pos (hπ j) (hM j i (Ne.symm hij)))

/-- R2a: entropy production is never negative. -/
theorem entropyProduction_nonneg (M : Matrix ι ι ℝ) (hM : PosRates M) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) : 0 ≤ entropyProduction M π := by
  unfold entropyProduction
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    entropyProduction_term_nonneg M hM π hπ i j

/-- R2b: it is zero exactly at detailed balance. -/
theorem entropyProduction_eq_zero_iff (M : Matrix ι ι ℝ) (hM : PosRates M) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) : entropyProduction M π = 0 ↔ DetailedBalance M π := by
  unfold entropyProduction DetailedBalance
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    entropyProduction_term_nonneg M hM π hπ i j]
  constructor
  · intro h i j
    have hi := h i (Finset.mem_univ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      entropyProduction_term_nonneg M hM π hπ i j] at hi
    exact (entropyProduction_term_eq_zero_iff M hM π hπ i j).mp (hi j (Finset.mem_univ _))
  · intro h i _
    exact Finset.sum_eq_zero fun j _ =>
      (entropyProduction_term_eq_zero_iff M hM π hπ i j).mpr (h i j)

/-- R2c ("a cycle is an arbitrage, and it dissipates"): if some triangle has nonzero affinity,
then EVERY positive weighting, the stationary one included, has strictly positive entropy
production. -/
theorem arbitrage_dissipates [Nonempty ι] (M : Matrix ι ι ℝ) (hM : PosRates M)
    (h : ¬ NoArbitrage M) : ∀ π : ι → ℝ, (∀ i, 0 < π i) → 0 < entropyProduction M π := by
  intro π hπ
  refine lt_of_le_of_ne (entropyProduction_nonneg M hM π hπ) fun h0 => h ?_
  exact (kolmogorov M hM).mp ⟨π, hπ, (entropyProduction_eq_zero_iff M hM π hπ).mp h0.symm⟩

/-- R3 ("rotation needs curl"): with no arbitrage, every complex eigenvalue of `M` is real.
So positive dynamics with a rotating (non-real) mode must have a triangle with nonzero affinity. -/
theorem rotation_needs_curl [Nonempty ι] (M : Matrix ι ι ℝ) (hM : PosRates M) (h : NoArbitrage M)
    (μ : ℂ) (v : ι → ℂ) (hv : v ≠ 0) (hev : (M.map ((↑) : ℝ → ℂ)) *ᵥ v = μ • v) : μ.im = 0 := by
  obtain ⟨π, hπ, hdb⟩ := (kolmogorov M hM).mpr h
  have hrow : ∀ i, ∑ j, (M i j : ℂ) * v j = μ * v i := by
    intro i
    have := congrFun hev i
    simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using this
  -- the `π`-weighted quadratic form `Q = ⟨v, M v⟩_π`
  set Q : ℂ := ∑ i, ∑ j, ((π i * M i j : ℝ) : ℂ) * (starRingEnd ℂ (v i) * v j) with hQ
  have hQ1 : Q = μ * ((∑ i, π i * Complex.normSq (v i) : ℝ) : ℂ) := by
    simp only [hQ, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∑ j, ((π i * M i j : ℝ) : ℂ) * (starRingEnd ℂ (v i) * v j)
        = (π i : ℂ) * starRingEnd ℂ (v i) * ∑ j, (M i j : ℂ) * v j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast; ring
    rw [this, hrow i, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    ring
  have hQ2 : starRingEnd ℂ Q = Q := by
    simp only [hQ, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hdb j i]
    ring
  have hQim : Q.im = 0 := Complex.conj_eq_iff_im.mp hQ2
  have hN : 0 < ∑ i, π i * Complex.normSq (v i) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hπ j).le (Complex.normSq_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos (hπ i) (Complex.normSq_pos.mpr hi)⟩
  rw [hQ1, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at hQim
  exact (mul_eq_zero.mp hQim).resolve_right hN.ne'

/-- R4 (Born square in the curl-free positive case): with no arbitrage there is a positive
diagonal rescaling `d` making `S i j = d i M i j / d j` symmetric. Each eigenvector `ψ` of `S`
gives a right eigenvector `ψ/d` and a left eigenvector `d ψ` of `M` with the same eigenvalue,
and their entrywise product is `ψ²`. -/
theorem born_square [Nonempty ι] (M : Matrix ι ι ℝ) (hM : PosRates M) (h : NoArbitrage M) :
    ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧
      (Matrix.of (fun i j => d i * M i j / d j))ᵀ = Matrix.of (fun i j => d i * M i j / d j) ∧
      ∀ (lam : ℝ) (ψ : ι → ℝ), Matrix.of (fun i j => d i * M i j / d j) *ᵥ ψ = lam • ψ →
        M *ᵥ (fun i => ψ i / d i) = lam • (fun i => ψ i / d i) ∧
        Mᵀ *ᵥ (fun i => d i * ψ i) = lam • (fun i => d i * ψ i) ∧
        ∀ i, (d i * ψ i) * (ψ i / d i) = ψ i ^ 2 := by
  obtain ⟨π, hπ, hdb⟩ := (kolmogorov M hM).mpr h
  set d : ι → ℝ := fun i => Real.sqrt (π i) with hd
  have hdpos : ∀ i, 0 < d i := fun i => Real.sqrt_pos.mpr (hπ i)
  have hdd : ∀ i j, d i * d i * M i j = d j * d j * M j i := by
    intro i j
    simp only [hd, Real.mul_self_sqrt (hπ i).le, Real.mul_self_sqrt (hπ j).le]
    exact hdb i j
  refine ⟨d, hdpos, ?_, ?_⟩
  · ext i j
    simp only [transpose_apply, of_apply]
    have := (hdpos i).ne'
    have := (hdpos j).ne'
    rw [div_eq_div_iff (hdpos i).ne' (hdpos j).ne']
    linear_combination (hdd j i)
  · intro lam ψ hS
    have hrow : ∀ i, ∑ j, d i * M i j / d j * ψ j = lam * ψ i := by
      intro i
      have := congrFun hS i
      simpa [Matrix.mulVec, dotProduct] using this
    refine ⟨?_, ?_, ?_⟩
    · funext i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      have hi := (hdpos i).ne'
      have : ∑ j, M i j * (ψ j / d j) = (∑ j, d i * M i j / d j * ψ j) / d i := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        have := (hdpos j).ne'
        field_simp
      rw [this, hrow i]
      ring
    · funext i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, transpose_apply]
      have : ∑ j, M j i * (d j * ψ j) = d i * ∑ j, d i * M i j / d j * ψ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have := (hdpos j).ne'
        field_simp
        linear_combination ψ j * hdd j i
      rw [this, hrow i]
      ring
    · intro i
      have := (hdpos i).ne'
      field_simp

/-! ## Part A: norm-preserving amplitudes -/

/-- Helper: `exp (-X) * exp X = 1` for matrices over `ℝ` or `ℂ`. -/
lemma exp_neg_mul_exp_self {𝕜 : Type*} [RCLike 𝕜] (X : Matrix ι ι 𝕜) :
    NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
    NormedSpace.exp_zero]

section OperatorNorm

open scoped Matrix.Norms.Operator

/-- Helper: if `exp (u • A) = 1` for every real `u`, then `A = 0` (differentiate at `u = 0`).
The `L∞` operator norm is chosen locally, only to do calculus. -/
lemma eq_zero_of_exp_smul_eq_one (A : Matrix ι ι ℝ)
    (h : ∀ u : ℝ, NormedSpace.exp (u • A) = 1) : A = 0 := by
  have hd := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at hd
  have hd' : HasDerivAt (fun _ : ℝ => (1 : Matrix ι ι ℝ)) A 0 :=
    hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => (h u).symm)
  exact ((hasDerivAt_const (0 : ℝ) (1 : Matrix ι ι ℝ)).unique hd').symm

end OperatorNorm

/-- A1 (ℝ amplitudes, symmetric generator): if `exp (t • A)` is orthogonal for every `t`,
then `A = 0`. Over ℝ, a self-adjoint generator cannot drive a nontrivial clock. -/
theorem real_symmetric_clock_trivial (A : Matrix ι ι ℝ) (hA : Aᵀ = A)
    (hU : ∀ t : ℝ, NormedSpace.exp (t • A) ∈ Matrix.orthogonalGroup ι ℝ) : A = 0 := by
  have hsq : ∀ t : ℝ, NormedSpace.exp ((t + t) • A) = 1 := by
    intro t
    have h1 := hU t
    rwa [Matrix.mem_orthogonalGroup_iff', ← Matrix.exp_transpose, transpose_smul, hA,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul] at h1
  have hconst : (fun u : ℝ => NormedSpace.exp (u • A)) = fun _ => 1 := by
    funext u
    have := hsq (u / 2)
    rwa [add_halves] at this
  exact eq_zero_of_exp_smul_eq_one A fun u => congrFun hconst u

/-- A2 (ℝ amplitudes, skew generator): real clocks do exist; their generator is skew,
i.e. the rotation sits in the generator. -/
theorem real_skew_clock (A : Matrix ι ι ℝ) (hA : Aᵀ = -A) (t : ℝ) :
    NormedSpace.exp (t • A) ∈ Matrix.orthogonalGroup ι ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff', ← Matrix.exp_transpose, transpose_smul, hA, smul_neg]
  exact exp_neg_mul_exp_self _

/-- A3 (ℂ amplitudes): EVERY self-adjoint generator drives a clock. The rotation sits in the
factor `-i t`, not in the generator. -/
theorem complex_hermitian_clock (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((-(t : ℂ) * I) • H) ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
    conjTranspose_smul, hH.eq]
  have : star (-(t : ℂ) * I) = -(-(t : ℂ) * I) := by
    simp
  rw [this, neg_smul]
  exact exp_neg_mul_exp_self _

/-- A3' (non-vacuity of the contrast): a nonzero self-adjoint complex generator exists, which
A1 rules out over ℝ. -/
theorem complex_hermitian_nonzero_exists :
    ∃ H : Matrix (Fin 2) (Fin 2) ℂ, H.IsHermitian ∧ H ≠ 0 := by
  exact ⟨1, isHermitian_one, one_ne_zero⟩

/-- A4 (no magnitude affinity over ℂ): a Hermitian generator's moduli are symmetric, so every
triangle has zero affinity in the moduli. -/
theorem hermitian_no_magnitude_affinity (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (i j k : ι) :
    ‖H i j‖ * ‖H j k‖ * ‖H k i‖ = ‖H i k‖ * ‖H k j‖ * ‖H j i‖ := by
  have hs : ∀ a b, ‖H a b‖ = ‖H b a‖ := by
    intro a b
    rw [← hH.apply a b, norm_star]
  rw [hs i k, hs k j, hs j i]
  ring

/-- A5 (but curl survives in the phases): a Hermitian matrix can have nonzero phase flux around a
triangle. This is what the signed-walker toy charged for. -/
theorem hermitian_phase_flux_possible :
    ∃ H : Matrix (Fin 3) (Fin 3) ℂ, H.IsHermitian ∧ H 0 1 * H 1 2 * H 2 0 ≠ H 0 2 * H 2 1 * H 1 0 := by
  refine ⟨!![0, I, -I; -I, 0, I; I, -I, 0], ?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  · simp [Complex.ext_iff]
    norm_num

/-- A6 (Born square over ℂ): for Hermitian `H`, each eigenvalue is real and `star ψ` is a left
eigenvector, so left × right = `star ψ i * ψ i = |ψ i|²`. -/
theorem hermitian_born (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (lam : ℂ) (ψ : ι → ℂ)
    (hψ : ψ ≠ 0) (hev : H *ᵥ ψ = lam • ψ) :
    lam.im = 0 ∧ Matrix.vecMul (star ψ) H = lam • star ψ := by
  have hrow : ∀ i, ∑ j, H i j * ψ j = lam * ψ i := by
    intro i
    have := congrFun hev i
    simpa [Matrix.mulVec, dotProduct] using this
  set Q : ℂ := ∑ i, ∑ j, starRingEnd ℂ (ψ i) * H i j * ψ j with hQ
  have hQ1 : Q = lam * ((∑ i, Complex.normSq (ψ i) : ℝ) : ℂ) := by
    simp only [hQ, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∑ j, starRingEnd ℂ (ψ i) * H i j * ψ j
        = starRingEnd ℂ (ψ i) * ∑ j, H i j * ψ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, hrow i, Complex.normSq_eq_conj_mul_self]
    ring
  have hQ2 : starRingEnd ℂ Q = Q := by
    simp only [hQ, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : starRingEnd ℂ (H j i) = H i j := hH.apply i j
    rw [this]
    ring
  have hQim : Q.im = 0 := Complex.conj_eq_iff_im.mp hQ2
  have hN : 0 < ∑ i, Complex.normSq (ψ i) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hψ
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  rw [hQ1, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at hQim
  have hlam : lam.im = 0 := (mul_eq_zero.mp hQim).resolve_right hN.ne'
  refine ⟨hlam, ?_⟩
  have hconj : starRingEnd ℂ lam = lam := Complex.conj_eq_iff_im.mpr hlam
  funext j
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, Pi.star_apply, smul_eq_mul]
  have : ∑ i, star (ψ i) * H i j = starRingEnd ℂ (∑ i, H j i * ψ i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← hH.apply j i]
    simp only [Complex.star_def, Complex.conj_conj]
    ring
  rw [this, hrow j, map_mul, hconj]
  rfl

end CycleClock
