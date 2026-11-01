import Mathlib

/-!
# Linear-response revelation principle for optimizer boundaries

Setting: `n` readers, `m` rewards, real matrices `Matrix (Fin n) (Fin m) ℝ`, expectations are
Bochner integrals against an arbitrary measure `μ` (a probability measure where stated).

PROVED
* `sum_outer_eq_mul`: a sum of `j` outer products `∑ r_l c_lᵀ` equals `R * C` with
  `R : n × j`, `C : j × m`.
* `rank_sum_outer_le`: a sum of `j` outer products has rank at most `j`.
* `exists_outer_decomposition`: every real `W` equals a sum of exactly `rank W` outer products
  `r_l c_lᵀ` (from a basis of the column space).
* `rank_le_of_eq_sum_outer`: if `W` is a sum of `j` outer products then `rank W ≤ j`; so `W` is not
  a sum of fewer than `rank W` outer products.
* `jointCov_posSemidef`: for every `r` and every `d ≥ 0`, the block matrix
  `[[1, rᵀ], [r, r rᵀ + diag d]]` (indexed by `Unit ⊕ Fin n`) is positive semidefinite, via the
  Schur complement `diag d`.
* `jointVec_second_moments`: if `E[ε²] = 1`, `E[ε ξ_j] = 0`, `E[ξ ξᵀ] = diag d`, then the vector
  `(ε, δ)` with `δ_i = r_i ε + ξ_i` has second-moment matrix `jointCov r d`.
* `exists_joint_law`: for every `r` and `d ≥ 0` there is a probability space (uniform measure on
  `Fin (n+1) → Bool`, Rademacher signs) carrying `ε`, `ξ` with `E[ε] = 0`, `Var ε = 1`,
  `E[ξ] = 0`, `E[ε ξ] = 0`, `Cov ξ = diag d`, `E[(ε, δ)] = 0`, and second-moment matrix of
  `(ε, δ)` equal to `[[1, rᵀ], [r, r rᵀ + diag d]]`; in particular `Var ε = 1`, `Cov(ε, δ) = r`.
* `estimator_mean_affine`: if `E[δ_i] = 0`, `E[δ_i δ_j] = σ² Σ_ij` (with the needed
  integrability) and `R_k(x) = b_k + ∑_j G_jk x_j`, then for every `θ : Fin n → ℝ`,
  `E[∑_{i,k} A_ik δ_i R_k(θ + δ)] = ∑_{j,k} W_jk G_jk` with `W = σ² Σ A`.
  No normalisation of `μ` is needed.
* `estimator_mean_quadratic`: the same identity for quadratic rewards written around `θ`,
  `R_k(x) = b_k + ∑_j G_jk (x_j - θ_j) + ∑_{j,l} H_kjl (x_j - θ_j)(x_l - θ_l)`, when all third
  moments `E[δ_i δ_j δ_l]` vanish. Here `G_jk` is the gradient `∂R_k/∂x_j` at `θ`.
* `quadratic_uncentered_counterexample`: the quadratic identity is false if `G` is read as the
  linear coefficient of an uncentered quadratic `b + ∑ G x + ∑ H x x`: with `n = m = 1`,
  Rademacher `δ`, `θ = 1`, `R(x) = x²`, `A = Σ = σ = 1`, all hypotheses hold (including zero third
  moment) but the mean is `2`, not `∑ W G = 0`.
* `directDraw_of_indep`: independence of `ε` and each `ξ_j` (with integrability, `E[ε] = 0`,
  `E[ε²] = s²`) gives the moment hypotheses `DirectDraw` used below; `E[ξ] = 0` is not needed.
* `direct_triple_mean`: if `δ_j = r_j ε + ξ_j`, `E[ε] = 0`, `E[ε²] = s²`, `E[ε ξ_j] = 0` and
  `R_k` is affine with coefficients `G`, then `E[ε ∑_k c_k R_k(θ + δ)] = ∑_{j,k} W_jk G_jk` with
  `W = s² r cᵀ`.
* `eq_of_pairing_eq`: a matrix is determined by its pairings `∑ W_jk G_jk` over all `G`.
* `mixture_rank_le`: if a sum of `J` direct triples `(s_l, r_l, c_l)` has the same mean as `W` for
  every affine reward, then `rank W ≤ J`.
* `direct_triples_realize`: for every `W` there are `rank W` direct triples with `Var ε_l = 1` whose
  summed estimator means equal `∑_{j,k} W_jk G_jk` for every affine reward and every probability
  structure satisfying `DirectDraw`.
* Auxiliary: `unif_isProb`, `integral_unif` (uniform probability on a finite type and its
  integral), `sgn_flip_self`, `sgn_flip_ne`, `sum_sgn`, `sum_sgn_mul` (Rademacher signs have mean
  zero and orthonormal second moments), `reindex_W` (the sum rearrangement giving `σ² Σ A`).

INTERPRETED (not formalized)
* `θ` is taken as a vector, one coordinate per reader; the scalar-`θ` case is the constant vector.
* "Joint law" is realised by an explicit finite law with the required first and second moments;
  independence of `ε` and `ξ` in that law is not proved (only `E[ε ξ_j] = 0`, which is what
  `direct_triple_mean` uses). Gaussian realisations are not formalized.
* That `G` in `estimator_mean_quadratic` is the derivative of `R_k` at `θ` is read off the
  centered form and not proved as a derivative statement. The `O(σ³)` remainder for general smooth
  rewards is not formalized.
-/

open Matrix MeasureTheory

namespace BoundaryRevelationLinearResponse

/-! ### (A) rank decomposition -/

theorem sum_outer_eq_mul {n m j : ℕ} (r : Fin j → Fin n → ℝ) (c : Fin j → Fin m → ℝ) :
    (∑ l, vecMulVec (r l) (c l)) =
      (Matrix.of fun i l => r l i : Matrix (Fin n) (Fin j) ℝ) * Matrix.of fun l k => c l k := by
  ext i k
  simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply]

theorem rank_sum_outer_le {n m j : ℕ} (r : Fin j → Fin n → ℝ) (c : Fin j → Fin m → ℝ) :
    (∑ l, vecMulVec (r l) (c l)).rank ≤ j := by
  rw [sum_outer_eq_mul]
  exact (rank_mul_le_left _ _).trans (rank_le_width _)

theorem exists_outer_decomposition {n m : ℕ} (W : Matrix (Fin n) (Fin m) ℝ) :
    ∃ (r : Fin W.rank → Fin n → ℝ) (c : Fin W.rank → Fin m → ℝ),
      W = ∑ l, vecMulVec (r l) (c l) := by
  set V := LinearMap.range W.mulVecLin
  let b : Module.Basis (Fin W.rank) ℝ V := Module.finBasisOfFinrankEq ℝ V rfl
  have hcol : ∀ k : Fin m, (fun i => W i k) ∈ V := by
    intro k
    refine ⟨Pi.single k 1, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine ⟨fun l => (b l : Fin n → ℝ), fun l k => b.repr ⟨_, hcol k⟩ l, ?_⟩
  ext i k
  have h := congrArg (fun v : V => (v : Fin n → ℝ) i) (b.sum_repr ⟨_, hcol k⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  rw [Matrix.sum_apply]
  simp only [vecMulVec_apply]
  rw [← h]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem rank_le_of_eq_sum_outer {n m j : ℕ} (W : Matrix (Fin n) (Fin m) ℝ)
    (r : Fin j → Fin n → ℝ) (c : Fin j → Fin m → ℝ) (h : W = ∑ l, vecMulVec (r l) (c l)) :
    W.rank ≤ j := h ▸ rank_sum_outer_le r c

/-! ### (B) block covariance -/

/-- The joint second-moment matrix of `(ε, δ)`, indexed by `Unit ⊕ Fin n`. -/
noncomputable def jointCov {n : ℕ} (r d : Fin n → ℝ) : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ :=
  fromBlocks 1 (replicateRow Unit r) (replicateCol Unit r) (vecMulVec r r + diagonal d)

theorem jointCov_posSemidef {n : ℕ} (r d : Fin n → ℝ) (hd : 0 ≤ d) :
    (jointCov r d).PosSemidef := by
  have hB : (replicateRow Unit r)ᴴ = replicateCol Unit r := by
    simp
  let _ : Invertible (1 : Matrix Unit Unit ℝ) := invertibleOne
  unfold jointCov
  rw [← hB, PosDef.fromBlocks₁₁ _ _ PosDef.one, hB, inv_one, Matrix.mul_one]
  have : vecMulVec r r + diagonal d - replicateCol Unit r * replicateRow Unit r = diagonal d := by
    rw [← vecMulVec_eq Unit]; abel
  rw [this]
  exact PosSemidef.diagonal hd

/-! ### (B) a joint law with the block covariance -/

section JointLaw

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The vector `(ε, δ)` with `δ_i = r_i ε + ξ_i`, indexed by `Unit ⊕ Fin n`. -/
def jointVec {n : ℕ} (r : Fin n → ℝ) (ε : Ω → ℝ) (ξ : Fin n → Ω → ℝ) :
    Unit ⊕ Fin n → Ω → ℝ :=
  Sum.elim (fun _ => ε) (fun i ω => r i * ε ω + ξ i ω)

theorem jointVec_second_moments {n : ℕ} (r d : Fin n → ℝ) (ε : Ω → ℝ) (ξ : Fin n → Ω → ℝ)
    (hεε : Integrable (fun ω => ε ω * ε ω) μ) (hεξ : ∀ j, Integrable (fun ω => ε ω * ξ j ω) μ)
    (hξξ : ∀ i j, Integrable (fun ω => ξ i ω * ξ j ω) μ)
    (hvar : ∫ ω, ε ω * ε ω ∂μ = 1) (hunc : ∀ j, ∫ ω, ε ω * ξ j ω ∂μ = 0)
    (hξcov : ∀ i j, ∫ ω, ξ i ω * ξ j ω ∂μ = diagonal d i j) :
    ∀ a b, ∫ ω, jointVec r ε ξ a ω * jointVec r ε ξ b ω ∂μ = jointCov r d a b := by
  have hεZ : ∀ j, ∫ ω, ε ω * (r j * ε ω + ξ j ω) ∂μ = r j := fun j => by
    have e : (fun ω => ε ω * (r j * ε ω + ξ j ω)) =
        fun ω => r j * (ε ω * ε ω) + ε ω * ξ j ω := funext fun ω => by ring
    rw [e, integral_add (hεε.const_mul _) (hεξ j), integral_const_mul, hvar, hunc]; ring
  rintro (u | i) (v | j)
  · simpa [jointVec, jointCov] using hvar
  · simpa [jointVec, jointCov] using hεZ j
  · have e : (fun ω => (r i * ε ω + ξ i ω) * ε ω) = fun ω => ε ω * (r i * ε ω + ξ i ω) :=
      funext fun ω => by ring
    simpa [jointVec, jointCov, e] using hεZ i
  · have e : (fun ω => (r i * ε ω + ξ i ω) * (r j * ε ω + ξ j ω)) =
        fun ω => ((r i * r j) * (ε ω * ε ω) + r i * (ε ω * ξ j ω)) +
          (r j * (ε ω * ξ i ω) + ξ i ω * ξ j ω) := funext fun ω => by ring
    have hA : Integrable (fun ω => (r i * r j) * (ε ω * ε ω) + r i * (ε ω * ξ j ω)) μ :=
      (hεε.const_mul _).add ((hεξ j).const_mul _)
    have hB : Integrable (fun ω => r j * (ε ω * ξ i ω) + ξ i ω * ξ j ω) μ :=
      ((hεξ i).const_mul _).add (hξξ i j)
    simp only [jointVec, Sum.elim_inr, jointCov, fromBlocks_apply₂₂, Matrix.add_apply,
      vecMulVec_apply]
    rw [e, integral_add hA hB, integral_add (hεε.const_mul _) ((hεξ j).const_mul _),
      integral_add ((hεξ i).const_mul _) (hξξ i j)]
    simp only [integral_const_mul, hvar, hunc, hξcov]
    ring

end JointLaw

/-- Uniform probability on a finite type. -/
noncomputable def unif (α : Type*) [Fintype α] [MeasurableSpace α] : Measure α :=
  ((Fintype.card α : ENNReal)⁻¹) • Measure.count

theorem unif_isProb (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] : IsProbabilityMeasure (unif α) := by
  constructor
  rw [unif, Measure.smul_apply, Measure.count_univ, smul_eq_mul]
  simp [ENat.card_eq_coe_fintype_card]
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

theorem integral_unif {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → ℝ) : ∫ a, f a ∂(unif α) = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  rw [unif, integral_smul_measure, integral_count, smul_eq_mul]
  simp

/-- A Rademacher sign attached to coordinate `a`. -/
def sgn {N : ℕ} (a : Fin N) (ω : Fin N → Bool) : ℝ := if ω a then 1 else -1

/-- Flipping coordinate `a`. -/
def flipFun {N : ℕ} (a : Fin N) (ω : Fin N → Bool) : Fin N → Bool := Function.update ω a (!ω a)

/-- Flipping coordinate `a`, as a permutation. -/
def flipAt {N : ℕ} (a : Fin N) : Equiv.Perm (Fin N → Bool) :=
  Function.Involutive.toPerm (flipFun a) fun ω => by
    unfold flipFun
    funext x
    by_cases h : x = a
    · subst h; simp
    · simp [Function.update_of_ne h]

theorem sgn_flip_self {N : ℕ} (a : Fin N) (ω : Fin N → Bool) :
    sgn a (flipAt a ω) = -sgn a ω := by
  change sgn a (flipFun a ω) = -sgn a ω
  simp only [flipFun, sgn, Function.update_self]
  cases ω a <;> simp

theorem sgn_flip_ne {N : ℕ} {a b : Fin N} (h : b ≠ a) (ω : Fin N → Bool) :
    sgn b (flipAt a ω) = sgn b ω := by
  change sgn b (flipFun a ω) = sgn b ω
  simp only [flipFun, sgn, Function.update_of_ne h]

theorem sum_sgn {N : ℕ} (a : Fin N) : ∑ ω, sgn a ω = 0 := by
  have h := Equiv.sum_comp (flipAt a) (sgn a)
  simp only [sgn_flip_self, Finset.sum_neg_distrib] at h
  linarith

theorem sum_sgn_mul {N : ℕ} (a b : Fin N) :
    ∑ ω, sgn a ω * sgn b ω = if a = b then (Fintype.card (Fin N → Bool) : ℝ) else 0 := by
  split_ifs with hab
  · subst hab
    have : ∀ ω, sgn a ω * sgn a ω = 1 := fun ω => by unfold sgn; split_ifs <;> norm_num
    simp [this]
  · have h := Equiv.sum_comp (flipAt a) (fun ω => sgn a ω * sgn b ω)
    simp only [sgn_flip_self, sgn_flip_ne (Ne.symm hab), neg_mul, Finset.sum_neg_distrib] at h
    linarith

theorem exists_joint_law {n : ℕ} (r d : Fin n → ℝ) (hd : 0 ≤ d) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (ε : Ω → ℝ) (ξ : Fin n → Ω → ℝ),
      IsProbabilityMeasure μ ∧ (∀ f : Ω → ℝ, Integrable f μ) ∧
      ∫ ω, ε ω ∂μ = 0 ∧ ∫ ω, ε ω * ε ω ∂μ = 1 ∧ (∀ i, ∫ ω, ξ i ω ∂μ = 0) ∧
      (∀ i, ∫ ω, ε ω * ξ i ω ∂μ = 0) ∧ (∀ i j, ∫ ω, ξ i ω * ξ j ω ∂μ = diagonal d i j) ∧
      (∀ a, ∫ ω, jointVec r ε ξ a ω ∂μ = 0) ∧
      ∀ a b, ∫ ω, jointVec r ε ξ a ω * jointVec r ε ξ b ω ∂μ = jointCov r d a b := by
  have := unif_isProb (Fin (n + 1) → Bool)
  have hc : (Fintype.card (Fin (n + 1) → Bool) : ℝ) ≠ 0 := by positivity
  have hint : ∀ f : (Fin (n + 1) → Bool) → ℝ, Integrable f (unif _) := fun f =>
    Integrable.of_finite
  have m1 : ∀ a : Fin (n + 1), ∫ ω, sgn a ω ∂(unif _) = 0 := fun a => by rw [integral_unif, sum_sgn, mul_zero]
  have m2 : ∀ a b : Fin (n + 1), ∫ ω, sgn a ω * sgn b ω ∂(unif _) = if a = b then 1 else 0 := fun a b => by
    rw [integral_unif, sum_sgn_mul]; split_ifs
    · exact inv_mul_cancel₀ hc
    · rw [mul_zero]
  let ε : (Fin (n + 1) → Bool) → ℝ := sgn 0
  let ξ : Fin n → (Fin (n + 1) → Bool) → ℝ := fun i ω => Real.sqrt (d i) * sgn i.succ ω
  have hε : ∫ ω, ε ω ∂(unif _) = 0 := m1 0
  have hεε : ∫ ω, ε ω * ε ω ∂(unif _) = 1 := by simp [ε, m2]
  have hξ : ∀ i, ∫ ω, ξ i ω ∂(unif _) = 0 := fun i => by
    simp only [ξ, integral_const_mul, m1, mul_zero]
  have hεξ : ∀ i, ∫ ω, ε ω * ξ i ω ∂(unif _) = 0 := fun i => by
    have e : (fun ω => ε ω * ξ i ω) = fun ω => Real.sqrt (d i) * (sgn 0 ω * sgn i.succ ω) :=
      funext fun ω => by simp only [ε, ξ]; ring
    rw [e, integral_const_mul, m2]
    simp [(Fin.succ_ne_zero i).symm]
  have hξξ : ∀ i j, ∫ ω, ξ i ω * ξ j ω ∂(unif _) = diagonal d i j := fun i j => by
    have e : (fun ω => ξ i ω * ξ j ω) =
        fun ω => (Real.sqrt (d i) * Real.sqrt (d j)) * (sgn i.succ ω * sgn j.succ ω) :=
      funext fun ω => by simp only [ξ]; ring
    rw [e, integral_const_mul, m2, diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [Real.mul_self_sqrt (hd i)]
    · simp [hij, Fin.succ_inj]
  refine ⟨_, inferInstance, unif _, ε, ξ, inferInstance, hint, hε, hεε, hξ, hεξ, hξξ, ?_,
    jointVec_second_moments r d ε ξ (hint _) (fun _ => hint _) (fun _ _ => hint _) hεε hεξ hξξ⟩
  rintro (u | i)
  · simpa [jointVec] using hε
  · simp only [jointVec, Sum.elim_inr]
    rw [integral_add ((hint _).const_mul _) (hint _), integral_const_mul, hε, hξ]; ring

/-! ### (C) mean of a linear randomized scheme -/

section Estimator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem reindex_W {n m : ℕ} {σ : ℝ} {S : Matrix (Fin n) (Fin n) ℝ} {A G : Matrix (Fin n) (Fin m) ℝ}
    (hsym : ∀ i j, σ ^ 2 * S i j = σ ^ 2 * S j i) :
    ∑ i, ∑ k, ∑ j, A i k * G j k * (σ ^ 2 * S i j) = ∑ j, ∑ k, (σ ^ 2 • (S * A)) j k * G j k :=
  calc ∑ i, ∑ k, ∑ j, A i k * G j k * (σ ^ 2 * S i j)
      = ∑ i, ∑ j, ∑ k, A i k * G j k * (σ ^ 2 * S i j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ k, A i k * G j k * (σ ^ 2 * S i j) := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, A i k * G j k * (σ ^ 2 * S i j) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ k, (σ ^ 2 • (S * A)) j k * G j k := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsym]; ring

theorem estimator_mean_affine {n m : ℕ} (δ : Fin n → Ω → ℝ) (σ : ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (A G : Matrix (Fin n) (Fin m) ℝ) (θ : Fin n → ℝ)
    (b : Fin m → ℝ) (R : Fin m → (Fin n → ℝ) → ℝ)
    (hR : ∀ k x, R k x = b k + ∑ j, G j k * x j)
    (h1 : ∀ i, Integrable (δ i) μ) (h2 : ∀ i j, Integrable (fun ω => δ i ω * δ j ω) μ)
    (hmean : ∀ i, ∫ ω, δ i ω ∂μ = 0)
    (hcov : ∀ i j, ∫ ω, δ i ω * δ j ω ∂μ = σ ^ 2 * S i j) :
    ∫ ω, ∑ i, ∑ k, A i k * δ i ω * R k (fun j => θ j + δ j ω) ∂μ =
      ∑ j, ∑ k, (σ ^ 2 • (S * A)) j k * G j k := by
  have hsym : ∀ i j, σ ^ 2 * S i j = σ ^ 2 * S j i := fun i j => by
    rw [← hcov, ← hcov]; simp only [mul_comm]
  have hpt : ∀ ω, (∑ i, ∑ k, A i k * δ i ω * R k (fun j => θ j + δ j ω)) =
      ∑ i, ∑ k, ((A i k * (b k + ∑ j, G j k * θ j)) * δ i ω +
        ∑ j, (A i k * G j k) * (δ i ω * δ j ω)) := by
    intro ω
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    have e1 : ∑ j, G j k * (θ j + δ j ω) = ∑ j, G j k * θ j + ∑ j, G j k * δ j ω := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ j, (A i k * G j k) * (δ i ω * δ j ω) = A i k * δ i ω * ∑ j, G j k * δ j ω := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hR, e1, e2]; ring
  simp_rw [hpt]
  have hI : ∀ i k, Integrable (fun ω => (A i k * (b k + ∑ j, G j k * θ j)) * δ i ω +
        ∑ j, (A i k * G j k) * (δ i ω * δ j ω)) μ := fun i k =>
    ((h1 i).const_mul _).add (integrable_finsetSum _ fun j _ => (h2 i j).const_mul _)
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hI i k]
  simp_rw [integral_finsetSum _ fun k _ => hI _ k]
  simp_rw [integral_add ((h1 _).const_mul _)
    (integrable_finsetSum _ fun j _ => (h2 _ j).const_mul _)]
  simp_rw [integral_finsetSum _ fun j _ => (h2 _ j).const_mul _, integral_const_mul, hmean, hcov]
  simp only [mul_zero, zero_add]
  exact reindex_W hsym

theorem estimator_mean_quadratic {n m : ℕ} (δ : Fin n → Ω → ℝ) (σ : ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (A G : Matrix (Fin n) (Fin m) ℝ) (θ : Fin n → ℝ)
    (b : Fin m → ℝ) (H : Fin m → Fin n → Fin n → ℝ) (R : Fin m → (Fin n → ℝ) → ℝ)
    (hR : ∀ k x, R k x = b k + ∑ j, G j k * (x j - θ j) +
      ∑ j, ∑ l, H k j l * ((x j - θ j) * (x l - θ l)))
    (h1 : ∀ i, Integrable (δ i) μ) (h2 : ∀ i j, Integrable (fun ω => δ i ω * δ j ω) μ)
    (h3 : ∀ i j l, Integrable (fun ω => δ i ω * δ j ω * δ l ω) μ)
    (hmean : ∀ i, ∫ ω, δ i ω ∂μ = 0)
    (hcov : ∀ i j, ∫ ω, δ i ω * δ j ω ∂μ = σ ^ 2 * S i j)
    (hthird : ∀ i j l, ∫ ω, δ i ω * δ j ω * δ l ω ∂μ = 0) :
    ∫ ω, ∑ i, ∑ k, A i k * δ i ω * R k (fun j => θ j + δ j ω) ∂μ =
      ∑ j, ∑ k, (σ ^ 2 • (S * A)) j k * G j k := by
  have hsym : ∀ i j, σ ^ 2 * S i j = σ ^ 2 * S j i := fun i j => by
    rw [← hcov, ← hcov]; simp only [mul_comm]
  have hpt : ∀ ω, (∑ i, ∑ k, A i k * δ i ω * R k (fun j => θ j + δ j ω)) =
      ∑ i, ∑ k, ((A i k * b k) * δ i ω + ∑ j, (A i k * G j k) * (δ i ω * δ j ω) +
        ∑ j, ∑ l, (A i k * H k j l) * (δ i ω * δ j ω * δ l ω)) := by
    intro ω
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    have e2 : ∑ j, (A i k * G j k) * (δ i ω * δ j ω) = A i k * δ i ω * ∑ j, G j k * δ j ω := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have e3 : ∑ j, ∑ l, (A i k * H k j l) * (δ i ω * δ j ω * δ l ω) =
        A i k * δ i ω * ∑ j, ∑ l, H k j l * (δ j ω * δ l ω) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hR, e2, e3]
    simp only [add_sub_cancel_left]
    ring
  simp_rw [hpt]
  have hI2 : ∀ i k, Integrable (fun ω => ∑ j, (A i k * G j k) * (δ i ω * δ j ω)) μ :=
    fun i k => integrable_finsetSum _ fun j _ => (h2 i j).const_mul _
  have hI3' : ∀ i k j, Integrable
      (fun ω => ∑ l, (A i k * H k j l) * (δ i ω * δ j ω * δ l ω)) μ :=
    fun i k j => integrable_finsetSum _ fun l _ => (h3 i j l).const_mul _
  have hI3 : ∀ i k, Integrable
      (fun ω => ∑ j, ∑ l, (A i k * H k j l) * (δ i ω * δ j ω * δ l ω)) μ :=
    fun i k => integrable_finsetSum _ fun j _ => hI3' i k j
  have hA : ∀ i k, Integrable (fun ω => (A i k * b k) * δ i ω +
      ∑ j, (A i k * G j k) * (δ i ω * δ j ω)) μ := fun i k =>
    ((h1 i).const_mul _).add (hI2 i k)
  have hI : ∀ i k, Integrable (fun ω => (A i k * b k) * δ i ω +
      ∑ j, (A i k * G j k) * (δ i ω * δ j ω) +
        ∑ j, ∑ l, (A i k * H k j l) * (δ i ω * δ j ω * δ l ω)) μ := fun i k =>
    (hA i k).add (hI3 i k)
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hI i k]
  refine (Finset.sum_congr rfl fun i _ => ?_).trans (reindex_W hsym)
  rw [integral_finsetSum _ fun k _ => hI i k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_add (hA i k) (hI3 i k),
    integral_add ((h1 i).const_mul _) (hI2 i k), integral_const_mul, hmean,
    integral_finsetSum _ fun j _ => (h2 i j).const_mul _,
    integral_finsetSum _ fun j _ => hI3' i k j]
  have h3z : ∀ j, ∫ ω, ∑ l, (A i k * H k j l) * (δ i ω * δ j ω * δ l ω) ∂μ = 0 := fun j => by
    rw [integral_finsetSum _ fun l _ => (h3 i j l).const_mul _]
    exact Finset.sum_eq_zero fun l _ => by rw [integral_const_mul, hthird, mul_zero]
  simp only [h3z, Finset.sum_const_zero, add_zero, mul_zero, zero_add, integral_const_mul, hcov]

/-! ### The uncentered quadratic reading fails -/

theorem quadratic_uncentered_counterexample :
    ∃ (μ : Measure Bool) (δ : Fin 1 → Bool → ℝ),
      IsProbabilityMeasure μ ∧ (∀ f : Bool → ℝ, Integrable f μ) ∧
      (∀ i, ∫ ω, δ i ω ∂μ = 0) ∧
      (∀ i j, ∫ ω, δ i ω * δ j ω ∂μ = (1 : ℝ) ^ 2 * (1 : Matrix (Fin 1) (Fin 1) ℝ) i j) ∧
      (∀ i j l, ∫ ω, δ i ω * δ j ω * δ l ω ∂μ = 0) ∧
      ∫ ω, ∑ i, ∑ k : Fin 1, (1 : Matrix (Fin 1) (Fin 1) ℝ) i k * δ i ω *
          (0 + ∑ j, (0 : Matrix (Fin 1) (Fin 1) ℝ) j k * (1 + δ j ω) +
            ∑ j, ∑ l, (1 + δ j ω) * (1 + δ l ω)) ∂μ ≠
        ∑ j, ∑ k, (((1 : ℝ) ^ 2 • ((1 : Matrix (Fin 1) (Fin 1) ℝ) * 1) :
          Matrix (Fin 1) (Fin 1) ℝ)) j k *
          (0 : Matrix (Fin 1) (Fin 1) ℝ) j k := by
  have := unif_isProb Bool
  refine ⟨unif Bool, fun _ ω => if ω then 1 else -1, inferInstance, fun f => Integrable.of_finite,
    ?_, ?_, ?_, ?_⟩
  · intro i; rw [integral_unif]; simp
  · intro i j; rw [integral_unif]; fin_cases i; fin_cases j; simp; norm_num
  · intro i j l; rw [integral_unif]; simp
  · rw [integral_unif]; simp

/-! ### (D) direct triples -/

/-- Moment hypotheses on a shared draw `ε` and private noise `ξ` used by a direct triple:
integrability of the needed products, `E[ε] = 0`, `E[ε²] = s²`, and `E[ε ξ_j] = 0`. -/
def DirectDraw {n : ℕ} (μ : Measure Ω) (ε : Ω → ℝ) (ξ : Fin n → Ω → ℝ) (s : ℝ) : Prop :=
  Integrable ε μ ∧ Integrable (fun ω => ε ω * ε ω) μ ∧
    (∀ j, Integrable (fun ω => ε ω * ξ j ω) μ) ∧ ∫ ω, ε ω ∂μ = 0 ∧
      ∫ ω, ε ω * ε ω ∂μ = s ^ 2 ∧ ∀ j, ∫ ω, ε ω * ξ j ω ∂μ = 0

theorem directDraw_of_indep {n : ℕ} (ε : Ω → ℝ) (ξ : Fin n → Ω → ℝ) (s : ℝ)
    (hε : Integrable ε μ) (hεε : Integrable (fun ω => ε ω * ε ω) μ)
    (hξ : ∀ j, Integrable (ξ j) μ) (hind : ∀ j, ProbabilityTheory.IndepFun ε (ξ j) μ)
    (hmean : ∫ ω, ε ω ∂μ = 0) (hvar : ∫ ω, ε ω * ε ω ∂μ = s ^ 2) :
    DirectDraw μ ε ξ s :=
  ⟨hε, hεε, fun j => (hind j).integrable_mul hε (hξ j), hmean, hvar, fun j => by
    rw [(hind j).integral_fun_mul_eq_mul_integral hε.aestronglyMeasurable
      (hξ j).aestronglyMeasurable, hmean, zero_mul]⟩

theorem direct_triple_mean {n m : ℕ} (ε : Ω → ℝ) (ξ : Fin n → Ω → ℝ) (s : ℝ)
    (r : Fin n → ℝ) (c : Fin m → ℝ) (θ : Fin n → ℝ) (b : Fin m → ℝ)
    (G : Matrix (Fin n) (Fin m) ℝ) (R : Fin m → (Fin n → ℝ) → ℝ)
    (hR : ∀ k x, R k x = b k + ∑ j, G j k * x j) (h : DirectDraw μ ε ξ s) :
    ∫ ω, ε ω * ∑ k, c k * R k (fun j => θ j + (r j * ε ω + ξ j ω)) ∂μ =
      ∑ j, ∑ k, (s ^ 2 • vecMulVec r c) j k * G j k := by
  obtain ⟨hε, hεε, hεξ, hmean, hvar, hunc⟩ := h
  have hpt : ∀ ω, ε ω * ∑ k, c k * R k (fun j => θ j + (r j * ε ω + ξ j ω)) =
      ∑ k, ((c k * (b k + ∑ j, G j k * θ j)) * ε ω +
        ∑ j, (c k * G j k * r j) * (ε ω * ε ω) + ∑ j, (c k * G j k) * (ε ω * ξ j ω)) := by
    intro ω
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : ∑ j, G j k * (θ j + (r j * ε ω + ξ j ω)) =
        ∑ j, G j k * θ j + ∑ j, G j k * r j * ε ω + ∑ j, G j k * ξ j ω := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ j, (c k * G j k * r j) * (ε ω * ε ω) = c k * ε ω * ∑ j, G j k * r j * ε ω := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have e3 : ∑ j, (c k * G j k) * (ε ω * ξ j ω) = c k * ε ω * ∑ j, G j k * ξ j ω := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hR, e1, e2, e3]; ring
  simp_rw [hpt]
  have hI2 : ∀ k, Integrable (fun ω => ∑ j, (c k * G j k * r j) * (ε ω * ε ω)) μ :=
    fun k => integrable_finsetSum _ fun j _ => hεε.const_mul _
  have hI3 : ∀ k, Integrable (fun ω => ∑ j, (c k * G j k) * (ε ω * ξ j ω)) μ :=
    fun k => integrable_finsetSum _ fun j _ => (hεξ j).const_mul _
  have hA : ∀ k, Integrable (fun ω => (c k * (b k + ∑ j, G j k * θ j)) * ε ω +
      ∑ j, (c k * G j k * r j) * (ε ω * ε ω)) μ :=
    fun k => (hε.const_mul _).add (hI2 k)
  have hI : ∀ k, Integrable (fun ω => (c k * (b k + ∑ j, G j k * θ j)) * ε ω +
      ∑ j, (c k * G j k * r j) * (ε ω * ε ω) + ∑ j, (c k * G j k) * (ε ω * ξ j ω)) μ :=
    fun k => (hA k).add (hI3 k)
  rw [integral_finsetSum _ fun k _ => hI k]
  have hk : ∀ k, ∫ ω, ((c k * (b k + ∑ j, G j k * θ j)) * ε ω +
      ∑ j, (c k * G j k * r j) * (ε ω * ε ω) + ∑ j, (c k * G j k) * (ε ω * ξ j ω)) ∂μ =
        ∑ j, c k * G j k * r j * s ^ 2 := fun k => by
    rw [integral_add (hA k) (hI3 k),
      integral_add (hε.const_mul _) (hI2 k), integral_const_mul, hmean,
      integral_finsetSum _ fun j _ => hεε.const_mul _,
      integral_finsetSum _ fun j _ => (hεξ j).const_mul _]
    simp only [integral_const_mul, hvar, hunc, mul_zero, zero_add, Finset.sum_const_zero, add_zero]
  simp only [hk]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]; ring

end Estimator

/-! ### Mixtures of direct triples -/

theorem eq_of_pairing_eq {n m : ℕ} {W W' : Matrix (Fin n) (Fin m) ℝ}
    (h : ∀ G : Matrix (Fin n) (Fin m) ℝ, ∑ j, ∑ k, W' j k * G j k = ∑ j, ∑ k, W j k * G j k) :
    W' = W := by
  ext a b
  have := h (Matrix.single a b 1)
  simpa [Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq'] using this

theorem mixture_rank_le {n m J : ℕ} (W : Matrix (Fin n) (Fin m) ℝ) (s : Fin J → ℝ)
    (r : Fin J → Fin n → ℝ) (c : Fin J → Fin m → ℝ)
    (h : ∀ G : Matrix (Fin n) (Fin m) ℝ,
      ∑ l, ∑ j, ∑ k, (s l ^ 2 • vecMulVec (r l) (c l)) j k * G j k =
        ∑ j, ∑ k, W j k * G j k) :
    W.rank ≤ J := by
  refine rank_le_of_eq_sum_outer W (fun l => s l ^ 2 • r l) c ?_
  refine (eq_of_pairing_eq fun G => ?_).symm
  rw [← h G]
  have e : ∀ j k, (∑ l, vecMulVec ((fun l => s l ^ 2 • r l) l) (c l)) j k * G j k =
      ∑ l, (s l ^ 2 • vecMulVec (r l) (c l)) j k * G j k := fun j k => by
    rw [Matrix.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [e]
  exact (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans Finset.sum_comm

universe u

theorem direct_triples_realize {n m : ℕ} (W : Matrix (Fin n) (Fin m) ℝ) :
    ∃ (r : Fin W.rank → Fin n → ℝ) (c : Fin W.rank → Fin m → ℝ),
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (ε : Fin W.rank → Ω → ℝ)
        (ξ : Fin W.rank → Fin n → Ω → ℝ) (θ : Fin n → ℝ) (b : Fin m → ℝ)
        (G : Matrix (Fin n) (Fin m) ℝ) (R : Fin m → (Fin n → ℝ) → ℝ),
        (∀ k x, R k x = b k + ∑ j, G j k * x j) → (∀ l, DirectDraw μ (ε l) (ξ l) 1) →
        ∑ l, ∫ ω, ε l ω * ∑ k, c l k * R k (fun j => θ j + (r l j * ε l ω + ξ l j ω)) ∂μ =
          ∑ j, ∑ k, W j k * G j k := by
  obtain ⟨r, c, hW⟩ := exists_outer_decomposition W
  refine ⟨r, c, fun μ ε ξ θ b G R hR hD => ?_⟩
  have hl : ∀ l, ∫ ω, ε l ω * ∑ k, c l k * R k (fun j => θ j + (r l j * ε l ω + ξ l j ω)) ∂μ =
      ∑ j, ∑ k, ((1 : ℝ) ^ 2 • vecMulVec (r l) (c l)) j k * G j k := fun l =>
    direct_triple_mean (ε l) (ξ l) 1 (r l) (c l) θ b G R hR (hD l)
  simp only [hl, one_pow, one_smul]
  conv_rhs => rw [hW]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.sum_apply, Finset.sum_mul]

end BoundaryRevelationLinearResponse
