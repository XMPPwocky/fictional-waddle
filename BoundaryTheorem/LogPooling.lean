import Mathlib

/-!
# Log-linear pooling is the externally Bayesian pooling rule

Fidelity record: `FIDELITY_log_pooling.md`.

Setting: a finite outcome/type space `X`, a finite set of members `ι`. Each member holds a strictly positive
probability vector `P i : X → ℝ`. Evidence is a strictly positive likelihood `ℓ : X → ℝ`, and the update is
`bayes p ℓ = normalize (p · ℓ)` (= the discrete replicator step with fitness `ℓ`).

* **Claim 1** `geoPool_bayes` / `geoPool_externallyBayesian`: geometric pooling with `∑ w = 1` commutes with the
  update; `geoPool_externallyBayesian_iff`: for `|X| ≥ 2` this holds iff `∑ w = 1`.
  `geoPool_bayes_hetero` is the identity for member-specific likelihoods (pooled likelihood `∏ ℓᵢ^{wᵢ}`).
* **Claim 2** `linPool_counterexample` (2 members, 2 outcomes); exact criteria `linPool_bayes_iff`,
  `linPool_two_bayes_iff` (two members: commutes iff `w₀ w₁ (c₁ - c₀) = 0`, `cᵢ` = evidence probability);
  `linPool_externallyBayesian_iff` (nonnegative weights, `|X| ≥ 2`: EB iff dictatorship).
* **Claim 3** (uniqueness) for pointwise pools `T(P)(x) ∝ g x (P₁(x),…,Pₙ(x))`, `|X| ≥ 3`:
  `eb_additive_form` (no regularity: `g x u = K x · exp(H(log u))`, `H` additive, `H(σ𝟙) = σ`),
  `pool_eb_of_additive_form` (converse), `eb_loglinear` (continuity of one `g x₀` ⇒ `g x u = K x ∏ uᵢ^{wᵢ}`,
  `∑ w = 1`), `pool_eb_iff_loglinear`, operator forms `pool_eq_genGeoPool`, `pool_eq_geoPool`.
  Necessity of `|X| ≥ 3`: `two_point_counterexample`.
* **Claim 4** (credit routing): `geoPool_smul_invariant`, `linPool_joint_renormalization`,
  `mixture_bayes`, `kellyPayout_eq_bayes`, `kelly_log_optimal`, `geoPool_softmax`, `pool_linear_eq_linPool`.
-/

open Finset Real Filter Topology

namespace BoundaryTheorem.LogPooling

set_option linter.unusedSectionVars false

variable {X ι : Type*} [Fintype X] [Fintype ι]

/-! ## Basic objects -/

/-- Divide a vector by its total. -/
noncomputable def normalize (v : X → ℝ) : X → ℝ := fun x => v x / ∑ y, v y

/-- Bayes / replicator step: multiply by the likelihood (fitness) `ℓ`, then renormalize. -/
noncomputable def bayes (p ℓ : X → ℝ) : X → ℝ := normalize (fun x => p x * ℓ x)

/-- Strictly positive probability vector. -/
def IsDist (p : X → ℝ) : Prop := (∀ x, 0 < p x) ∧ ∑ x, p x = 1

/-- Pointwise pooling operator: `T(P)(x) ∝ g x (P₁(x), …, Pₙ(x))`. -/
noncomputable def pool (g : X → (ι → ℝ) → ℝ) (P : ι → X → ℝ) : X → ℝ :=
  normalize (fun x => g x (fun i => P i x))

/-- Log-linear (geometric) pooling `T(P)(x) ∝ ∏ᵢ Pᵢ(x)^{wᵢ}`. -/
noncomputable def geoPool (w : ι → ℝ) (P : ι → X → ℝ) : X → ℝ :=
  normalize (fun x => ∏ i, P i x ^ w i)

/-- Generalized log-linear pooling `T(P)(x) ∝ K(x) ∏ᵢ Pᵢ(x)^{wᵢ}`. -/
noncomputable def genGeoPool (K : X → ℝ) (w : ι → ℝ) (P : ι → X → ℝ) : X → ℝ :=
  normalize (fun x => K x * ∏ i, P i x ^ w i)

/-- Linear pooling `T(P)(x) = ∑ᵢ wᵢ Pᵢ(x)` (a probability vector when `∑ w = 1` and the `Pᵢ` are). -/
def linPool (w : ι → ℝ) (P : ι → X → ℝ) : X → ℝ := fun x => ∑ i, w i * P i x

/-- **External Bayesianity** (Madansky 1964): for every profile of strictly positive probability vectors and
every strictly positive likelihood common to all members, pooling the updated members equals updating the
pool. -/
def ExternallyBayesian (T : (ι → X → ℝ) → X → ℝ) : Prop :=
  ∀ P : ι → X → ℝ, (∀ i, IsDist (P i)) → ∀ ℓ : X → ℝ, (∀ x, 0 < ℓ x) →
    T (fun i => bayes (P i) ℓ) = bayes (T P) ℓ

/-- Evidence probability `cᵢ = ∑ₓ Pᵢ(x) ℓ(x)` (the normalizer of member `i`'s update). -/
def evid (p ℓ : X → ℝ) : ℝ := ∑ x, p x * ℓ x

/-! ## Normalization lemmas -/

theorem sum_pos_of_pos [Nonempty X] {v : X → ℝ} (hv : ∀ x, 0 < v x) : 0 < ∑ x, v x :=
  Finset.sum_pos (fun x _ => hv x) Finset.univ_nonempty

theorem normalize_pos [Nonempty X] {v : X → ℝ} (hv : ∀ x, 0 < v x) (x : X) : 0 < normalize v x :=
  div_pos (hv x) (sum_pos_of_pos hv)

theorem isDist_normalize [Nonempty X] {v : X → ℝ} (hv : ∀ x, 0 < v x) : IsDist (normalize v) := by
  refine ⟨normalize_pos hv, ?_⟩
  simp only [normalize, ← Finset.sum_div]
  exact div_self (sum_pos_of_pos hv).ne'

theorem normalize_smul {v : X → ℝ} {c : ℝ} (hc : c ≠ 0) :
    normalize (fun x => c * v x) = normalize v := by
  funext x
  simp only [normalize, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ hc]

theorem normalize_of_sum_eq_one {v : X → ℝ} (h : ∑ x, v x = 1) : normalize v = v := by
  funext x; simp [normalize, h]

/-- Normalizing twice: `normalize (normalize v · ℓ) = normalize (v · ℓ)`. -/
theorem normalize_normalize_mul {v ℓ : X → ℝ} (hv : ∑ y, v y ≠ 0) :
    normalize (fun x => normalize v x * ℓ x) = normalize (fun x => v x * ℓ x) := by
  have : (fun x => normalize v x * ℓ x) = fun x => (∑ y, v y)⁻¹ * (v x * ℓ x) := by
    funext x; simp only [normalize]; ring
  rw [this, normalize_smul (inv_ne_zero hv)]

/-- Cross-ratio criterion (⇐). -/
theorem normalize_eq_of_cross {v v' : X → ℝ} (hv : 0 < ∑ y, v y) (hv' : 0 < ∑ y, v' y)
    (h : ∀ x y, v x * v' y = v y * v' x) : normalize v = normalize v' := by
  funext x
  simp only [normalize]
  rw [div_eq_div_iff hv.ne' hv'.ne', Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by rw [h x y]; ring

/-- Cross-ratio criterion (⇒). -/
theorem cross_of_normalize_eq {v v' : X → ℝ} (hv : 0 < ∑ y, v y) (hv' : 0 < ∑ y, v' y)
    (h : normalize v = normalize v') (x y : X) : v x * v' y = v y * v' x := by
  have hx := congrFun h x
  have hy := congrFun h y
  simp only [normalize] at hx hy
  rw [div_eq_div_iff hv.ne' hv'.ne'] at hx hy
  have hS : (∑ z, v z) ≠ 0 := hv.ne'
  have hS' : (∑ z, v' z) ≠ 0 := hv'.ne'
  apply mul_right_cancel₀ (mul_ne_zero hS hS')
  linear_combination (v' y * ∑ z, v z) * hx - (v' x * ∑ z, v z) * hy

theorem normalize_eq_iff_cross [Nonempty X] {v v' : X → ℝ} (hv : ∀ x, 0 < v x) (hv' : ∀ x, 0 < v' x) :
    normalize v = normalize v' ↔ ∀ x y, v x * v' y = v y * v' x :=
  ⟨cross_of_normalize_eq (sum_pos_of_pos hv) (sum_pos_of_pos hv'),
    normalize_eq_of_cross (sum_pos_of_pos hv) (sum_pos_of_pos hv')⟩

theorem bayes_apply (p ℓ : X → ℝ) (x : X) : bayes p ℓ x = p x * ℓ x / evid p ℓ := rfl

theorem evid_pos [Nonempty X] {p ℓ : X → ℝ} (hp : ∀ x, 0 < p x) (hℓ : ∀ x, 0 < ℓ x) : 0 < evid p ℓ :=
  sum_pos_of_pos fun x => mul_pos (hp x) (hℓ x)

theorem isDist_bayes [Nonempty X] {p ℓ : X → ℝ} (hp : ∀ x, 0 < p x) (hℓ : ∀ x, 0 < ℓ x) :
    IsDist (bayes p ℓ) :=
  isDist_normalize fun x => mul_pos (hp x) (hℓ x)

/-- A strictly positive probability vector on a space with ≥ 2 points has all entries `< 1`. -/
theorem IsDist.lt_one [Nontrivial X] {p : X → ℝ} (hp : IsDist p) (x : X) : p x < 1 := by
  classical
  obtain ⟨y, hy⟩ := exists_ne x
  have h1 := Finset.add_sum_erase Finset.univ p (Finset.mem_univ x)
  have h2 : p y ≤ ∑ z ∈ Finset.univ.erase x, p z :=
    Finset.single_le_sum (fun z _ => (hp.1 z).le) (Finset.mem_erase.2 ⟨hy, Finset.mem_univ y⟩)
  linarith [hp.1 y, hp.2]

/-- `bayes (normalize v) ℓ = bayes v ℓ`. -/
theorem bayes_normalize {v ℓ : X → ℝ} (hv : ∑ y, v y ≠ 0) : bayes (normalize v) ℓ = bayes v ℓ :=
  normalize_normalize_mul hv

/-! ## Claim 1: log-linear pooling commutes with the update -/

/-- **Heterogeneous-likelihood identity.** If member `i` updates on its own likelihood `ℓᵢ`, geometric pooling
of the posteriors equals updating the geometric pool on the pooled likelihood `∏ᵢ ℓᵢ^{wᵢ}`. Any real weights;
only positivity is used. -/
theorem geoPool_bayes_hetero [Nonempty X] (w : ι → ℝ) {P L : ι → X → ℝ} (hP : ∀ i x, 0 < P i x)
    (hL : ∀ i x, 0 < L i x) :
    geoPool w (fun i => bayes (P i) (L i)) = bayes (geoPool w P) (fun x => ∏ i, L i x ^ w i) := by
  have hc : ∀ i, 0 < evid (P i) (L i) := fun i => evid_pos (hP i) (hL i)
  have hsum : ∑ y, ∏ i, P i y ^ w i ≠ 0 :=
    (sum_pos_of_pos fun y => Finset.prod_pos fun i _ => rpow_pos_of_pos (hP i y) _).ne'
  unfold geoPool
  rw [bayes, normalize_normalize_mul hsum]
  have : (fun x => ∏ i, bayes (P i) (L i) x ^ w i) =
      fun x => (∏ i, (evid (P i) (L i) ^ w i)⁻¹) * ((∏ i, P i x ^ w i) * ∏ i, L i x ^ w i) := by
    funext x
    simp only [bayes_apply]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_rpow (mul_pos (hP i x) (hL i x)).le (hc i).le, mul_rpow (hP i x).le (hL i x).le]
    field_simp
  rw [this, normalize_smul]
  exact Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (rpow_pos_of_pos (hc i) _).ne'

/-- Common evidence, general weights: pooling the posteriors = updating the pool on `ℓ^{∑ w}`. -/
theorem geoPool_bayes_pow [Nonempty X] (w : ι → ℝ) {P : ι → X → ℝ} (hP : ∀ i x, 0 < P i x)
    {ℓ : X → ℝ} (hℓ : ∀ x, 0 < ℓ x) :
    geoPool w (fun i => bayes (P i) ℓ) = bayes (geoPool w P) (fun x => ℓ x ^ ∑ i, w i) := by
  rw [geoPool_bayes_hetero w hP (fun _ x => hℓ x)]
  congr 1
  funext x
  rw [rpow_sum_of_pos (hℓ x)]

/-- **Claim 1.** With `∑ w = 1`, geometric pooling commutes with the common update (any real weights). -/
theorem geoPool_bayes [Nonempty X] {w : ι → ℝ} (hw : ∑ i, w i = 1) {P : ι → X → ℝ}
    (hP : ∀ i x, 0 < P i x) {ℓ : X → ℝ} (hℓ : ∀ x, 0 < ℓ x) :
    geoPool w (fun i => bayes (P i) ℓ) = bayes (geoPool w P) ℓ := by
  rw [geoPool_bayes_pow w hP hℓ]
  simp [hw]

theorem geoPool_externallyBayesian [Nonempty X] {w : ι → ℝ} (hw : ∑ i, w i = 1) :
    ExternallyBayesian (X := X) (geoPool w) :=
  fun _ hP _ hℓ => geoPool_bayes hw (fun i => (hP i).1) hℓ

/-- Product identity behind every log-linear computation. -/
theorem prod_bayes_rpow (w : ι → ℝ) {a c : ι → ℝ} {b : ℝ} (ha : ∀ i, 0 < a i) (hb : 0 < b)
    (hc : ∀ i, 0 < c i) :
    ∏ i, (a i * b / c i) ^ w i = (∏ i, (c i ^ w i)⁻¹) * ((∏ i, a i ^ w i) * b ^ ∑ i, w i) := by
  rw [rpow_sum_of_pos hb, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [div_rpow (mul_pos (ha i) hb).le (hc i).le, mul_rpow (ha i).le hb.le]
  field_simp

theorem genGeoPool_eq_geoPool_mul (K : X → ℝ) (w : ι → ℝ) (P : ι → X → ℝ) :
    genGeoPool K w P = normalize (fun x => K x * ∏ i, P i x ^ w i) := rfl

/-- Generalized log-linear pools (`K > 0`, `∑ w = 1`) are externally Bayesian. -/
theorem genGeoPool_bayes [Nonempty X] {K : X → ℝ} (hK : ∀ x, 0 < K x) {w : ι → ℝ} (hw : ∑ i, w i = 1)
    {P : ι → X → ℝ} (hP : ∀ i x, 0 < P i x) {ℓ : X → ℝ} (hℓ : ∀ x, 0 < ℓ x) :
    genGeoPool K w (fun i => bayes (P i) ℓ) = bayes (genGeoPool K w P) ℓ := by
  have hc : ∀ i, 0 < evid (P i) ℓ := fun i => evid_pos (hP i) hℓ
  have hsum : ∑ y, K y * ∏ i, P i y ^ w i ≠ 0 :=
    (sum_pos_of_pos fun y => mul_pos (hK y) (Finset.prod_pos fun i _ => rpow_pos_of_pos (hP i y) _)).ne'
  unfold genGeoPool
  rw [bayes, normalize_normalize_mul hsum]
  have : (fun x => K x * ∏ i, bayes (P i) ℓ x ^ w i) =
      fun x => (∏ i, (evid (P i) ℓ ^ w i)⁻¹) * (K x * (∏ i, P i x ^ w i) * ℓ x) := by
    funext x
    simp only [bayes_apply]
    rw [prod_bayes_rpow w (fun i => hP i x) (hℓ x) hc, hw, rpow_one]
    ring
  rw [this, normalize_smul]
  exact Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (rpow_pos_of_pos (hc i) _).ne'

theorem genGeoPool_externallyBayesian [Nonempty X] {K : X → ℝ} (hK : ∀ x, 0 < K x) {w : ι → ℝ}
    (hw : ∑ i, w i = 1) : ExternallyBayesian (X := X) (genGeoPool K w) :=
  fun _ hP _ hℓ => genGeoPool_bayes hK hw (fun i => (hP i).1) hℓ

/-- **`∑ w = 1` is necessary**: on a space with ≥ 2 outcomes, geometric pooling is externally Bayesian iff
the weights sum to one. (No sign restriction on the weights; `ι` may be empty.) -/
theorem geoPool_externallyBayesian_iff [Nontrivial X] (w : ι → ℝ) :
    ExternallyBayesian (X := X) (geoPool w) ↔ ∑ i, w i = 1 := by
  classical
  refine ⟨fun h => ?_, geoPool_externallyBayesian⟩
  obtain ⟨x₀, x₁, hne⟩ := exists_pair_ne X
  set u : X → ℝ := fun _ => 1 / (Fintype.card X : ℝ)
  have hcard : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hu : IsDist u := ⟨fun _ => by positivity, by simp [u, Finset.card_univ]⟩
  set ℓ : X → ℝ := fun x => if x = x₀ then 2 else 1
  have hℓ : ∀ x, 0 < ℓ x := fun x => by simp only [ℓ]; split_ifs <;> norm_num
  have h1 := h (fun _ => u) (fun _ => hu) ℓ hℓ
  rw [geoPool_bayes_pow w (fun _ => hu.1) hℓ] at h1
  set W := ∑ i, w i
  set q := geoPool w (fun _ : ι => u)
  have hq : ∀ x, 0 < q x := normalize_pos fun x => Finset.prod_pos fun i _ => rpow_pos_of_pos (hu.1 x) _
  have hcr := cross_of_normalize_eq
    (sum_pos_of_pos fun x => mul_pos (hq x) (rpow_pos_of_pos (hℓ x) W))
    (sum_pos_of_pos fun x => mul_pos (hq x) (hℓ x)) h1 x₀ x₁
  have hx1 : ℓ x₁ = 1 := by simp [ℓ, Ne.symm hne]
  have hx0 : ℓ x₀ = 2 := by simp [ℓ]
  simp only [hx0, hx1, one_rpow, mul_one] at hcr
  have h2 : (2 : ℝ) ^ W = 2 := by
    have := mul_pos (hq x₀) (hq x₁)
    nlinarith [hcr]
  have := congrArg Real.log h2
  rw [Real.log_rpow (by norm_num)] at this
  have hl : Real.log 2 ≠ 0 := by positivity
  field_simp at this
  linarith

/-! ## Claim 2: linear pooling does not commute with the update -/

theorem evid_linPool (w : ι → ℝ) (P : ι → X → ℝ) (ℓ : X → ℝ) :
    evid (linPool w P) ℓ = ∑ i, w i * evid (P i) ℓ := by
  simp only [evid, linPool, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

theorem linPool_bayes_apply (w : ι → ℝ) (P : ι → X → ℝ) (ℓ : X → ℝ) (x : X) :
    linPool w (fun i => bayes (P i) ℓ) x = ℓ x * ∑ i, w i * P i x / evid (P i) ℓ := by
  simp only [linPool, bayes_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem bayes_linPool_apply (w : ι → ℝ) (P : ι → X → ℝ) (ℓ : X → ℝ) (x : X) :
    bayes (linPool w P) ℓ x = ℓ x * ((∑ i, w i * P i x) / ∑ i, w i * evid (P i) ℓ) := by
  rw [bayes_apply, evid_linPool]; simp only [linPool]; ring

/-- **Exact criterion for linear pooling** (any weights): linear pooling commutes with the update by `ℓ` at
profile `P` iff `∑ᵢ wᵢ Pᵢ(x)/cᵢ = (∑ᵢ wᵢ Pᵢ(x)) / ∑ᵢ wᵢ cᵢ` for every `x`, where `cᵢ = evid (P i) ℓ`. -/
theorem linPool_bayes_iff (w : ι → ℝ) (P : ι → X → ℝ) {ℓ : X → ℝ} (hℓ : ∀ x, ℓ x ≠ 0) :
    linPool w (fun i => bayes (P i) ℓ) = bayes (linPool w P) ℓ ↔
      ∀ x, ∑ i, w i * P i x / evid (P i) ℓ = (∑ i, w i * P i x) / ∑ i, w i * evid (P i) ℓ := by
  rw [funext_iff]
  refine forall_congr' fun x => ?_
  rw [linPool_bayes_apply, bayes_linPool_apply]
  exact ⟨fun h => mul_left_cancel₀ (hℓ x) h, fun h => by rw [h]⟩

/-- **When linear pooling IS consistent (1): equal evidence probabilities.** If every member with nonzero
weight assigns the same probability `c₀ ≠ 0` to the evidence, linear pooling (with `∑ w = 1`) commutes. -/
theorem linPool_bayes_of_evid_eq {w : ι → ℝ} (hw : ∑ i, w i = 1) (P : ι → X → ℝ) {ℓ : X → ℝ}
    (hℓ : ∀ x, ℓ x ≠ 0) {c₀ : ℝ} (h : ∀ i, w i ≠ 0 → evid (P i) ℓ = c₀) :
    linPool w (fun i => bayes (P i) ℓ) = bayes (linPool w P) ℓ := by
  rw [linPool_bayes_iff w P hℓ]
  intro x
  have h1 : ∀ i, w i * P i x / evid (P i) ℓ = w i * P i x / c₀ := fun i => by
    by_cases hi : w i = 0
    · simp [hi]
    · rw [h i hi]
  have h2 : ∀ i, w i * evid (P i) ℓ = w i * c₀ := fun i => by
    by_cases hi : w i = 0
    · simp [hi]
    · rw [h i hi]
  simp only [h1, h2, ← Finset.sum_mul, hw, one_mul, ← Finset.sum_div]

/-- **When linear pooling IS consistent (2): clones.** Members sharing one state. -/
theorem linPool_bayes_of_clones {w : ι → ℝ} (hw : ∑ i, w i = 1) {P : ι → X → ℝ}
    (hclone : ∀ i j, P i = P j) {ℓ : X → ℝ} (hℓ : ∀ x, ℓ x ≠ 0) :
    linPool w (fun i => bayes (P i) ℓ) = bayes (linPool w P) ℓ := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp at hw
  exact linPool_bayes_of_evid_eq hw P hℓ (c₀ := evid (P i₀) ℓ) fun i _ => by rw [hclone i i₀]

/-- One member: linear pooling is the identity and commutes. -/
theorem linPool_bayes_of_subsingleton [Subsingleton ι] {w : ι → ℝ} (hw : ∑ i, w i = 1)
    (P : ι → X → ℝ) {ℓ : X → ℝ} (hℓ : ∀ x, ℓ x ≠ 0) :
    linPool w (fun i => bayes (P i) ℓ) = bayes (linPool w P) ℓ :=
  linPool_bayes_of_clones hw (fun i j => by rw [Subsingleton.elim i j]) hℓ

/-- Algebra behind the two-type criterion. -/
theorem two_type_key {a b c₀ c₁ p q : ℝ} (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hd : a * c₀ + b * c₁ ≠ 0)
    (hab : a + b = 1) :
    a * p / c₀ + b * q / c₁ - (a * p + b * q) / (a * c₀ + b * c₁) =
      a * b * (c₁ - c₀) * (c₁ * p - c₀ * q) / (c₀ * c₁ * (a * c₀ + b * c₁)) := by
  obtain rfl : b = 1 - a := by linarith
  field_simp
  ring

/-- **Two-type criterion.** Mixing two probability vectors `U`, `V` with nonnegative weights `a + b = 1`:
the linear mixture commutes with the update by `ℓ` (pointwise identity for all `x`) iff
`a · b · (c_V − c_U) = 0`, i.e. iff one weight is zero or `U` and `V` assign the evidence the same
probability. -/
theorem two_type_iff [Nonempty X] {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) {U V : X → ℝ}
    (hU : IsDist U) (hV : IsDist V) {ℓ : X → ℝ} (hℓ : ∀ x, 0 < ℓ x) :
    (∀ x, a * U x / evid U ℓ + b * V x / evid V ℓ =
        (a * U x + b * V x) / (a * evid U ℓ + b * evid V ℓ)) ↔
      a * b * (evid V ℓ - evid U ℓ) = 0 := by
  have hcU := evid_pos hU.1 hℓ
  have hcV := evid_pos hV.1 hℓ
  have hd : 0 < a * evid U ℓ + b * evid V ℓ := by
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_pos ha' hcU, mul_nonneg hb hcV.le]
    · subst ha'; simp at hab; subst hab; simpa using hcV
  have key := fun x => two_type_key (p := U x) (q := V x) hcU.ne' hcV.ne' hd.ne' hab
  constructor
  · intro h
    by_contra hne
    have hall : ∀ x, evid V ℓ * U x - evid U ℓ * V x = 0 := fun x => by
      have := key x
      rw [h x, sub_self, eq_comm, div_eq_zero_iff] at this
      rcases this with h0 | h0
      · exact (mul_eq_zero.1 h0).resolve_left hne
      · exact absurd h0 (by positivity)
    have hs : ∑ x, (evid V ℓ * U x - evid U ℓ * V x) = 0 := Finset.sum_eq_zero fun x _ => hall x
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hU.2, hV.2] at hs
    exact hne (by rw [mul_one, mul_one] at hs; rw [show evid V ℓ - evid U ℓ = 0 by linarith, mul_zero])
  · intro h x
    have := key x
    rw [h, zero_mul, zero_div, sub_eq_zero] at this
    exact this

/-- **Two members.** With nonnegative weights `w₀ + w₁ = 1`, linear pooling commutes with the update by `ℓ`
iff `w₀ w₁ (c₁ − c₀) = 0`. -/
theorem linPool_two_bayes_iff [Nonempty X] {w : Fin 2 → ℝ} (hw0 : 0 ≤ w 0) (hw1 : 0 ≤ w 1)
    (hw : w 0 + w 1 = 1) {P : Fin 2 → X → ℝ} (hP : ∀ i, IsDist (P i)) {ℓ : X → ℝ}
    (hℓ : ∀ x, 0 < ℓ x) :
    linPool w (fun i => bayes (P i) ℓ) = bayes (linPool w P) ℓ ↔
      w 0 * w 1 * (evid (P 1) ℓ - evid (P 0) ℓ) = 0 := by
  rw [linPool_bayes_iff w P (fun x => (hℓ x).ne'), ← two_type_iff hw0 hw1 hw (hP 0) (hP 1) hℓ]
  simp only [Fin.sum_univ_two, mul_div_assoc]

/-- Splitting a weighted sum over a profile with one deviant member. -/
theorem sum_ite_weight [DecidableEq ι] {w : ι → ℝ} (hw : ∑ i, w i = 1) (k : ι) (A B : ℝ) :
    ∑ i, w i * (if i = k then A else B) = w k * A + (1 - w k) * B := by
  have : ∀ i, w i * (if i = k then A else B) = w i * B + (if i = k then w i * (A - B) else 0) :=
    fun i => by split_ifs <;> ring
  simp only [this, Finset.sum_add_distrib, ← Finset.sum_mul, hw, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  ring

/-- **Linear pooling is externally Bayesian only for dictatorships** (nonnegative weights summing to one,
at least two outcomes). -/
theorem linPool_externallyBayesian_iff [Nontrivial X] {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw : ∑ i, w i = 1) : ExternallyBayesian (X := X) (linPool w) ↔ ∃ j, w j = 1 := by
  classical
  constructor
  · intro hEB
    by_contra hnot
    push Not at hnot
    obtain ⟨k, hk⟩ : ∃ k, 0 < w k := by
      by_contra h; push Not at h
      have : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => h i
      linarith
    have hk1 : w k ≤ 1 := by
      rw [← hw]; exact Finset.single_le_sum (fun i _ => hw0 i) (Finset.mem_univ k)
    have hk1' : w k < 1 := lt_of_le_of_ne hk1 (hnot k)
    obtain ⟨x₀⟩ : Nonempty X := inferInstance
    set n : ℝ := (Fintype.card X : ℝ)
    have hn : (1 : ℝ) < n := by simp only [n]; exact_mod_cast Fintype.one_lt_card
    set e : X → ℝ := fun x => if x = x₀ then 1 else 0
    set ℓ : X → ℝ := fun x => 1 + e x
    have hℓ : ∀ x, 0 < ℓ x := fun x => by simp only [ℓ, e]; split_ifs <;> norm_num
    have hse : ∑ x, e x = 1 := by simp [e]
    have hse2 : ∑ x, e x * e x = 1 := by simp [e]
    have hs1 : ∑ x : X, (1 : ℝ) = n := by simp [n]
    set U : X → ℝ := fun _ => 1 / n
    set V : X → ℝ := fun x => ℓ x / (n + 1)
    have hU : IsDist U := ⟨fun _ => by positivity, by simp [U, Finset.card_univ, n]⟩
    have hV : IsDist V := by
      refine ⟨fun x => div_pos (hℓ x) (by positivity), ?_⟩
      simp only [V, ℓ, ← Finset.sum_div, Finset.sum_add_distrib, hs1, hse]
      field_simp
    have hcU : evid U ℓ = (n + 1) / n := by
      simp only [evid, U, ℓ, ← Finset.mul_sum, Finset.sum_add_distrib, hs1, hse]
      field_simp
    have hcV : evid V ℓ = (n + 3) / (n + 1) := by
      simp only [evid, V, ℓ]
      have : ∀ x, (1 + e x) / (n + 1) * (1 + e x) = (1 + 2 * e x + e x * e x) / (n + 1) :=
        fun x => by ring
      simp only [this, ← Finset.sum_div, Finset.sum_add_distrib, hs1, ← Finset.mul_sum, hse, hse2]
      ring
    set P : ι → X → ℝ := fun i => if i = k then V else U
    have hP : ∀ i, IsDist (P i) := fun i => by simp only [P]; split_ifs; exacts [hV, hU]
    have h1 := hEB P hP ℓ hℓ
    rw [linPool_bayes_iff w P (fun x => (hℓ x).ne')] at h1
    have h2 : ∀ x, w k * V x / evid V ℓ + (1 - w k) * U x / evid U ℓ =
        (w k * V x + (1 - w k) * U x) / (w k * evid V ℓ + (1 - w k) * evid U ℓ) := by
      intro x
      have := h1 x
      have e1 : ∑ i, w i * P i x / evid (P i) ℓ = ∑ i, w i * (if i = k then V x / evid V ℓ
          else U x / evid U ℓ) := Finset.sum_congr rfl fun i _ => by
        simp only [P]; split_ifs <;> ring
      have e2 : ∑ i, w i * P i x = ∑ i, w i * (if i = k then V x else U x) :=
        Finset.sum_congr rfl fun i _ => by simp only [P]; split_ifs <;> rfl
      have e3 : ∑ i, w i * evid (P i) ℓ = ∑ i, w i * (if i = k then evid V ℓ else evid U ℓ) :=
        Finset.sum_congr rfl fun i _ => by simp only [P]; split_ifs <;> rfl
      rw [e1, e2, e3, sum_ite_weight hw, sum_ite_weight hw, sum_ite_weight hw] at this
      rw [mul_div_assoc, mul_div_assoc, this]
    have h3 := (two_type_iff hk.le (by linarith) (by ring) hV hU hℓ).1 h2
    rw [hcU, hcV] at h3
    have hk0 : w k ≠ 0 := hk.ne'
    have hk2 : 1 - w k ≠ 0 := by linarith
    have : (n + 1) / n - (n + 3) / (n + 1) = 0 := by
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h (mul_ne_zero hk0 hk2)
      · exact h
    field_simp at this
    nlinarith
  · rintro ⟨j, hj⟩ P hP ℓ hℓ
    have hzero : ∀ i, i ≠ j → w i = 0 := by
      intro i hij
      have h1 := Finset.add_sum_erase Finset.univ w (Finset.mem_univ j)
      have h2 : w i ≤ ∑ z ∈ Finset.univ.erase j, w z :=
        Finset.single_le_sum (fun z _ => hw0 z) (Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩)
      linarith [hw0 i]
    exact linPool_bayes_of_evid_eq hw P (fun x => (hℓ x).ne') (c₀ := evid (P j) ℓ)
      fun i hi => by
        by_cases hij : i = j
        · rw [hij]
        · exact absurd (hzero i hij) hi

/-- **Minimal counterexample (2 members, 2 outcomes).** Weights `(1/2, 1/2)`, members `(1/2, 1/2)` and
`(1/4, 3/4)`, likelihood `(3, 1)`: pooling the posteriors gives `5/8` on outcome 0, updating the pool gives
`9/14`. Fewer members (one) or fewer outcomes (one) cannot give a counterexample
(`linPool_bayes_of_subsingleton`; on one outcome every probability vector is `1`). -/
theorem linPool_counterexample :
    linPool (X := Fin 2) ![1/2, 1/2] (fun i => bayes (![![1/2, 1/2], ![1/4, 3/4]] i) ![3, 1]) 0 = 5/8 ∧
    bayes (linPool ![1/2, 1/2] ![![1/2, 1/2], ![1/4, 3/4]]) ![3, 1] 0 = 9/14 := by
  constructor <;>
  simp [linPool, bayes_apply, evid, Fin.sum_univ_two] <;> norm_num

theorem linPool_not_externallyBayesian_two :
    ¬ ExternallyBayesian (X := Fin 2) (linPool (ι := Fin 2) ![1/2, 1/2]) := by
  intro h
  have hP : ∀ i, IsDist (![![1/2, 1/2], ![1/4, 3/4]] i : Fin 2 → ℝ) := by
    intro i; fin_cases i <;> refine ⟨fun x => by fin_cases x <;> norm_num, ?_⟩ <;>
      simp [Fin.sum_univ_two] <;> norm_num
  have := congrFun (h _ hP ![3, 1] (fun x => by fin_cases x <;> norm_num)) 0
  rw [linPool_counterexample.1, linPool_counterexample.2] at this
  norm_num at this

/-! ## Claim 3: uniqueness for pointwise pooling operators -/

/-- The open unit box `(0,1)^ι`. When `|X| ≥ 2`, it is exactly the set of values `(P₁(x),…,Pₙ(x))` a profile
of strictly positive probability vectors can take at one outcome, so a pointwise pool only ever reads its
kernel on this box. -/
def InBox (u : ι → ℝ) : Prop := ∀ i, 0 < u i ∧ u i < 1

/-- Positivity of the pooling kernel on the box. -/
def KernelPos (g : X → (ι → ℝ) → ℝ) : Prop := ∀ x u, InBox u → 0 < g x u

/-- Coordinatewise log. -/
noncomputable def logv (u : ι → ℝ) : ι → ℝ := fun i => Real.log (u i)

/-- The member normalizers in the three-outcome construction. -/
def evid3 (a b : ι → ℝ) (α β γ : ℝ) : ι → ℝ := fun i => a i * α + b i * β + (1 - a i - b i) * γ

theorem profile_inBox [Nontrivial X] {P : ι → X → ℝ} (hP : ∀ i, IsDist (P i)) (x : X) :
    InBox (fun i => P i x) := fun i => ⟨(hP i).1 x, (hP i).lt_one x⟩

theorem nontrivial_of_three (hX : 3 ≤ Fintype.card X) : Nontrivial X :=
  Fintype.one_lt_card_iff_nontrivial.1 (by omega)

/-- External Bayesianity of a pointwise pool, as a cross-ratio identity between two outcomes. -/
theorem eb_cross [Nontrivial X] {g : X → (ι → ℝ) → ℝ} (hg : KernelPos g)
    (hEB : ExternallyBayesian (pool g)) {P : ι → X → ℝ} (hP : ∀ i, IsDist (P i)) {ℓ : X → ℝ}
    (hℓ : ∀ x, 0 < ℓ x) (x y : X) :
    g x (fun i => bayes (P i) ℓ x) * (g y (fun i => P i y) * ℓ y) =
      g y (fun i => bayes (P i) ℓ y) * (g x (fun i => P i x) * ℓ x) := by
  have hQ : ∀ i, IsDist (bayes (P i) ℓ) := fun i => isDist_bayes (hP i).1 hℓ
  have hpos : ∀ z, 0 < g z (fun i => P i z) := fun z => hg z _ (profile_inBox hP z)
  have hposQ : ∀ z, 0 < g z (fun i => bayes (P i) ℓ z) := fun z => hg z _ (profile_inBox hQ z)
  have h := hEB P hP ℓ hℓ
  unfold pool at h
  rw [bayes, normalize_normalize_mul (sum_pos_of_pos hpos).ne'] at h
  exact cross_of_normalize_eq (sum_pos_of_pos hposQ)
    (sum_pos_of_pos fun z => mul_pos (hpos z) (hℓ z)) h x y

/-- **Three-outcome core.** With `|X| ≥ 3`, external Bayesianity of a pointwise pool implies: for distinct
outcomes `x ≠ y`, all `a, b ∈ (0,1)^ι` with `a + b < 1` and all `α, β, γ > 0`,
`g x (a α / N) · g y b · β = g y (b β / N) · g x a · α`, `N = a α + b β + (1 − a − b) γ`.
(Profile: members put `a`, `b` on `x`, `y` and spread the rest evenly; likelihood `α`, `β`, `γ`.) -/
theorem eb_three (hX : 3 ≤ Fintype.card X) {g : X → (ι → ℝ) → ℝ} (hg : KernelPos g)
    (hEB : ExternallyBayesian (pool g)) {x y : X} (hxy : x ≠ y) {a b : ι → ℝ} (ha : InBox a)
    (hb : InBox b) (hab : ∀ i, a i + b i < 1) {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) :
    g x (fun i => a i * α / evid3 a b α β γ i) * (g y b * β) =
      g y (fun i => b i * β / evid3 a b α β γ i) * (g x a * α) := by
  classical
  have := nontrivial_of_three hX
  set R := (Finset.univ.erase x).erase y with hR
  have hyR : y ∈ Finset.univ.erase x := Finset.mem_erase.2 ⟨hxy.symm, Finset.mem_univ y⟩
  have hRcard : 1 ≤ R.card := by
    rw [hR, Finset.card_erase_of_mem hyR, Finset.card_erase_of_mem (Finset.mem_univ x),
      Finset.card_univ]
    omega
  set m : ℝ := (R.card : ℝ)
  have hm : 0 < m := by simp only [m]; exact_mod_cast hRcard
  have hsplit : ∀ f : X → ℝ, ∑ z, f z = f x + f y + ∑ z ∈ R, f z := fun f => by
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ x), ← Finset.add_sum_erase _ f hyR]
    ring
  have hmemR : ∀ z ∈ R, z ≠ x ∧ z ≠ y := fun z hz => by
    rw [hR, Finset.mem_erase, Finset.mem_erase] at hz
    exact ⟨hz.2.1, hz.1⟩
  set P : ι → X → ℝ := fun i z => if z = x then a i else if z = y then b i else (1 - a i - b i) / m
  set ℓ : X → ℝ := fun z => if z = x then α else if z = y then β else γ
  have hPx : ∀ i, P i x = a i := fun i => by simp [P]
  have hPy : ∀ i, P i y = b i := fun i => by simp [P, hxy.symm]
  have hPR : ∀ i, ∀ z ∈ R, P i z = (1 - a i - b i) / m := fun i z hz => by
    simp [P, (hmemR z hz).1, (hmemR z hz).2]
  have hℓx : ℓ x = α := by simp [ℓ]
  have hℓy : ℓ y = β := by simp [ℓ, hxy.symm]
  have hℓR : ∀ z ∈ R, ℓ z = γ := fun z hz => by simp [ℓ, (hmemR z hz).1, (hmemR z hz).2]
  have hrest : ∀ i, 0 < 1 - a i - b i := fun i => by linarith [hab i]
  have hP : ∀ i, IsDist (P i) := by
    intro i
    refine ⟨fun z => ?_, ?_⟩
    · simp only [P]
      split_ifs
      exacts [(ha i).1, (hb i).1, div_pos (hrest i) hm]
    · rw [hsplit, hPx, hPy, Finset.sum_congr rfl (hPR i), Finset.sum_const, nsmul_eq_mul]
      field_simp
      ring
  have hℓ : ∀ z, 0 < ℓ z := fun z => by simp only [ℓ]; split_ifs <;> assumption
  have hev : ∀ i, evid (P i) ℓ = evid3 a b α β γ i := fun i => by
    rw [evid, hsplit, hPx, hPy, hℓx, hℓy,
      Finset.sum_congr rfl (fun z hz => by rw [hPR i z hz, hℓR z hz]), Finset.sum_const,
      nsmul_eq_mul]
    simp only [evid3]
    rw [show ((R.card : ℕ) : ℝ) = m from rfl]
    field_simp
  have h := eb_cross hg hEB hP hℓ x y
  simp only [bayes_apply, hPx, hPy, hℓx, hℓy, hev] at h
  exact h

/-- **Scaling step.** For `m, a, a' ∈ (0,1)^ι`: `g x (m a) · g x a' = g x (m a') · g x a`, i.e. the ratio
`g x (m ⊙ a) / g x a` does not depend on `a`. -/
theorem eb_scale (hX : 3 ≤ Fintype.card X) {g : X → (ι → ℝ) → ℝ} (hg : KernelPos g)
    (hEB : ExternallyBayesian (pool g)) (x : X) {m a a' : ι → ℝ} (hm : InBox m) (ha : InBox a)
    (ha' : InBox a') :
    g x (fun i => m i * a i) * g x a' = g x (fun i => m i * a' i) * g x a := by
  have := nontrivial_of_three hX
  obtain ⟨y, hy⟩ := exists_ne x
  set δ : ι → ℝ := fun i => 1 - max (a i) (a' i)
  have hδ : ∀ i, 0 < δ i := fun i => by
    simp only [δ]; have := (ha i).2; have := (ha' i).2; rw [sub_pos, max_lt_iff]; exact ⟨by linarith, by linarith⟩
  set t : ι → ℝ := fun i => 1 / m i - 1
  have ht : ∀ i, 0 < t i := fun i => by
    simp only [t]; rw [sub_pos, lt_div_iff₀ (hm i).1]; linarith [(hm i).2]
  set β : ℝ := 2 + ∑ i, t i / δ i
  have hsum_nn : 0 ≤ ∑ i, t i / δ i := Finset.sum_nonneg fun i _ => (div_pos (ht i) (hδ i)).le
  have hβ1 : 0 < β - 1 := by simp only [β]; linarith
  have hβ : 0 < β := by linarith
  set b : ι → ℝ := fun i => t i / (β - 1)
  have hbδ : ∀ i, b i < δ i := fun i => by
    have h1 : t i / δ i ≤ ∑ j, t j / δ j :=
      Finset.single_le_sum (fun j _ => (div_pos (ht j) (hδ j)).le) (Finset.mem_univ i)
    have h2 : t i / δ i < β - 1 := by simp only [β]; linarith
    simp only [b]
    rw [div_lt_iff₀ hβ1]
    rw [div_lt_iff₀ (hδ i)] at h2
    linarith
  have hδ1 : ∀ i, δ i ≤ 1 := fun i => by
    simp only [δ]; have := (ha i).1; have := le_max_left (a i) (a' i); linarith
  have hb : InBox b := fun i => ⟨div_pos (ht i) hβ1, lt_of_lt_of_le (hbδ i) (hδ1 i)⟩
  have hab : ∀ i, a i + b i < 1 := fun i => by
    have := hbδ i; have := le_max_left (a i) (a' i); simp only [δ] at *; linarith
  have hab' : ∀ i, a' i + b i < 1 := fun i => by
    have := hbδ i; have := le_max_right (a i) (a' i); simp only [δ] at *; linarith
  have hN : ∀ c : ι → ℝ, ∀ i, evid3 c b 1 β 1 i = 1 / m i := fun c i => by
    simp only [evid3, b, t]
    field_simp
    ring
  have h1 := eb_three hX hg hEB hy.symm ha hb hab one_pos hβ one_pos
  have h2 := eb_three hX hg hEB hy.symm ha' hb hab' one_pos hβ one_pos
  have e1 : ∀ c : ι → ℝ, (fun i => c i * 1 / evid3 c b 1 β 1 i) = fun i => m i * c i := fun c => by
    funext i; rw [hN]; have := (hm i).1; field_simp
  have e2 : ∀ c : ι → ℝ, (fun i => b i * β / evid3 c b 1 β 1 i) = fun i => b i * β * m i := fun c => by
    funext i; rw [hN]; have := (hm i).1; field_simp
  rw [e1, e2] at h1 h2
  apply mul_right_cancel₀ (mul_pos (hg y b hb) hβ).ne'
  linear_combination (g x a') * h1 - (g x a) * h2

/-- **Multiplicative representation at one outcome.** `g x u = K · φ(u)` on the box, with `φ` positive and
multiplicative on the box. -/
theorem eb_mult_rep (hX : 3 ≤ Fintype.card X) {g : X → (ι → ℝ) → ℝ} (hg : KernelPos g)
    (hEB : ExternallyBayesian (pool g)) (x : X) :
    ∃ K : ℝ, 0 < K ∧ ∃ φ : (ι → ℝ) → ℝ, (∀ m, InBox m → 0 < φ m) ∧
      (∀ m m', InBox m → InBox m' → φ (fun i => m i * m' i) = φ m * φ m') ∧
      ∀ u, InBox u → g x u = K * φ u := by
  set h : ι → ℝ := fun _ => 1 / 2
  have hh : InBox h := fun _ => ⟨by norm_num, by norm_num⟩
  have hmul : ∀ m m' : ι → ℝ, InBox m → InBox m' → InBox (fun i => m i * m' i) := by
    intro m m' hm hm' i
    have := (hm i).1; have := (hm i).2; have := (hm' i).1; have := (hm' i).2
    exact ⟨mul_pos (hm i).1 (hm' i).1, by nlinarith⟩
  have hgh := hg x h hh
  have hghh := hg x _ (hmul _ _ hh hh)
  refine ⟨g x h * g x h / g x (fun i => h i * h i), by positivity,
    fun m => g x (fun i => m i * h i) / g x h, fun m hm => div_pos (hg x _ (hmul _ _ hm hh)) hgh,
    fun m m' hm hm' => ?_, fun u hu => ?_⟩
  · have := eb_scale hX hg hEB x hm (hmul _ _ hm' hh) hh
    have e : (fun i => m i * m' i * h i) = fun i => m i * (m' i * h i) :=
      funext fun i => mul_assoc _ _ _
    show g x (fun i => m i * m' i * h i) / g x h =
      g x (fun i => m i * h i) / g x h * (g x (fun i => m' i * h i) / g x h)
    rw [e, div_mul_div_comm, div_eq_div_iff hgh.ne' (mul_pos hgh hgh).ne']
    linear_combination (g x h) * this
  · have := eb_scale hX hg hEB x hh hu hh
    have hc : (fun i => u i * h i) = fun i => h i * u i := funext fun i => mul_comm _ _
    show g x u = g x h * g x h / g x (fun i => h i * h i) * (g x (fun i => u i * h i) / g x h)
    rw [hc, div_mul_div_comm, eq_div_iff (mul_pos hghh hgh).ne']
    linear_combination (-(g x h)) * this

/-- A function additive on the open negative orthant extends to an additive map on all of `ι → ℝ`. -/
theorem extend_additive (f : (ι → ℝ) → ℝ)
    (hadd : ∀ s t : ι → ℝ, (∀ i, s i < 0) → (∀ i, t i < 0) → f (s + t) = f s + f t) :
    ∃ H : (ι → ℝ) →+ ℝ, ∀ t : ι → ℝ, (∀ i, t i < 0) → H t = f t := by
  let M : (ι → ℝ) → ℝ := fun t => ∑ i, |t i| + 1
  let sh : (ι → ℝ) → (ι → ℝ) := fun t _ => -M t
  have hle : ∀ t : ι → ℝ, ∀ i, t i < M t := fun t i => by
    have := Finset.single_le_sum (f := fun j => |t j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have := le_abs_self (t i)
    simp only [M]; linarith
  have hMpos : ∀ t, 0 < M t := fun t => by
    simp only [M]; linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => abs_nonneg (t j))]
  let F : (ι → ℝ) → ℝ := fun t => f (t + sh t) - f (sh t)
  have key : ∀ t s : ι → ℝ, (∀ i, s i < 0) → (∀ i, t i + s i < 0) → F t = f (t + s) - f s := by
    intro t s hs hts
    have hsh : ∀ i, sh t i < 0 := fun i => by simp only [sh]; linarith [hMpos t]
    have htsh : ∀ i, t i + sh t i < 0 := fun i => by simp only [sh]; linarith [hle t i]
    have e1 := hadd (t + sh t) s htsh hs
    have e2 := hadd (t + s) (sh t) hts hsh
    have : t + sh t + s = t + s + sh t := by abel
    simp only [F]
    rw [this] at e1
    linarith
  refine ⟨{ toFun := F, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · simp [F]
  · intro t t'
    set s := sh t + sh t'
    have hs : ∀ i, s i < 0 := fun i => by simp only [s, sh, Pi.add_apply]; linarith [hMpos t, hMpos t']
    have h1 : ∀ i, t' i + s i < 0 := fun i => by
      simp only [s, sh, Pi.add_apply]; linarith [hle t' i, hMpos t]
    have h2 : ∀ i, (t + t') i + s i < 0 := fun i => by
      simp only [s, sh, Pi.add_apply]; linarith [hle t i, hle t' i]
    have h3 : ∀ i, t i + (t' + s) i < 0 := fun i => by
      simp only [s, sh, Pi.add_apply]; linarith [hle t i, hle t' i]
    show F (t + t') = F t + F t'
    rw [key (t + t') s hs h2, key t (t' + s) h1 h3, key t' s hs h1]
    have : t + t' + s = t + (t' + s) := by abel
    rw [this]; ring
  · intro t ht
    show F t = f t
    rw [key t t ht (fun i => by linarith [ht i]), hadd t t ht ht]
    ring

/-- An additive map vanishing on a small open box `(0, ε)^ι` vanishes identically. -/
theorem addHom_eq_zero_of_box (D : (ι → ℝ) →+ ℝ) {ε : ℝ} (hε : 0 < ε)
    (hD : ∀ t : ι → ℝ, (∀ i, 0 < t i ∧ t i < ε) → D t = 0) (t : ι → ℝ) : D t = 0 := by
  set c := ε / 2
  have hc : 0 < c := by positivity
  obtain ⟨k, hk⟩ := exists_nat_gt ((∑ i, |t i|) / c)
  have hS : 0 ≤ ∑ i, |t i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hkpos : (0 : ℝ) < k := lt_of_le_of_lt (div_nonneg hS hc.le) hk
  have hsmall : ∀ i, |t i| / k < c := fun i => by
    have h1 : |t i| ≤ ∑ j, |t j| :=
      Finset.single_le_sum (f := fun j => |t j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [div_lt_iff₀ hkpos]
    rw [div_lt_iff₀ hc] at hk
    nlinarith
  have hcc : c + c = ε := by simp only [c]; ring
  set u : ι → ℝ := fun i => c + t i / k
  set v : ι → ℝ := fun _ => c
  have hu : D u = 0 := hD u fun i => by
    have := hsmall i
    have h1 := neg_abs_le (t i / k)
    have h2 := le_abs_self (t i / k)
    rw [abs_div, abs_of_pos hkpos] at h1 h2
    simp only [u]; constructor <;> linarith
  have hv : D v = 0 := hD v fun i => ⟨hc, by linarith⟩
  have htk : t = k • (u - v) := by
    funext i; simp only [u, v, Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul]; field_simp; ring
  rw [htk, map_nsmul, map_sub, hu, hv, sub_zero, smul_zero]

/-- The key identity `(★)` obtained by inserting the representations `g z u = K_z exp(H_z(log u))` into the
three-outcome core. -/
theorem star_identity {Kx Ky : ℝ} (hKx : 0 < Kx) (hKy : 0 < Ky) {Hx Hy : (ι → ℝ) →+ ℝ}
    {gx gy : (ι → ℝ) → ℝ} (hrx : ∀ u, InBox u → gx u = Kx * exp (Hx (logv u)))
    (hry : ∀ u, InBox u → gy u = Ky * exp (Hy (logv u))) {a b : ι → ℝ} (ha : InBox a) (hb : InBox b)
    (hab : ∀ i, a i + b i < 1) {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (heq : gx (fun i => a i * α / evid3 a b α β γ i) * (gy b * β) =
      gy (fun i => b i * β / evid3 a b α β γ i) * (gx a * α)) :
    Hx (fun _ => Real.log α) - Hx (logv (evid3 a b α β γ)) + Real.log β =
      Hy (fun _ => Real.log β) - Hy (logv (evid3 a b α β γ)) + Real.log α := by
  set N := evid3 a b α β γ
  have hrest : ∀ i, 0 < 1 - a i - b i := fun i => by linarith [hab i]
  have hNa : ∀ i, a i * α < N i := fun i => by
    have := mul_pos (hb i).1 hβ; have := mul_pos (hrest i) hγ; simp only [N, evid3]; linarith
  have hNb : ∀ i, b i * β < N i := fun i => by
    have := mul_pos (ha i).1 hα; have := mul_pos (hrest i) hγ; simp only [N, evid3]; linarith
  have hNpos : ∀ i, 0 < N i := fun i => lt_trans (mul_pos (ha i).1 hα) (hNa i)
  have hpa : InBox (fun i => a i * α / N i) := fun i =>
    ⟨div_pos (mul_pos (ha i).1 hα) (hNpos i), (div_lt_one (hNpos i)).2 (hNa i)⟩
  have hpb : InBox (fun i => b i * β / N i) := fun i =>
    ⟨div_pos (mul_pos (hb i).1 hβ) (hNpos i), (div_lt_one (hNpos i)).2 (hNb i)⟩
  have hlog : ∀ (c : ι → ℝ) (κ : ℝ), InBox c → 0 < κ →
      logv (fun i => c i * κ / N i) = logv c + (fun _ => Real.log κ) - logv N := by
    intro c κ hc hκ
    funext i
    simp only [logv, Pi.add_apply, Pi.sub_apply]
    rw [Real.log_div (mul_pos (hc i).1 hκ).ne' (hNpos i).ne', Real.log_mul (hc i).1.ne' hκ.ne']
  rw [hrx _ hpa, hry _ hpb, hrx _ ha, hry _ hb, hlog a α ha hα, hlog b β hb hβ, map_sub, map_add,
    map_sub, map_add] at heq
  apply Real.exp_injective
  rw [exp_add, exp_add, exp_log hα, exp_log hβ]
  have hC : 0 < Kx * Ky * exp (Hx (logv a)) * exp (Hy (logv b)) := by positivity
  apply mul_left_cancel₀ hC.ne'
  have e1 : exp (Hx (logv a) + Hx (fun _ => Real.log α) - Hx (logv N)) =
      exp (Hx (logv a)) * exp (Hx (fun _ => Real.log α) - Hx (logv N)) := by
    rw [← exp_add]; ring_nf
  have e2 : exp (Hy (logv b) + Hy (fun _ => Real.log β) - Hy (logv N)) =
      exp (Hy (logv b)) * exp (Hy (fun _ => Real.log β) - Hy (logv N)) := by
    rw [← exp_add]; ring_nf
  rw [e1, e2] at heq
  linear_combination heq

/-- **Uniqueness without regularity.** `|X| ≥ 3`, a pointwise pool with positive kernel that is externally
Bayesian. Then there are constants `K x > 0` and a single additive map `H : (ι → ℝ) →+ ℝ` with `H(σ𝟙) = σ`
such that `g x u = K x · exp(H(log u))` on the whole box, for every outcome `x`. -/
theorem eb_additive_form (hX : 3 ≤ Fintype.card X) {g : X → (ι → ℝ) → ℝ} (hg : KernelPos g)
    (hEB : ExternallyBayesian (pool g)) :
    ∃ K : X → ℝ, (∀ x, 0 < K x) ∧ ∃ H : (ι → ℝ) →+ ℝ, (∀ σ : ℝ, H (fun _ => σ) = σ) ∧
      ∀ x u, InBox u → g x u = K x * exp (H (logv u)) := by
  have := nontrivial_of_three hX
  -- Step 1: per-outcome additive representation.
  have hrep : ∀ x, ∃ K : ℝ, 0 < K ∧ ∃ H : (ι → ℝ) →+ ℝ,
      ∀ u, InBox u → g x u = K * exp (H (logv u)) := by
    intro x
    obtain ⟨K, hK, φ, hφpos, hφmul, hgφ⟩ := eb_mult_rep hX hg hEB x
    have hexp : ∀ t : ι → ℝ, (∀ i, t i < 0) → InBox (fun i => exp (t i)) := fun t ht i =>
      ⟨exp_pos _, exp_lt_one_iff.2 (ht i)⟩
    obtain ⟨H, hH⟩ := extend_additive (fun t => Real.log (φ (fun i => exp (t i)))) (by
      intro s t hs ht
      have : (fun i => exp ((s + t) i)) = fun i => exp (s i) * exp (t i) :=
        funext fun i => by simp [exp_add]
      rw [this, hφmul _ _ (hexp s hs) (hexp t ht),
        Real.log_mul (hφpos _ (hexp s hs)).ne' (hφpos _ (hexp t ht)).ne'])
    refine ⟨K, hK, H, fun u hu => ?_⟩
    have hneg : ∀ i, logv u i < 0 := fun i => Real.log_neg (hu i).1 (hu i).2
    rw [hH _ hneg, hgφ u hu]
    have : (fun i => exp (logv u i)) = u := funext fun i => exp_log (hu i).1
    simp only [this, exp_log (hφpos u hu)]
  choose K hK Hf hHf using hrep
  -- Step 2: the additive parts agree across outcomes.
  have hsame : ∀ x y, Hf x = Hf y := by
    intro x y
    by_cases hxy : x = y
    · rw [hxy]
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hzero := addHom_eq_zero_of_box (Hf x - Hf y) hl2 (fun t ht => by
      set s : ι → ℝ := fun i => 2 - exp (t i)
      have hs : ∀ i, 0 < s i ∧ s i < 1 := fun i => by
        have h1 := (ht i).1; have h2 := (ht i).2
        have e1 : 1 < exp (t i) := one_lt_exp_iff.2 h1
        have e2 : exp (t i) < 2 := by
          calc exp (t i) < exp (Real.log 2) := exp_lt_exp.2 h2
            _ = 2 := exp_log (by norm_num)
        simp only [s]; constructor <;> linarith
      set a : ι → ℝ := fun i => s i / 2
      have ha : InBox a := fun i => ⟨by simp only [a]; linarith [(hs i).1], by
        simp only [a]; linarith [(hs i).2]⟩
      have hab : ∀ i, a i + a i < 1 := fun i => by simp only [a]; linarith [(hs i).2]
      have hN : logv (evid3 a a 1 1 2) = t := by
        funext i; simp only [logv, evid3, a, s]; ring_nf; exact Real.log_exp _
      have := star_identity (hK x) (hK y) (hHf x) (hHf y) ha ha hab one_pos one_pos two_pos
        (eb_three hX hg hEB hxy ha ha hab one_pos one_pos two_pos)
      simp only [Real.log_one, hN] at this
      have h0 : (fun _ : ι => (0 : ℝ)) = 0 := rfl
      rw [h0, map_zero, map_zero] at this
      simp only [AddMonoidHom.sub_apply]
      linarith)
    ext t
    have := hzero t
    simp only [AddMonoidHom.sub_apply, sub_eq_zero] at this
    exact this
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  refine ⟨K, hK, Hf x₀, ?_, fun x u hu => by rw [hHf x u hu, hsame x x₀]⟩
  -- Step 3: normalization `H(σ𝟙) = σ`.
  intro σ
  obtain ⟨y, hy⟩ := exists_ne x₀
  set a : ι → ℝ := fun _ => 1 / 4
  have ha : InBox a := fun _ => ⟨by norm_num, by norm_num⟩
  have hab : ∀ i, a i + a i < 1 := fun _ => by norm_num [a]
  have := star_identity (hK x₀) (hK y) (hHf x₀) (hHf y) ha ha hab (exp_pos σ) one_pos one_pos
    (eb_three hX hg hEB (Ne.symm hy) ha ha hab (exp_pos σ) one_pos one_pos)
  rw [hsame y x₀, Real.log_exp, Real.log_one] at this
  have h0 : (fun _ : ι => (0 : ℝ)) = 0 := rfl
  rw [h0, map_zero] at this
  linarith

/-- **Converse (no regularity).** Every kernel of the form `K x · exp(H(log u))` with `H` additive and
`H(σ𝟙) = σ` gives an externally Bayesian pool. Together with `eb_additive_form` this is an exact
characterization for `|X| ≥ 3`. -/
theorem pool_eb_of_additive_form [Nontrivial X] {g : X → (ι → ℝ) → ℝ} {K : X → ℝ} (hK : ∀ x, 0 < K x)
    {H : (ι → ℝ) →+ ℝ} (hH : ∀ σ : ℝ, H (fun _ => σ) = σ)
    (hrep : ∀ x u, InBox u → g x u = K x * exp (H (logv u))) :
    ExternallyBayesian (pool g) := by
  intro P hP ℓ hℓ
  have hQ : ∀ i, IsDist (bayes (P i) ℓ) := fun i => isDist_bayes (hP i).1 hℓ
  have hpos : ∀ z, 0 < g z (fun i => P i z) := fun z => by
    rw [hrep z _ (profile_inBox hP z)]; exact mul_pos (hK z) (exp_pos _)
  unfold pool
  rw [bayes, normalize_normalize_mul (sum_pos_of_pos hpos).ne']
  set c : ι → ℝ := fun i => evid (P i) ℓ
  have hc : ∀ i, 0 < c i := fun i => evid_pos (hP i).1 hℓ
  have : (fun x => g x (fun i => bayes (P i) ℓ x)) =
      fun x => exp (-H (logv c)) * (g x (fun i => P i x) * ℓ x) := by
    funext x
    rw [hrep x _ (profile_inBox hQ x), hrep x _ (profile_inBox hP x)]
    have hl : logv (fun i => bayes (P i) ℓ x) = logv (fun i => P i x) + (fun _ => Real.log (ℓ x)) -
        logv c := by
      funext i
      simp only [logv, bayes_apply, Pi.add_apply, Pi.sub_apply, c]
      rw [Real.log_div (mul_pos ((hP i).1 x) (hℓ x)).ne' (hc i).ne',
        Real.log_mul ((hP i).1 x).ne' (hℓ x).ne']
    rw [hl, map_sub, map_add, hH, exp_sub, exp_add, exp_log (hℓ x), exp_neg]
    field_simp
  rw [this, normalize_smul (exp_pos _).ne']

/-- **Main uniqueness theorem.** `|X| ≥ 3`, pointwise pool with positive kernel, externally Bayesian, and the
kernel at *one* outcome `x₀` continuous on the box. Then there are weights `w` with `∑ w = 1` and constants
`K x > 0` such that `g x u = K x · ∏ᵢ uᵢ^{wᵢ}` on the box for every `x`. (Weights may be negative.) -/
theorem eb_loglinear (hX : 3 ≤ Fintype.card X) {g : X → (ι → ℝ) → ℝ} (hg : KernelPos g)
    (hEB : ExternallyBayesian (pool g)) {x₀ : X} (hcont : ContinuousOn (g x₀) {u | InBox u}) :
    ∃ K : X → ℝ, (∀ x, 0 < K x) ∧ ∃ w : ι → ℝ, ∑ i, w i = 1 ∧
      ∀ x u, InBox u → g x u = K x * ∏ i, u i ^ w i := by
  classical
  obtain ⟨K, hK, H, hH, hrep⟩ := eb_additive_form hX hg hEB
  -- H is continuous.
  have hHneg : ∀ s : ι → ℝ, (∀ i, s i < 0) →
      H s = Real.log (g x₀ (fun i => exp (s i))) - Real.log (K x₀) := by
    intro s hs
    have hb : InBox (fun i => exp (s i)) := fun i => ⟨exp_pos _, exp_lt_one_iff.2 (hs i)⟩
    rw [hrep x₀ _ hb]
    have : logv (fun i => exp (s i)) = s := funext fun i => Real.log_exp _
    rw [this, Real.log_mul (hK x₀).ne' (exp_pos _).ne', Real.log_exp]; ring
  have hHcont : Continuous H := by
    rw [continuous_iff_continuousAt]
    intro t₀
    set M : ℝ := ∑ i, |t₀ i| + 1
    set U : Set (ι → ℝ) := {t | ∀ i, t i < M}
    have hUo : IsOpen U := by
      have : U = ⋂ i, {t : ι → ℝ | t i < M} := by ext t; simp [U]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
    have ht₀ : t₀ ∈ U := fun i => by
      have := Finset.single_le_sum (f := fun j => |t₀ j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
      have := le_abs_self (t₀ i)
      simp only [M]; linarith
    set F : (ι → ℝ) → ℝ := fun t => Real.log (g x₀ (fun i => exp (t i - M))) - Real.log (K x₀) + M
    have hHF : ∀ t ∈ U, H t = F t := by
      intro t ht
      have hs : ∀ i, (t - (fun _ : ι => M)) i < 0 := fun i => by
        simp only [Pi.sub_apply]; linarith [ht i]
      have : t = (t - (fun _ : ι => M)) + (fun _ : ι => M) := by abel
      rw [this, map_add, hH, hHneg _ hs]
      simp only [F, Pi.sub_apply, sub_add_cancel]
    have hmaps : Set.MapsTo (fun t : ι → ℝ => fun i => exp (t i - M)) U {u | InBox u} :=
      fun t ht i => ⟨exp_pos _, exp_lt_one_iff.2 (by linarith [ht i])⟩
    have hcomp : ContinuousOn (fun t : ι → ℝ => g x₀ (fun i => exp (t i - M))) U :=
      hcont.comp (Continuous.continuousOn (by fun_prop)) hmaps
    have hFc : ContinuousOn F U := by
      refine ((hcomp.log fun t ht => (hg x₀ _ (hmaps ht)).ne').sub continuousOn_const).add
        continuousOn_const
    exact (hFc.continuousAt (hUo.mem_nhds ht₀)).congr
      (Filter.eventually_of_mem (hUo.mem_nhds ht₀) fun t ht => (hHF t ht).symm)
  -- H is linear.
  set w : ι → ℝ := fun i => H (fun j => if i = j then 1 else 0)
  have hlin : ∀ t, H t = ∑ i, t i * w i := by
    intro t
    conv_lhs => rw [pi_eq_sum_univ t]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_real_smul H hHcont, smul_eq_mul]
  refine ⟨K, hK, w, ?_, fun x u hu => ?_⟩
  · have := hH 1
    rw [hlin] at this
    simpa using this
  · rw [hrep x u hu, hlin, Real.exp_sum]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [rpow_def_of_pos (hu i).1]; rfl

/-- Operator form: on every profile, the pool *is* the generalized log-linear pool. -/
theorem pool_eq_genGeoPool [Nontrivial X] {g : X → (ι → ℝ) → ℝ} {K : X → ℝ} {w : ι → ℝ}
    (hrep : ∀ x u, InBox u → g x u = K x * ∏ i, u i ^ w i) {P : ι → X → ℝ}
    (hP : ∀ i, IsDist (P i)) : pool g P = genGeoPool K w P := by
  unfold pool genGeoPool
  congr 1
  funext x
  exact hrep x _ (profile_inBox hP x)

/-- **Main theorem, iff form.** For `|X| ≥ 3`, a pointwise pool with positive kernel that is continuous at one
outcome is externally Bayesian iff its kernel is generalized log-linear with weights summing to one. -/
theorem pool_eb_iff_loglinear (hX : 3 ≤ Fintype.card X) {g : X → (ι → ℝ) → ℝ} (hg : KernelPos g)
    {x₀ : X} (hcont : ContinuousOn (g x₀) {u | InBox u}) :
    ExternallyBayesian (pool g) ↔ ∃ K : X → ℝ, (∀ x, 0 < K x) ∧ ∃ w : ι → ℝ, ∑ i, w i = 1 ∧
      ∀ x u, InBox u → g x u = K x * ∏ i, u i ^ w i := by
  have := nontrivial_of_three hX
  refine ⟨fun h => eb_loglinear hX hg h hcont, ?_⟩
  rintro ⟨K, hK, w, hw, hrep⟩ P hP ℓ hℓ
  have hQ : ∀ i, IsDist (bayes (P i) ℓ) := fun i => isDist_bayes (hP i).1 hℓ
  rw [pool_eq_genGeoPool hrep hQ, pool_eq_genGeoPool hrep hP]
  exact genGeoPool_bayes hK hw (fun i => (hP i).1) hℓ

/-- **Outcome-independent kernel (the GMS "likelihood principle" form).** If the same `g` is used at every
outcome, an externally Bayesian pool with `|X| ≥ 3` and `g` continuous on the box is plain log-linear pooling
`geoPool w` with `∑ w = 1`, on every profile. -/
theorem pool_eq_geoPool (hX : 3 ≤ Fintype.card X) {g : (ι → ℝ) → ℝ}
    (hg : ∀ u, InBox u → 0 < g u) (hEB : ExternallyBayesian (X := X) (pool fun _ => g))
    (hcont : ContinuousOn g {u | InBox u}) :
    ∃ w : ι → ℝ, ∑ i, w i = 1 ∧ ∀ P : ι → X → ℝ, (∀ i, IsDist (P i)) → pool (fun _ => g) P = geoPool w P := by
  have := nontrivial_of_three hX
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨K, hK, w, hw, hrep⟩ := eb_loglinear hX (fun _ => hg) hEB (x₀ := x₀) hcont
  refine ⟨w, hw, fun P hP => ?_⟩
  set h : ι → ℝ := fun _ => 1 / 2
  have hh : InBox h := fun _ => ⟨by norm_num, by norm_num⟩
  have hprod : 0 < ∏ i, h i ^ w i := Finset.prod_pos fun i _ => rpow_pos_of_pos (by norm_num) _
  have hKc : ∀ x, K x = K x₀ := fun x => by
    have := (hrep x h hh).symm.trans (hrep x₀ h hh)
    exact mul_right_cancel₀ hprod.ne' this
  rw [pool_eq_genGeoPool hrep hP, genGeoPool]
  simp only [hKc]
  exact normalize_smul (hK x₀).ne'

/-! ### `|X| ≥ 3` is necessary: a smooth non-log-linear externally Bayesian pool on two outcomes -/

/-- `g(x₀, x₁) = x₀ · (2 + ρ)` with `ρ = x₀(1 − x₁)/((1 − x₀) x₁)` the odds ratio of member 0 to member 1. -/
noncomputable def gTwo' (x₀ x₁ : ℝ) : ℝ := x₀ * (2 + x₀ * (1 - x₁) / ((1 - x₀) * x₁))

/-- The two-member kernel (same at both outcomes). -/
noncomputable def gTwo (u : Fin 2 → ℝ) : ℝ := gTwo' (u 0) (u 1)

theorem gTwo_pos : ∀ u : Fin 2 → ℝ, InBox u → 0 < gTwo u := fun u hu => by
  have h0 := hu 0; have h1 := hu 1
  have : 0 < 1 - u 0 := by linarith [h0.2]
  have : 0 < 1 - u 1 := by linarith [h1.2]
  unfold gTwo gTwo'
  have : 0 < u 0 * (1 - u 1) / ((1 - u 0) * u 1) := div_pos (mul_pos h0.1 ‹_›) (mul_pos ‹_› h1.1)
  exact mul_pos h0.1 (by linarith)

theorem gTwo_continuousOn : ContinuousOn gTwo {u | InBox u} := by
  unfold gTwo gTwo'
  refine ContinuousOn.mul (continuous_apply 0).continuousOn (ContinuousOn.add continuousOn_const ?_)
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun u hu => ?_
  have h0 := hu.out 0; have h1 := hu.out 1
  exact mul_ne_zero (by linarith [h0.2]) h1.1.ne'

/-- The algebraic identity behind `two_point_eb`. -/
theorem gTwo'_bayes {p q a b : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) (ha : 0 < a)
    (hb : 0 < b) :
    gTwo' (p * a / (p * a + (1 - p) * b)) (q * a / (q * a + (1 - q) * b)) * (gTwo' (1 - p) (1 - q) * b) =
      gTwo' ((1 - p) * b / (p * a + (1 - p) * b)) ((1 - q) * b / (q * a + (1 - q) * b)) *
        (gTwo' p q * a) := by
  have hp' : 0 < 1 - p := by linarith
  have hq' : 0 < 1 - q := by linarith
  have hc0 : 0 < p * a + (1 - p) * b := by positivity
  have hc1 : 0 < q * a + (1 - q) * b := by positivity
  have e1 : 1 - p * a / (p * a + (1 - p) * b) = (1 - p) * b / (p * a + (1 - p) * b) := by
    field_simp; ring
  have e2 : 1 - q * a / (q * a + (1 - q) * b) = (1 - q) * b / (q * a + (1 - q) * b) := by
    field_simp; ring
  have e3 : 1 - (1 - p) * b / (p * a + (1 - p) * b) = p * a / (p * a + (1 - p) * b) := by
    field_simp; ring
  have e4 : 1 - (1 - q) * b / (q * a + (1 - q) * b) = q * a / (q * a + (1 - q) * b) := by
    field_simp; ring
  unfold gTwo'
  rw [e1, e2, e3, e4, sub_sub_cancel, sub_sub_cancel]
  field_simp

/-- **Two outcomes: a continuous, outcome-independent, externally Bayesian pool.** -/
theorem two_point_eb : ExternallyBayesian (X := Fin 2) (pool fun _ => gTwo) := by
  intro P hP ℓ hℓ
  have hQ : ∀ i, IsDist (bayes (P i) ℓ) := fun i => isDist_bayes (hP i).1 hℓ
  have hpos : ∀ z, 0 < gTwo (fun i => P i z) := fun z => gTwo_pos _ (profile_inBox hP z)
  have hposQ : ∀ z, 0 < gTwo (fun i => bayes (P i) ℓ z) := fun z => gTwo_pos _ (profile_inBox hQ z)
  unfold pool
  rw [bayes, normalize_normalize_mul (sum_pos_of_pos hpos).ne']
  apply normalize_eq_of_cross (sum_pos_of_pos hposQ) (sum_pos_of_pos fun z => mul_pos (hpos z) (hℓ z))
  have s : ∀ i, P i 1 = 1 - P i 0 := fun i => by
    have := (hP i).2; rw [Fin.sum_univ_two] at this; linarith
  have hev : ∀ i, evid (P i) ℓ = P i 0 * ℓ 0 + (1 - P i 0) * ℓ 1 := fun i => by
    rw [evid, Fin.sum_univ_two, s]
  have key : gTwo (fun i => bayes (P i) ℓ 0) * (gTwo (fun i => P i 1) * ℓ 1) =
      gTwo (fun i => bayes (P i) ℓ 1) * (gTwo (fun i => P i 0) * ℓ 0) := by
    simp only [gTwo, bayes_apply, hev, s]
    exact gTwo'_bayes ((hP 0).1 0) ((hP 0).lt_one 0) ((hP 1).1 0) ((hP 1).lt_one 0) (hℓ 0) (hℓ 1)
  intro x y
  fin_cases x <;> fin_cases y
  · ring
  · exact key
  · simp only [Fin.mk_one, Fin.zero_eta]; linarith [key]
  · ring

theorem two_point_cross {K : Fin 2 → ℝ} {w : Fin 2 → ℝ} (hK : ∀ x, 0 < K x)
    (h : ∀ P : Fin 2 → Fin 2 → ℝ, (∀ i, IsDist (P i)) → pool (fun _ => gTwo) P = genGeoPool K w P)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    gTwo' a (1/2) * (K 1 * ((1 - a) ^ w 0 * (1/2 : ℝ) ^ w 1)) =
      gTwo' (1 - a) (1/2) * (K 0 * (a ^ w 0 * (1/2 : ℝ) ^ w 1)) := by
  set P : Fin 2 → Fin 2 → ℝ := ![![a, 1 - a], ![1/2, 1/2]]
  have hP : ∀ i, IsDist (P i) := by
    intro i
    fin_cases i
    · exact ⟨fun x => by fin_cases x <;> simp [P] <;> linarith, by simp [P, Fin.sum_univ_two]⟩
    · exact ⟨fun x => by fin_cases x <;> norm_num [P], by norm_num [P, Fin.sum_univ_two]⟩
  have hpos : ∀ z, 0 < gTwo (fun i => P i z) := fun z => gTwo_pos _ (profile_inBox hP z)
  have hgpos : ∀ z, 0 < K z * ∏ i, P i z ^ w i := fun z =>
    mul_pos (hK z) (Finset.prod_pos fun i _ => rpow_pos_of_pos ((hP i).1 z) _)
  have := cross_of_normalize_eq (sum_pos_of_pos hpos) (sum_pos_of_pos hgpos) (h P hP) 0 1
  simpa [gTwo, P, Fin.prod_univ_two] using this

/-- **The two-outcome pool is not (generalized) log-linear**, for any constants and any weights (not even
weights failing `∑ w = 1`). So `|X| ≥ 3` cannot be dropped from `eb_loglinear`, even for a smooth,
outcome-independent kernel. -/
theorem two_point_not_loglinear :
    ¬ ∃ K : Fin 2 → ℝ, (∀ x, 0 < K x) ∧ ∃ w : Fin 2 → ℝ,
      ∀ P : Fin 2 → Fin 2 → ℝ, (∀ i, IsDist (P i)) → pool (fun _ => gTwo) P = genGeoPool K w P := by
  rintro ⟨K, hK, w, h⟩
  have c1 := two_point_cross hK h (a := 1/2) (by norm_num) (by norm_num)
  have c2 := two_point_cross hK h (a := 2/3) (by norm_num) (by norm_num)
  have c3 := two_point_cross hK h (a := 4/5) (by norm_num) (by norm_num)
  norm_num [gTwo'] at c1 c2 c3
  have hA : (0 : ℝ) < (1/2 : ℝ) ^ w 1 := rpow_pos_of_pos (by norm_num) _
  have hB : (0 : ℝ) < (1/2 : ℝ) ^ w 0 := rpow_pos_of_pos (by norm_num) _
  have hK01 : K 1 = K 0 := by
    rcases c1 with h | h | h
    · exact h
    · exact absurd h hB.ne'
    · exact absurd h hA.ne'
  rw [hK01] at c2 c3
  have h23 : (2/3 : ℝ) ^ w 0 = 2 ^ w 0 * (1/3 : ℝ) ^ w 0 := by
    rw [← mul_rpow (by norm_num) (by norm_num)]; norm_num
  have h45 : (4/5 : ℝ) ^ w 0 = 2 ^ w 0 * 2 ^ w 0 * (1/5 : ℝ) ^ w 0 := by
    rw [← mul_rpow (by norm_num) (by norm_num), ← mul_rpow (by norm_num) (by norm_num)]; norm_num
  rw [h23] at c2
  rw [h45] at c3
  set t := (2 : ℝ) ^ w 0
  have h3 : (0 : ℝ) < (1/3 : ℝ) ^ w 0 := rpow_pos_of_pos (by norm_num) _
  have h5 : (0 : ℝ) < (1/5 : ℝ) ^ w 0 := rpow_pos_of_pos (by norm_num) _
  have hC := mul_pos (hK 0) hA
  have ht : t = 16 / 5 := by
    have : (K 0 * (1/2 : ℝ) ^ w 1 * (1/3 : ℝ) ^ w 0) * (t * (5/6) - 8/3) = 0 := by linear_combination -c2
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 (by positivity)
    · linarith
  have : (K 0 * (1/2 : ℝ) ^ w 1 * (1/5 : ℝ) ^ w 0) * (t * t * (9/20) - 24/5) = 0 := by
    linear_combination -c3
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 (by positivity)
  · rw [ht] at h0; norm_num at h0

/-! ## Claim 4: the credit-routing reading -/

/-- **Why only log-linear pooling survives separate renormalization.** Geometric pooling is blind to
rescaling each member separately (any weights). Linear pooling is not (it fails EB). -/
theorem geoPool_smul_invariant (w : ι → ℝ) {c : ι → ℝ} (hc : ∀ i, 0 < c i) {P : ι → X → ℝ}
    (hP : ∀ i x, 0 < P i x) : geoPool w (fun i x => c i * P i x) = geoPool w P := by
  unfold geoPool
  have : (fun x => ∏ i, (c i * P i x) ^ w i) = fun x => (∏ i, c i ^ w i) * ∏ i, P i x ^ w i := by
    funext x
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => mul_rpow (hc i).le (hP i x).le
  rw [this, normalize_smul (Finset.prod_ne_zero_iff.2 fun i _ => (rpow_pos_of_pos (hc i) _).ne')]

/-- **When linear pooling IS consistent (3): one joint renormalization.** Linearly pooling unnormalized
"wealth" vectors and renormalizing once commutes with the update: members are *not* renormalized
separately. -/
theorem linPool_joint_renormalization (w : ι → ℝ) (W : ι → X → ℝ) (ℓ : X → ℝ)
    (hS : ∑ x, linPool w W x ≠ 0) :
    normalize (linPool w (fun i x => W i x * ℓ x)) = bayes (normalize (linPool w W)) ℓ := by
  rw [bayes_normalize hS, bayes]
  congr 1
  funext x
  simp only [linPool, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **When linear pooling IS consistent (4): Bayesian model averaging.** If the weights are themselves
updated by each member's evidence probability (`w ↦ bayes w c`), the linear pool of the updated members
equals the update of the linear pool. This is the Kelly-market / mixture case: credit shares are reallocated
by realized performance. -/
theorem mixture_bayes (w : ι → ℝ) (P : ι → X → ℝ) (ℓ : X → ℝ) (hc : ∀ i, evid (P i) ℓ ≠ 0)
    (hcbar : ∑ i, w i * evid (P i) ℓ ≠ 0) :
    linPool (bayes w fun i => evid (P i) ℓ) (fun i => bayes (P i) ℓ) = bayes (linPool w P) ℓ := by
  funext x
  rw [bayes_linPool_apply]
  simp only [linPool, bayes_apply]
  have he : evid w (fun i => evid (P i) ℓ) = ∑ i, w i * evid (P i) ℓ := rfl
  rw [he, mul_div_assoc', Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by have := hc i; field_simp

/-- Parimutuel market price: wealth-share–weighted average belief (a linear pool with weights `s`). -/
def price (s : ι → ℝ) (b : ι → X → ℝ) : X → ℝ := linPool s b

/-- Wealth shares after outcome `x` when bettor `i` stakes `s i · b i x` on each `x` and the pool pays out
in proportion to stakes on the realized outcome. -/
noncomputable def kellyShares (s : ι → ℝ) (b : ι → X → ℝ) (x : X) : ι → ℝ :=
  fun i => s i * b i x / price s b x

/-- **Kelly market = Bayes over bettors** (definitional): the share update is the Bayes/replicator step on
the bettors with likelihood/fitness `i ↦ b i x`. -/
theorem kellyShares_eq_bayes (s : ι → ℝ) (b : ι → X → ℝ) (x : X) :
    kellyShares s b x = bayes s (fun i => b i x) := rfl

/-- **Log-utility (Kelly) bettors stake their beliefs**: for any fixed odds `o > 0`, the portfolio `f = b`
maximizes expected log wealth `∑ b log(f · o)` among strictly positive portfolios (Gibbs' inequality). -/
theorem kelly_log_optimal {b f : X → ℝ} (hb : IsDist b) (hf : IsDist f) {o : X → ℝ}
    (ho : ∀ x, 0 < o x) :
    ∑ x, b x * Real.log (f x * o x) ≤ ∑ x, b x * Real.log (b x * o x) := by
  rw [← sub_nonpos, ← Finset.sum_sub_distrib]
  have hterm : ∀ x, b x * Real.log (f x * o x) - b x * Real.log (b x * o x) ≤ f x - b x := by
    intro x
    have hbx := hb.1 x; have hfx := hf.1 x
    rw [← mul_sub, Real.log_mul hfx.ne' (ho x).ne', Real.log_mul hbx.ne' (ho x).ne', add_sub_add_right_eq_sub,
      ← Real.log_div hfx.ne' hbx.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hfx hbx)
    calc b x * Real.log (f x / b x) ≤ b x * (f x / b x - 1) := mul_le_mul_of_nonneg_left this hbx.le
      _ = f x - b x := by field_simp
  calc ∑ x, (b x * Real.log (f x * o x) - b x * Real.log (b x * o x)) ≤ ∑ x, (f x - b x) :=
        Finset.sum_le_sum fun x _ => hterm x
    _ = 0 := by rw [Finset.sum_sub_distrib, hf.2, hb.2, sub_self]

/-- **Scale matters: log-linear pooling of Boltzmann members = Boltzmann of the linear sum of rewards.**
If member `i` is the softmax of a reward vector `rᵢ`, the geometric pool is the softmax of `∑ᵢ wᵢ rᵢ`
(any weights). "Linear in rewards" and "log-linear in probabilities/wealth" are the same aggregation. -/
theorem geoPool_softmax [Nonempty X] (w : ι → ℝ) (r : ι → X → ℝ) :
    geoPool w (fun i => normalize (fun x => exp (r i x))) = normalize (fun x => exp (∑ i, w i * r i x)) := by
  have hZ : ∀ i, 0 < ∑ y, exp (r i y) := fun i => sum_pos_of_pos fun y => exp_pos _
  unfold geoPool
  have : (fun x => ∏ i, normalize (fun x => exp (r i x)) x ^ w i) =
      fun x => (∏ i, ((∑ y, exp (r i y)) ^ w i)⁻¹) * exp (∑ i, w i * r i x) := by
    funext x
    rw [Real.exp_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [normalize]
    rw [div_rpow (exp_pos _).le (hZ i).le, ← exp_mul, mul_comm (r i x)]
    field_simp
  rw [this, normalize_smul (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (rpow_pos_of_pos (hZ i) _).ne')]

/-- The "organism" credit aggregator `g(u) = ∑ᵢ wᵢ uᵢ`, normalized, is linear pooling. -/
theorem pool_linear_eq_linPool {w : ι → ℝ} (hw : ∑ i, w i = 1) {P : ι → X → ℝ}
    (hP : ∀ i, IsDist (P i)) : pool (fun _ u => ∑ i, w i * u i) P = linPool w P := by
  unfold pool
  apply normalize_of_sum_eq_one
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, (hP _).2, mul_one, hw]

/-- **"Organism" credit is inconsistent under separate renormalization**: with nonnegative weights summing to
one and no member holding all the weight, the linear credit aggregator is not externally Bayesian (`|X| ≥ 2`). -/
theorem organism_credit_not_eb [Nontrivial X] {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hnd : ∀ j, w j ≠ 1) : ¬ ExternallyBayesian (X := X) (pool fun _ u => ∑ i, w i * u i) := by
  intro h
  obtain ⟨j, hj⟩ := (linPool_externallyBayesian_iff (X := X) hw0 hw).1 (fun P hP ℓ hℓ => by
    have hQ : ∀ i, IsDist (bayes (P i) ℓ) := fun i => isDist_bayes (hP i).1 hℓ
    rw [← pool_linear_eq_linPool hw hQ, ← pool_linear_eq_linPool hw hP]
    exact h P hP ℓ hℓ)
  exact hnd j hj

end BoundaryTheorem.LogPooling
