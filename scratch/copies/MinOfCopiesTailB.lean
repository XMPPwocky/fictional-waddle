import Mathlib

/-!
# Minimum of independent copies of a run time

PROVED
* `survival_inter_eq_prod`: for independent random variables `T i` (`i : Fin N`) with values in a
  linearly ordered space, `P(∀ i, T i > t) = ∏ i, P(T i > t)`.
* `minimum_survival_eq_prod`: for `N + 1` independent copies, the minimum `min_i T i` satisfies
  `P(min > t) = ∏ i, P(T i > t)`.
* `minimum_survival_eq_pow`: if all copies have the same survival value `S` at `t`, then
  `P(min > t) = S ^ (N + 1)`; i.e. the survival function of the minimum is `S(t) ^ N`.
* `minimum_survival_eq_pow_fun`: the same as an identity of survival functions, for all `t`.
* `firstSuccess_gt_iff`: in the explicit Bernoulli model, copy `i` survives past `t`
  (first success index `> t`, steps counted from 1) iff its first `t` trials all fail.
* `minFirstSuccess_gt_iff`: the minimum over copies survives past `t` iff all `N * t` trials
  in the block `Fin N × {0, …, t-1}` fail.
* `copy_survival`: in the explicit model `P(T i > t) = (1 - p) ^ t` (each copy is geometric).
* `minimum_survival_model`: in the explicit model `P(min_i T i > t) = (1 - p) ^ (N * t)`.
* `minimum_survival_model_eq_pow_copy`: `P(min > t) = P(T i > t) ^ N`.
* `minimum_survival_model_geometric`: `P(min > t) = (1 - q) ^ t` with `q = 1 - (1 - p) ^ N`,
  i.e. the minimum is geometric with per-step success probability `1 - (1 - p) ^ N`.
* `tail_strictAnti`: for real `0 < p < 1` and `t ≥ 1`, `N ↦ (1 - p) ^ (N * t)` is strictly
  decreasing.
* `minimum_survival_model_strictAnti`: for `0 < p < 1` and `t ≥ 1`, the model probability
  `P(min of N copies > t)` is strictly decreasing in `N`.

INTERPRETED
* The explicit discrete model is the product (Mathlib `Measure.infinitePi`) of Bernoulli(`p`)
  trials indexed by `Fin N × ℕ`; copy `i` succeeds at step `s` (0-based) iff `ω (i, s) = true`.
  The run time of copy `i` is the 1-based index of its first success, valued in `ℕ∞`
  (`⊤` if it never succeeds). The minimum is `Finset.univ.inf` over copies (`⊤` if `N = 0`).
* `p` ranges over `unitInterval`; the strict-decrease statements assume `0 < p < 1`, since for
  `p = 0` the tail is constantly `1`.
-/

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace MinOfCopiesTailB

section General

variable {Ω β : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
  [OpensMeasurableSpace β]

theorem survival_inter_eq_prod {N : ℕ} (T : Fin N → Ω → β) (hind : iIndepFun T μ) (t : β) :
    μ {ω | ∀ i, t < T i ω} = ∏ i, μ {ω | t < T i ω} := by
  have h := hind.measure_inter_preimage_eq_mul Finset.univ (sets := fun _ => Set.Ioi t)
    (fun _ _ => measurableSet_Ioi)
  have hset : (⋂ i ∈ (Finset.univ : Finset (Fin N)), T i ⁻¹' Set.Ioi t)
      = {ω | ∀ i, t < T i ω} := by
    ext ω; simp
  rw [hset] at h
  exact h

/-- The minimum of `N + 1` copies. -/
def minimum {N : ℕ} (T : Fin (N + 1) → Ω → β) (ω : Ω) : β :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => T i ω)

omit [MeasurableSpace Ω] [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
  [OpensMeasurableSpace β] in
theorem lt_minimum_iff {N : ℕ} (T : Fin (N + 1) → Ω → β) (t : β) (ω : Ω) :
    t < minimum T ω ↔ ∀ i, t < T i ω := by
  simp [minimum, Finset.lt_inf'_iff]

theorem minimum_survival_eq_prod {N : ℕ} (T : Fin (N + 1) → Ω → β) (hind : iIndepFun T μ)
    (t : β) : μ {ω | t < minimum T ω} = ∏ i, μ {ω | t < T i ω} := by
  have : {ω | t < minimum T ω} = {ω | ∀ i, t < T i ω} := by
    ext ω; simp [lt_minimum_iff]
  rw [this, survival_inter_eq_prod T hind t]

theorem minimum_survival_eq_pow {N : ℕ} (T : Fin (N + 1) → Ω → β) (hind : iIndepFun T μ)
    (t : β) (S : ℝ≥0∞) (hS : ∀ i, μ {ω | t < T i ω} = S) :
    μ {ω | t < minimum T ω} = S ^ (N + 1) := by
  rw [minimum_survival_eq_prod T hind t]
  simp [hS]

theorem minimum_survival_eq_pow_fun {N : ℕ} (T : Fin (N + 1) → Ω → β) (hind : iIndepFun T μ)
    (S : β → ℝ≥0∞) (hS : ∀ i t, μ {ω | t < T i ω} = S t) :
    (fun t => μ {ω | t < minimum T ω}) = fun t => S t ^ (N + 1) := by
  funext t
  exact minimum_survival_eq_pow T hind t (S t) (fun i => hS i t)

end General

section Model

/-- Sample space: outcome of trial `s` of copy `i`. -/
abbrev Omega (N : ℕ) := Fin N × ℕ → Bool

/-- Independent Bernoulli(`p`) trials, `true` meaning success. -/
noncomputable def model (N : ℕ) (p : I) : Measure (Omega N) :=
  Measure.infinitePi (fun _ : Fin N × ℕ => bernoulliMeasure true false p)

instance (N : ℕ) (p : I) : IsProbabilityMeasure (model N p) := by
  unfold model; infer_instance

open Classical in
/-- 1-based index of the first success of copy `i`, or `⊤` if it never succeeds. -/
noncomputable def firstSuccess {N : ℕ} (i : Fin N) (ω : Omega N) : ℕ∞ :=
  if h : ∃ s, ω (i, s) = true then ((Nat.find h + 1 : ℕ) : ℕ∞) else ⊤

/-- Run time of the fastest copy. -/
noncomputable def minFirstSuccess {N : ℕ} (ω : Omega N) : ℕ∞ :=
  Finset.univ.inf (fun i => firstSuccess i ω)

theorem firstSuccess_gt_iff {N : ℕ} (i : Fin N) (ω : Omega N) (t : ℕ) :
    (t : ℕ∞) < firstSuccess i ω ↔ ∀ s < t, ω (i, s) = false := by
  classical
  unfold firstSuccess
  split_ifs with h
  · rw [ENat.natCast_lt_natCast, Nat.lt_succ_iff, Nat.le_find_iff]
    simp
  · push Not at h
    simp only [ENat.natCast_lt_top, true_iff]
    intro s _
    simpa using h s

theorem minFirstSuccess_gt_iff {N : ℕ} (ω : Omega N) (t : ℕ) :
    (t : ℕ∞) < minFirstSuccess ω ↔ ∀ i : Fin N, ∀ s < t, ω (i, s) = false := by
  unfold minFirstSuccess
  rw [Finset.lt_inf_iff (ENat.natCast_lt_top t)]
  simp [firstSuccess_gt_iff]

theorem bernoulli_false (p : I) :
    bernoulliMeasure true false p {false} = (toNNReal (σ p) : ℝ≥0∞) := by
  simp

theorem block_eq_pi {N : ℕ} (t : ℕ) :
    {ω : Omega N | (t : ℕ∞) < minFirstSuccess ω}
      = Set.pi ((Finset.univ ×ˢ Finset.range t : Finset (Fin N × ℕ)) : Set (Fin N × ℕ))
          (fun _ => {false}) := by
  ext ω
  simp only [Set.mem_ofPred_eq, minFirstSuccess_gt_iff, Set.mem_pi, Finset.coe_product,
    Finset.coe_univ, Finset.coe_range, Set.mem_prod, Set.mem_univ, Set.mem_Iio, true_and,
    Set.mem_singleton_iff, Prod.forall]

theorem copy_eq_pi {N : ℕ} (i : Fin N) (t : ℕ) :
    {ω : Omega N | (t : ℕ∞) < firstSuccess i ω}
      = Set.pi ((({i} : Finset (Fin N)) ×ˢ Finset.range t : Finset (Fin N × ℕ)) : Set (Fin N × ℕ))
          (fun _ => {false}) := by
  ext ω
  simp only [Set.mem_ofPred_eq, firstSuccess_gt_iff, Set.mem_pi, Finset.coe_product,
    Finset.coe_singleton, Finset.coe_range, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Iio,
    Prod.forall]
  constructor
  · rintro h j s ⟨rfl, hs⟩; exact h s hs
  · intro h s hs; exact h i s ⟨rfl, hs⟩

theorem minimum_survival_model_ennreal (N : ℕ) (p : I) (t : ℕ) :
    model N p {ω | (t : ℕ∞) < minFirstSuccess ω} = (toNNReal (σ p) : ℝ≥0∞) ^ (N * t) := by
  rw [block_eq_pi, model, Measure.infinitePi_pi _ (fun _ _ => MeasurableSet.singleton _)]
  simp [Finset.prod_const]

theorem copy_survival_ennreal (N : ℕ) (p : I) (i : Fin N) (t : ℕ) :
    model N p {ω | (t : ℕ∞) < firstSuccess i ω} = (toNNReal (σ p) : ℝ≥0∞) ^ t := by
  rw [copy_eq_pi, model, Measure.infinitePi_pi _ (fun _ _ => MeasurableSet.singleton _)]
  simp [Finset.prod_const]

theorem toReal_symm (p : I) : ((toNNReal (σ p) : ℝ≥0∞)).toReal = 1 - (p : ℝ) := by
  rw [ENNReal.coe_toReal]
  rfl

theorem minimum_survival_model (N : ℕ) (p : I) (t : ℕ) :
    (model N p).real {ω | (t : ℕ∞) < minFirstSuccess ω} = (1 - (p : ℝ)) ^ (N * t) := by
  rw [measureReal_def, minimum_survival_model_ennreal, ENNReal.toReal_pow, toReal_symm]

theorem copy_survival (N : ℕ) (p : I) (i : Fin N) (t : ℕ) :
    (model N p).real {ω | (t : ℕ∞) < firstSuccess i ω} = (1 - (p : ℝ)) ^ t := by
  rw [measureReal_def, copy_survival_ennreal, ENNReal.toReal_pow, toReal_symm]

theorem minimum_survival_model_eq_pow_copy (N : ℕ) (p : I) (i : Fin N) (t : ℕ) :
    (model N p).real {ω | (t : ℕ∞) < minFirstSuccess ω}
      = ((model N p).real {ω | (t : ℕ∞) < firstSuccess i ω}) ^ N := by
  rw [minimum_survival_model, copy_survival, ← pow_mul, mul_comm]

theorem minimum_survival_model_geometric (N : ℕ) (p : I) (t : ℕ) :
    (model N p).real {ω | (t : ℕ∞) < minFirstSuccess ω}
      = (1 - (1 - (1 - (p : ℝ)) ^ N)) ^ t := by
  rw [minimum_survival_model, sub_sub_cancel, ← pow_mul]

theorem tail_strictAnti {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {t : ℕ} (ht : 1 ≤ t) :
    StrictAnti (fun N : ℕ => (1 - p) ^ (N * t)) := by
  have hb0 : 0 < (1 - p) ^ t := pow_pos (by linarith) t
  have hb1 : (1 - p) ^ t < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  intro m n hmn
  simp only [mul_comm _ t, pow_mul]
  exact pow_lt_pow_right_of_lt_one₀ hb0 hb1 hmn

theorem minimum_survival_model_strictAnti (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {t : ℕ} (ht : 1 ≤ t) :
    StrictAnti (fun N : ℕ => (model N p).real {ω | (t : ℕ∞) < minFirstSuccess ω}) := by
  simp only [minimum_survival_model]
  exact tail_strictAnti hp0 hp1 ht

end Model

end MinOfCopiesTailB
