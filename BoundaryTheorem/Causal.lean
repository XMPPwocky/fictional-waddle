import Mathlib
import BoundaryTheorem.Potential

/-!
# The Kantian field is the total derivative through the real causal structure

Source: the framing "the Kantian field is just the total derivative through the real causal structure", refining
part (C) of `notes/BOOK_THEOREM.md` (§1 box (C)), whose formalization is `BoundaryTheorem/Potential.lean`.

In `Potential.lean` a slot is either an exact instance of the policy (`x_j = θ`) or a fixed external (`x_j = ξ_j`),
and kinship is the 0/1 label `j ∈ S`. Here kinship is not a label: it is the slot's **true causal response** to an
intervention on my policy. Slot `j` holds the state `g j θ` (any differentiable function of my policy `θ`), and a
learner credits slot `j`, for reward `k`, through an **assumed** response `A j k θ : V →L[ℝ] V`, giving the field

  `causalField g A R θ = Σ_{j,k} ∇_j R_k(g(θ)) ∘ A j k θ`.

A learner is *Kantian* when its assumed response is the true one, `A j k θ = c_k • D(g j)(θ)`, up to the credit
`c_k` it attaches to reward `k`. The main results:

* `hasFDerivAt_causal_potential` — **the headline, fully general.** If assumed = true response (times credit), the
  field is the derivative of `θ ↦ Σ_k c_k R_k(g(θ))` at every `θ`: the Kantian field *is* the total derivative
  through the real causal structure. No restriction on `g` beyond differentiability.
* `linear_iff` — **the characterization**, on the linear-response class `g j θ = r j • θ + b j` (slot `j` responds
  with strength `r j`: `1` for a copy, `0` for an external, anything in between for a partial reader) with scalar
  assumed responses `a j k • id`. For `dim V ≥ 2` and some `r j ≠ 0`: the field is conservative for every C² family
  iff `a j k = c k * r j` for some credit `c`. No extra hypothesis is needed; both hypotheses are shown necessary
  (`not_kantian_but_conservative_r_zero`, `not_kantian_but_conservative_dim_one`).
* `potential_iff_of_causal`, `field_eq_causalField` — `Potential.lean`'s part (C) is the special case `r ∈ {0,1}`.
* `homoMoralis_not_conservative` — homo moralis (a fully responding slot credited with `κ ≠` the self's credit) is
  not Kantian: an explicit bilinear reward gives a non-conservative field.
* `graded_hasFDerivAt` — graded relatedness done right: a slot responding with strength `r` and credited with
  `c_k · r` is Kantian; Hamilton's graded `r` is compatible with the complete self exactly when it is the true
  causal response.
* `operator_iff` — operator responses `g j θ = L j θ + b j` with operator credits `M j k`: if some slot responds
  bijectively (`L j₀` invertible) and `dim V ≥ 2`, conservative for every C² family iff `M j k = c k • L j`.
  `rank_one_counterexample` shows that the weaker hypothesis `∃ j, L j ≠ 0` does not suffice.
-/

open Finset
open BoundaryTheorem.Potential

namespace BoundaryTheorem.Causal

set_option linter.unusedSectionVars false

variable {N K V : Type*} [Fintype N] [DecidableEq N] [Fintype K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## Definitions -/

/-- The joint state of all slots when my policy is `θ`: slot `i` holds `g i θ`. This is the real causal structure:
`g i` says how slot `i` actually depends on my policy (a copy: `g i θ = θ`; something I cannot move: constant;
a partial reader: anything in between). -/
def state (g : N → V → V) (θ : V) : N → V := fun i => g i θ

/-- The learner's field. The learner credits slot `j`, for reward `k`, through the response it *assumes*,
`A j k θ : V →L[ℝ] V` (how it believes slot `j` moves when it moves its policy), so the covector it follows is
`Σ_{j,k} ∇_j R_k(g(θ)) ∘ A j k θ`, where `∇_j R_k` is the slot-`j` partial derivative of reward `k` at the true
joint state. -/
noncomputable def causalField (g : N → V → V) (A : N → K → V → (V →L[ℝ] V))
    (R : K → (N → V) → ℝ) (θ : V) : V →L[ℝ] ℝ :=
  ∑ j, ∑ k, ((fderiv ℝ (R k) (state g θ)).comp (slot j)).comp (A j k θ)

/-- A learner is Kantian when, for every slot and every reward, the response it assumes is the *true* causal response
of that slot to its policy, scaled by the credit `c k` it attaches to reward `k`. -/
def IsKantian (g : N → V → V) (A : N → K → V → (V →L[ℝ] V)) : Prop :=
  ∃ c : K → ℝ, ∀ j k θ, A j k θ = c k • fderiv ℝ (g j) θ

/-! ## The headline: the Kantian field is the total derivative through the real causal structure -/

/-- The derivative of the joint state: each slot moves by its own true response. -/
theorem hasFDerivAt_state (g : N → V → V) (hg : ∀ j, Differentiable ℝ (g j)) (θ : V) :
    HasFDerivAt (state g) (ContinuousLinearMap.pi fun j => fderiv ℝ (g j) θ) θ := by
  rw [hasFDerivAt_pi']
  intro j
  simpa [state] using (hg j θ).hasFDerivAt

/-- A functional on the joint state composed with a slot-wise map is the sum over slots of the partial derivative
composed with that slot's map. -/
theorem comp_pi (D : (N → V) →L[ℝ] ℝ) (f : N → V →L[ℝ] V) :
    D.comp (ContinuousLinearMap.pi f) = ∑ j, (D.comp (slot j)).comp (f j) := by
  ext h
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, _root_.sum_apply]
  rw [← map_sum]
  congr 1
  ext i
  simp [ContinuousLinearMap.pi_apply, Finset.sum_apply, Pi.single_apply]

/-- **The Kantian field is the total derivative through the real causal structure.** If the learner's assumed
response equals the true causal response times the credit, `A j k θ = c k • D(g j)(θ)`, and every `g j` and `R k`
is differentiable, then its field is the derivative of `θ ↦ Σ_k c_k R_k(g(θ))` at every `θ`. No assumption on the
shape of `g`: copies, externals, partial readers, nonlinear readers, all at once. -/
theorem hasFDerivAt_causal_potential (g : N → V → V) (A : N → K → V → (V →L[ℝ] V))
    (R : K → (N → V) → ℝ) (c : K → ℝ) (hA : ∀ j k θ, A j k θ = c k • fderiv ℝ (g j) θ)
    (hg : ∀ j, Differentiable ℝ (g j)) (hR : ∀ k, Differentiable ℝ (R k)) (θ : V) :
    HasFDerivAt (fun θ => ∑ k, c k * R k (state g θ)) (causalField g A R θ) θ := by
  have h : HasFDerivAt (fun θ => ∑ k, c k * R k (state g θ))
      (∑ k, c k • (fderiv ℝ (R k) (state g θ)).comp
        (ContinuousLinearMap.pi fun j => fderiv ℝ (g j) θ)) θ := by
    apply HasFDerivAt.fun_sum
    intro k _
    exact ((hR k _).hasFDerivAt.comp θ (hasFDerivAt_state g hg θ)).const_mul (c k)
  convert h using 1
  simp only [causalField, comp_pi, hA, ContinuousLinearMap.comp_smul, Finset.smul_sum]
  exact Finset.sum_comm

/-- A Kantian learner's field is conservative, for every differentiable causal structure and reward family. -/
theorem conservative_of_isKantian (g : N → V → V) (A : N → K → V → (V →L[ℝ] V))
    (hA : IsKantian g A) (R : K → (N → V) → ℝ)
    (hg : ∀ j, Differentiable ℝ (g j)) (hR : ∀ k, Differentiable ℝ (R k)) :
    Conservative (causalField g A R) := by
  obtain ⟨c, hc⟩ := hA
  exact ⟨_, hasFDerivAt_causal_potential g A R c hc hg hR⟩

/-! ## The bilinear test reward through an arbitrary causal structure -/

/-- The field of the bilinear test reward `R_{k₀}(x) = α(x_i) β(x_j)` (other rewards zero) through any causal
structure `g` and any assumed responses `A`:
`F(θ) = β(g_j θ) · α ∘ A_{i k₀}(θ) + α(g_i θ) · β ∘ A_{j k₀}(θ)`. -/
theorem causalField_testFamily [DecidableEq K] (g : N → V → V) (A : N → K → V → (V →L[ℝ] V))
    (k₀ : K) (i j : N) (α β : V →L[ℝ] ℝ) (θ : V) :
    causalField g A (testFamily k₀ i j α β) θ =
      β (g j θ) • α.comp (A i k₀ θ) + α (g i θ) • β.comp (A j k₀ θ) := by
  have hD : ∀ k, fderiv ℝ (testFamily k₀ i j α β k) (state g θ) =
      if k = k₀ then bilinDeriv i j α β (state g θ) else 0 := by
    intro k
    by_cases hk : k = k₀
    · simp [testFamily, hk, (hasFDerivAt_bilin i j α β _).fderiv]
    · simp [testFamily, hk]
  have hk : ∀ j' : N, ∑ k, ((fderiv ℝ (testFamily k₀ i j α β k) (state g θ)).comp (slot j')).comp (A j' k θ) =
      ((bilinDeriv i j α β (state g θ)).comp (slot j')).comp (A j' k₀ θ) := by
    intro j'
    rw [Finset.sum_eq_single k₀]
    · simp [hD]
    · intro k _ hk
      simp [hD, hk]
    · simp
  simp only [causalField, hk]
  ext h
  simp [bilinDeriv, Pi.single_apply, apply_ite, Finset.sum_add_distrib, state]
  ring

/-! ## The linear-response class: slot `j` responds with strength `r j`, credited with weight `a j k` -/

/-- Linear response: slot `j` holds `r j • θ + b j`. `r j = 1` is an exact copy (instance), `r j = 0` an external
that does not move with my policy, `0 < r j < 1` a partial reader (a predictor, a learner on a finite hold), and
negative or larger values are allowed too. -/
def linResp (r : N → ℝ) (b : N → V) : N → V → V := fun j θ => r j • θ + b j

/-- Scalar assumed responses: the learner credits slot `j` for reward `k` with the weight `a j k`, i.e. it assumes
slot `j` moves like `a j k • id` when it moves its policy. This is the boundary matrix `W` of part (C). -/
def scalarA (a : N → K → ℝ) : N → K → V → (V →L[ℝ] V) := fun j k _ => a j k • ContinuousLinearMap.id ℝ V

theorem hasFDerivAt_linResp (r : N → ℝ) (b : N → V) (j : N) (θ : V) :
    HasFDerivAt (linResp r b j) (r j • ContinuousLinearMap.id ℝ V) θ := by
  unfold linResp
  exact ((hasFDerivAt_id (𝕜 := ℝ) θ).const_smul (r j)).add_const (b j)

/-- The true causal response of a linear slot is `r j • id`. -/
theorem fderiv_linResp (r : N → ℝ) (b : N → V) (j : N) (θ : V) :
    fderiv ℝ (linResp r b j) θ = r j • ContinuousLinearMap.id ℝ V :=
  (hasFDerivAt_linResp r b j θ).fderiv

theorem differentiable_linResp (r : N → ℝ) (b : N → V) (j : N) : Differentiable ℝ (linResp r b j) :=
  fun θ => (hasFDerivAt_linResp r b j θ).differentiableAt

/-- Crediting slot `j` with `c k * r j` is exactly "assumed response = true response times credit". -/
theorem scalarA_kantian (r : N → ℝ) (b : N → V) (c : K → ℝ) (j : N) (k : K) (θ : V) :
    scalarA (fun j k => c k * r j) j k θ = c k • fderiv ℝ (linResp r b j) θ := by
  simp [scalarA, fderiv_linResp, mul_smul]

/-- **The cross condition.** If the field of the bilinear test reward coupling slots `i` and `j` (in reward `k₀`) is
conservative, then `a_{i k₀} r_j = a_{j k₀} r_i`: the credit each slot receives must be proportional to its true
response, with the same constant. (`α, β, u, v` is a dual pair; the field is affine in `θ`, and its linear part
must be a symmetric bilinear form.) -/
theorem cross_eq [DecidableEq K] (r : N → ℝ) (b : N → V) (a : N → K → ℝ) (k₀ : K) (i j : N)
    {α β : V →L[ℝ] ℝ} {u v : V}
    (hαu : α u = 1) (hαv : α v = 0) (hβu : β u = 0) (hβv : β v = 1)
    (hC : Conservative (causalField (linResp r b) (scalarA a) (testFamily k₀ i j α β))) :
    a i k₀ * r j = a j k₀ * r i := by
  set F' : V →L[ℝ] V →L[ℝ] ℝ := (a i k₀ * r j) • β.smulRight α + (a j k₀ * r i) • α.smulRight β
  have hF : causalField (linResp r b) (scalarA a) (testFamily k₀ i j α β) =
      fun θ => F' θ + ((a i k₀ * β (b j)) • α + (a j k₀ * α (b i)) • β) := by
    funext θ
    rw [causalField_testFamily]
    ext w
    simp [F', linResp, scalarA]
    ring
  have hder : HasFDerivAt (causalField (linResp r b) (scalarA a) (testFamily k₀ i j α β)) F' 0 := by
    rw [hF]
    exact F'.hasFDerivAt.add_const _
  have := symm_of_conservative hC hder v u
  simpa [F', hαu, hαv, hβu, hβv] using this

/-- **The characterization on the linear-response class.** Let slot `j` respond to my policy with strength `r j`
(any reals; some slot must respond at all, `∃ j, r j ≠ 0`), let `dim V ≥ 2`, and let the learner credit slot `j`
for reward `k` with weight `a j k`. Then its field is conservative for every C² reward family iff there is a credit
vector `c` with `a j k = c k * r j` for all `j, k`: iff the assumed response is the true response times the credit.
No further hypothesis is needed. -/
theorem linear_iff [FiniteDimensional ℝ V] (h2 : 2 ≤ Module.finrank ℝ V) (r : N → ℝ) (hr : ∃ j, r j ≠ 0)
    (b : N → V) (a : N → K → ℝ) :
    (∀ R : K → (N → V) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) →
        Conservative (causalField (linResp r b) (scalarA a) R)) ↔
      ∃ c : K → ℝ, ∀ j k, a j k = c k * r j := by
  classical
  constructor
  · intro h
    obtain ⟨α, β, u, v, hαu, hαv, hβu, hβv⟩ := exists_dualPair (V := V) h2
    obtain ⟨j₀, hj₀⟩ := hr
    refine ⟨fun k => a j₀ k / r j₀, fun j k => ?_⟩
    have := cross_eq r b a k j j₀ hαu hαv hβu hβv (h _ (contDiff_testFamily k j j₀ α β))
    field_simp
    linarith
  · rintro ⟨c, hc⟩ R hR
    have : a = fun j k => c k * r j := funext fun j => funext fun k => hc j k
    subst this
    exact conservative_of_isKantian _ _ ⟨c, scalarA_kantian r b c⟩ R (differentiable_linResp r b)
      fun k => (hR k).differentiable (by norm_num)

/-- **Graded relatedness done right.** A slot responding with strength `r j` and credited with `c k * r j` is
Kantian: the field is the derivative of `θ ↦ Σ_k c_k R_k(g(θ))`. Hamilton's graded `r` is compatible with the
complete self exactly when `r` is the true causal response (and `linear_iff` says: only then). -/
theorem graded_hasFDerivAt (r : N → ℝ) (b : N → V) (c : K → ℝ) (R : K → (N → V) → ℝ)
    (hR : ∀ k, Differentiable ℝ (R k)) (θ : V) :
    HasFDerivAt (fun θ => ∑ k, c k * R k (state (linResp r b) θ))
      (causalField (linResp r b) (scalarA fun j k => c k * r j) R θ) θ :=
  hasFDerivAt_causal_potential _ _ R c (scalarA_kantian r b c) (differentiable_linResp r b) hR θ

/-- **Homo moralis is not Kantian.** Two slots `s, t` both respond fully (`r = 1`: the self and a full copy of it),
but the learner credits them differently in reward `k₀` (`a t k₀ = κ ≠ a s k₀`, e.g. the self at `1` and the copy
at `κ < 1`). Then the explicit bilinear reward `α(x_s) β(x_t)` gives a non-conservative field. -/
theorem homoMoralis_not_conservative [DecidableEq K] (r : N → ℝ) (b : N → V) (a : N → K → ℝ) (k₀ : K)
    {s t : N} (hs : r s = 1) (ht : r t = 1) (hκ : a t k₀ ≠ a s k₀)
    {α β : V →L[ℝ] ℝ} {u v : V}
    (hαu : α u = 1) (hαv : α v = 0) (hβu : β u = 0) (hβv : β v = 1) :
    ¬ Conservative (causalField (linResp r b) (scalarA a) (testFamily k₀ s t α β)) := by
  intro hC
  have := cross_eq r b a k₀ s t hαu hαv hβu hβv hC
  rw [hs, ht, mul_one, mul_one] at this
  exact hκ this.symm

/-- The homo moralis field written out (base states `0`): `F(θ) = a_{s k₀} β(θ) α + a_{t k₀} α(θ) β`. In `ℝ²` with
`α, β` the coordinates this is `(a_{s k₀} θ₂, a_{t k₀} θ₁)`, whose curl is `a_{t k₀} − a_{s k₀}`. -/
theorem homoMoralis_field_eq [DecidableEq K] (r : N → ℝ) (a : N → K → ℝ) (k₀ : K)
    {s t : N} (hs : r s = 1) (ht : r t = 1) (α β : V →L[ℝ] ℝ) (θ : V) :
    causalField (linResp r 0) (scalarA a) (testFamily k₀ s t α β) θ =
      (a s k₀ * β θ) • α + (a t k₀ * α θ) • β := by
  rw [causalField_testFamily]
  ext w
  simp [linResp, scalarA, hs, ht]
  ring

/-- Homo moralis in coordinates, `V = ℝ²`, reward `R(x) = x_{s,0} · x_{t,1}`. -/
theorem homoMoralis_not_conservative_fin2 [DecidableEq K] (r : N → ℝ) (b : N → (Fin 2 → ℝ))
    (a : N → K → ℝ) (k₀ : K) {s t : N} (hs : r s = 1) (ht : r t = 1) (hκ : a t k₀ ≠ a s k₀) :
    ¬ Conservative (causalField (linResp r b) (scalarA a)
      (testFamily k₀ s t (ContinuousLinearMap.proj 0) (ContinuousLinearMap.proj 1))) :=
  homoMoralis_not_conservative r b a k₀ hs ht hκ (u := Pi.single 0 1) (v := Pi.single 1 1)
    (by simp) (by simp) (by simp) (by simp)

/-! ## Part (C) of `Potential.lean` is the special case `r ∈ {0, 1}` -/

/-- The diagonal embedding of `Potential.lean` is the linear response with `r = 1_S` and base states `ξ` off `S`. -/
theorem state_linResp_indicator (S : Finset N) (ξ : N → V) (θ : V) :
    state (linResp (fun j => if j ∈ S then 1 else 0) (fun j => if j ∈ S then 0 else ξ j)) θ =
      embed S ξ θ := by
  funext j
  by_cases hj : j ∈ S <;> simp [state, linResp, embed, hj]

/-- **The two fields coincide.** `Potential.field S ξ W R` is `causalField` for the response `r = 1_S` (instances
respond exactly, externals not at all), base states `ξ`, and scalar credits `W`. -/
theorem field_eq_causalField (S : Finset N) (ξ : N → V) (W : N → K → ℝ) (R : K → (N → V) → ℝ) (θ : V) :
    field S ξ W R θ =
      causalField (linResp (fun j => if j ∈ S then 1 else 0) (fun j => if j ∈ S then 0 else ξ j))
        (scalarA W) R θ := by
  simp only [causalField, field, state_linResp_indicator, scalarA, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_id]

/-- The two Kantian conditions agree on the `0/1` class: `W j k = c k * 1_S(j)` iff `W = (1_S, 0_E) cᵀ`. -/
theorem isKantian_iff (S : Finset N) (W : N → K → ℝ) :
    (∃ c : K → ℝ, ∀ j k, W j k = c k * (if j ∈ S then 1 else 0)) ↔
      ∃ c : K → ℝ, ∀ j k, W j k = if j ∈ S then c k else 0 := by
  constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨c, fun j k => ?_⟩ <;> have := hc j k <;>
    by_cases hj : j ∈ S <;> simp_all

/-- **`potential_iff` re-derived** from `linear_iff`: part (C) with `S ≠ ∅` is the case `r = 1_S` of the causal
characterization (`S ≠ ∅` is `∃ j, r j ≠ 0`). Same statement as `BoundaryTheorem.Potential.potential_iff`. -/
theorem potential_iff_of_causal [FiniteDimensional ℝ V] (S : Finset N) (hS : S.Nonempty)
    (h2 : 2 ≤ Module.finrank ℝ V) (ξ : N → V) (W : N → K → ℝ) :
    (∀ R : K → (N → V) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) → Conservative (field S ξ W R)) ↔
      ∃ c : K → ℝ, ∀ j k, W j k = if j ∈ S then c k else 0 := by
  have hf : ∀ R : K → (N → V) → ℝ, field S ξ W R =
      causalField (linResp (fun j => if j ∈ S then 1 else 0) (fun j => if j ∈ S then 0 else ξ j))
        (scalarA W) R := fun R => funext (field_eq_causalField S ξ W R)
  simp_rw [hf]
  obtain ⟨s, hs⟩ := hS
  rw [linear_iff h2 _ ⟨s, by simp [hs]⟩, isKantian_iff]

/-! ## The hypotheses of `linear_iff` are needed -/

/-- Continuity of the field in `θ` for continuous responses and a C¹ family. -/
theorem continuous_causalField (g : N → V → V) (A : N → K → V → (V →L[ℝ] V)) (R : K → (N → V) → ℝ)
    (hg : ∀ j, Continuous (g j)) (hA : ∀ j k, Continuous (A j k)) (hR : ∀ k, ContDiff ℝ 1 (R k)) :
    Continuous (causalField g A R) := by
  have hs : Continuous (state g) := continuous_pi hg
  unfold causalField
  refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
  exact ((((hR k).continuous_fderiv (by norm_num)).comp hs).clm_comp continuous_const).clm_comp (hA j k)

/-- **`∃ j, r j ≠ 0` is needed.** If no slot responds to my policy the field does not depend on `θ`, so it is
conservative whatever the learner assumes. -/
theorem conservative_of_r_zero (b : N → V) (a : N → K → ℝ) (R : K → (N → V) → ℝ) :
    Conservative (causalField (linResp (fun _ => 0) b) (scalarA a) R) := by
  have hconst : ∀ θ, causalField (linResp (fun _ => 0) b) (scalarA a) R θ =
      causalField (linResp (fun _ => 0) b) (scalarA a) R 0 := by
    intro θ
    have : state (linResp (fun _ => (0 : ℝ)) b) θ = state (linResp (fun _ => 0) b) 0 := by
      funext j; simp [state, linResp]
    simp only [causalField, this, scalarA]
  exact ⟨fun θ => causalField (linResp (fun _ => 0) b) (scalarA a) R 0 θ, fun θ => by
    rw [hconst θ]; exact (causalField (linResp (fun _ => 0) b) (scalarA a) R 0).hasFDerivAt⟩

/-- With `r = 0` everywhere, any nonzero credit `a e k ≠ 0` is non-Kantian (`c k * 0 ≠ a e k`) yet conservative for
every C² family: the "only if" of `linear_iff` fails without `∃ j, r j ≠ 0`. -/
theorem not_kantian_but_conservative_r_zero {k : K} (b : N → V) (a : N → K → ℝ) {e : N} (ha : a e k ≠ 0) :
    ¬ (∃ c : K → ℝ, ∀ j k, a j k = c k * (fun _ : N => (0 : ℝ)) j) ∧
      ∀ R : K → (N → V) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) →
        Conservative (causalField (linResp (fun _ => 0) b) (scalarA a) R) := by
  refine ⟨fun ⟨c, hc⟩ => ha (by simpa using hc e k), fun R _ => conservative_of_r_zero b a R⟩

/-- **`dim V ≥ 2` is needed.** On a line every continuous field is a gradient (fundamental theorem of calculus). -/
theorem conservative_dim_one (r : N → ℝ) (b : N → ℝ) (a : N → K → ℝ) (R : K → (N → ℝ) → ℝ)
    (hR : ∀ k, ContDiff ℝ 1 (R k)) : Conservative (causalField (linResp r b) (scalarA a) R) := by
  have hcont : Continuous (causalField (linResp r b) (scalarA a) R) :=
    continuous_causalField _ _ R (fun j => (differentiable_linResp r b j).continuous)
      (fun j k => continuous_const) hR
  have hc : Continuous fun θ => causalField (linResp r b) (scalarA a) R θ 1 :=
    hcont.clm_apply continuous_const
  refine ⟨fun θ => ∫ t in (0 : ℝ)..θ, causalField (linResp r b) (scalarA a) R t 1, fun θ => ?_⟩
  have h := (hc.integral_hasStrictDerivAt 0 θ).hasDerivAt.hasFDerivAt
  convert h using 1
  ext
  simp

/-- For `V = ℝ`, a non-responding slot (`r e = 0`) credited with nonzero weight is non-Kantian yet conservative for
every C² family: the "only if" of `linear_iff` fails without `dim V ≥ 2`. -/
theorem not_kantian_but_conservative_dim_one {k : K} (r : N → ℝ) (b : N → ℝ) (a : N → K → ℝ) {e : N}
    (he : r e = 0) (ha : a e k ≠ 0) :
    ¬ (∃ c : K → ℝ, ∀ j k, a j k = c k * r j) ∧
      ∀ R : K → (N → ℝ) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) →
        Conservative (causalField (linResp r b) (scalarA a) R) :=
  ⟨fun ⟨c, hc⟩ => ha (by simpa [he] using hc e k),
    fun R hR => conservative_dim_one r b a R fun k => (hR k).of_le (by norm_num)⟩

/-! ## General linear responses with operator credit -/

/-- Affine operator response: slot `j` holds `L j θ + b j` (my policy seen through the linear channel `L j`). -/
def affResp (L : N → V →L[ℝ] V) (b : N → V) : N → V → V := fun j θ => L j θ + b j

/-- Constant operator credit: the learner assumes slot `j` responds to reward `k` through the operator `M j k`. -/
def constA (M : N → K → V →L[ℝ] V) : N → K → V → (V →L[ℝ] V) := fun j k _ => M j k

theorem hasFDerivAt_affResp (L : N → V →L[ℝ] V) (b : N → V) (j : N) (θ : V) :
    HasFDerivAt (affResp L b j) (L j) θ := by
  unfold affResp
  exact (L j).hasFDerivAt.add_const (b j)

/-- The true causal response of an affine slot is its channel `L j`. -/
theorem fderiv_affResp (L : N → V →L[ℝ] V) (b : N → V) (j : N) (θ : V) :
    fderiv ℝ (affResp L b j) θ = L j :=
  (hasFDerivAt_affResp L b j θ).fderiv

theorem differentiable_affResp (L : N → V →L[ℝ] V) (b : N → V) (j : N) : Differentiable ℝ (affResp L b j) :=
  fun θ => (hasFDerivAt_affResp L b j θ).differentiableAt

/-- The operator cross condition: conservativity of the bilinear test reward coupling slots `i, j` forces the
bilinear form `(v, w) ↦ β(L_j v) α(M_{i k₀} w) + α(L_i v) β(M_{j k₀} w)` to be symmetric. -/
theorem op_cross [DecidableEq K] (L : N → V →L[ℝ] V) (b : N → V) (M : N → K → V →L[ℝ] V) (k₀ : K) (i j : N)
    (α β : V →L[ℝ] ℝ)
    (hC : Conservative (causalField (affResp L b) (constA M) (testFamily k₀ i j α β))) (v w : V) :
    β (L j v) * α (M i k₀ w) + α (L i v) * β (M j k₀ w) =
      β (L j w) * α (M i k₀ v) + α (L i w) * β (M j k₀ v) := by
  set F' : V →L[ℝ] V →L[ℝ] ℝ :=
    (β.comp (L j)).smulRight (α.comp (M i k₀)) + (α.comp (L i)).smulRight (β.comp (M j k₀))
  have hF : causalField (affResp L b) (constA M) (testFamily k₀ i j α β) =
      fun θ => F' θ + (β (b j) • α.comp (M i k₀) + α (b i) • β.comp (M j k₀)) := by
    funext θ
    rw [causalField_testFamily]
    ext x
    simp [F', affResp, constA]
    ring
  have hder : HasFDerivAt (causalField (affResp L b) (constA M) (testFamily k₀ i j α β)) F' 0 := by
    rw [hF]
    exact F'.hasFDerivAt.add_const _
  have := symm_of_conservative hC hder v w
  simpa [F'] using this

/-- Linear algebra: if `(v, w) ↦ β(v) α(M w) + α(v) β(M w)` is symmetric for all functionals `α, β`, then `M` is a
scalar multiple of the identity (`dim V ≥ 2`). -/
theorem eq_smul_id_of_symm [FiniteDimensional ℝ V] (h2 : 2 ≤ Module.finrank ℝ V) (M : V →L[ℝ] V)
    (h : ∀ (α β : V →L[ℝ] ℝ) (v w : V),
      β v * α (M w) + α v * β (M w) = β w * α (M v) + α w * β (M v)) :
    ∃ c : ℝ, M = c • ContinuousLinearMap.id ℝ V := by
  let bs := Module.finBasis ℝ V
  let φ : Fin (Module.finrank ℝ V) → V →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (bs.coord i)
  have hφ : ∀ i l, φ i (bs l) = if i = l then 1 else 0 := by
    intro i l
    simp [φ, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  have hoff : ∀ i l, i ≠ l → φ i (M (bs l)) = 0 := by
    intro i l hil
    have := h (φ i) (φ i) (bs i) (bs l)
    simp [hφ, hil] at this
    linarith
  have hdiag : ∀ i l, i ≠ l → φ l (M (bs l)) = φ i (M (bs i)) := by
    intro i l hil
    have := h (φ i) (φ l) (bs i) (bs l)
    simpa [hφ, hil, hil.symm] using this
  let i0 : Fin (Module.finrank ℝ V) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank ℝ V) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  refine ⟨φ i0 (M (bs i0)), ?_⟩
  apply ContinuousLinearMap.coe_injective
  apply bs.ext
  intro l
  apply bs.ext_elem
  intro i
  have hrepr : ∀ x, bs.repr x i = φ i x := fun x => by simp [φ, Module.Basis.coord_apply]
  simp only [ContinuousLinearMap.coe_coe, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, Finsupp.smul_apply, smul_eq_mul, hrepr, hφ]
  by_cases hil : i = l
  · subst hil
    simp only [ite_true, mul_one]
    by_cases hi0 : i = i0
    · subst hi0; rfl
    · exact hdiag i0 i (Ne.symm hi0)
  · simp [hil, hoff i l hil]

/-- A bijectively responding slot pins its own credit to a scalar multiple of its channel. -/
theorem op_self [FiniteDimensional ℝ V] (h2 : 2 ≤ Module.finrank ℝ V) (L M : V →L[ℝ] V)
    (hL : Function.Bijective L)
    (h : ∀ (α β : V →L[ℝ] ℝ) (v w : V),
      β (L v) * α (M w) + α (L v) * β (M w) = β (L w) * α (M v) + α (L w) * β (M v)) :
    ∃ c : ℝ, M = c • L := by
  let e : V ≃L[ℝ] V := (LinearEquiv.ofBijective (L : V →ₗ[ℝ] V) hL).toContinuousLinearEquiv
  have he : ∀ x, e x = L x := fun x => rfl
  have hes : ∀ x, L (e.symm x) = x := fun x => by rw [← he]; exact e.apply_symm_apply x
  have hes' : ∀ x, e.symm (L x) = x := fun x => by rw [← he]; exact e.symm_apply_apply x
  obtain ⟨c, hc⟩ := eq_smul_id_of_symm h2 (M.comp (e.symm : V →L[ℝ] V)) fun α β v w => by
    simpa [hes] using h α β (e.symm v) (e.symm w)
  refine ⟨c, ?_⟩
  ext x
  have := congrArg (fun T : V →L[ℝ] V => T (L x)) hc
  simpa [he, hes'] using this

/-- A bijectively responding slot `L₀` with credit `c • L₀` forces every other slot's credit to `c • L`. -/
theorem op_pair [FiniteDimensional ℝ V] (h2 : 2 ≤ Module.finrank ℝ V) (L₀ L M : V →L[ℝ] V) (c : ℝ)
    (hL : Function.Bijective L₀)
    (h : ∀ (α β : V →L[ℝ] ℝ) (v w : V),
      β (L₀ v) * α (M w) + α (L v) * β ((c • L₀) w) = β (L₀ w) * α (M v) + α (L w) * β ((c • L₀) v)) :
    M = c • L := by
  let e : V ≃L[ℝ] V := (LinearEquiv.ofBijective (L₀ : V →ₗ[ℝ] V) hL).toContinuousLinearEquiv
  have he : ∀ x, e x = L₀ x := fun x => rfl
  have hes : ∀ x, e.symm (L₀ x) = x := fun x => by rw [← he]; exact e.symm_apply_apply x
  set P : V →L[ℝ] V := M - c • L with hP
  have hP' : ∀ (α β : V →L[ℝ] ℝ) (v w : V), β (L₀ v) * α (P w) = β (L₀ w) * α (P v) := by
    intro α β v w
    have := h α β v w
    simp only [hP, sub_apply, smul_apply, map_sub, map_smul, smul_eq_mul] at this ⊢
    linarith
  let bs := Module.finBasis ℝ V
  let φ : Fin (Module.finrank ℝ V) → V →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (bs.coord i)
  have hφ : ∀ i l, φ i (bs l) = if i = l then 1 else 0 := by
    intro i l
    simp [φ, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  have hzero : ∀ l, P (bs l) = 0 := by
    intro l
    obtain ⟨i, hil⟩ : ∃ i, i ≠ l := by
      by_cases hl : l = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by rw [hl]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, by omega⟩, Ne.symm hl⟩
    apply bs.ext_elem
    intro m
    have := hP' (φ m) ((φ i).comp (e.symm : V →L[ℝ] V)) (bs i) (bs l)
    simp [hes, hφ, hil] at this
    simpa [φ, Module.Basis.coord_apply] using this
  have : P = 0 := ContinuousLinearMap.coe_injective (bs.ext fun l => by simpa using hzero l)
  exact sub_eq_zero.mp this

/-- **Operator responses.** Slot `j` holds `L j θ + b j`, the learner credits it through the operator `M j k`.
If some slot responds bijectively (`L j₀` invertible: a copy, or the policy seen through an invertible channel) and
`dim V ≥ 2`, then the field is conservative for every C² family iff `M j k = c k • L j` for some credit `c`: the
assumed operator response is the true channel times the credit. -/
theorem operator_iff [FiniteDimensional ℝ V] (h2 : 2 ≤ Module.finrank ℝ V) (L : N → V →L[ℝ] V)
    (hL : ∃ j₀, Function.Bijective (L j₀)) (b : N → V) (M : N → K → V →L[ℝ] V) :
    (∀ R : K → (N → V) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) →
        Conservative (causalField (affResp L b) (constA M) R)) ↔
      ∃ c : K → ℝ, ∀ j k, M j k = c k • L j := by
  classical
  constructor
  · intro h
    obtain ⟨j₀, hj₀⟩ := hL
    have hself : ∀ k, ∃ c : ℝ, M j₀ k = c • L j₀ := fun k =>
      op_self h2 (L j₀) (M j₀ k) hj₀ fun α β v w =>
        op_cross L b M k j₀ j₀ α β (h _ (contDiff_testFamily k j₀ j₀ α β)) v w
    choose c hc using hself
    refine ⟨c, fun j k => ?_⟩
    apply op_pair h2 (L j₀) (L j) (M j k) (c k) hj₀
    intro α β v w
    have := op_cross L b M k j j₀ α β (h _ (contDiff_testFamily k j j₀ α β)) v w
    rwa [hc k] at this
  · rintro ⟨c, hc⟩ R hR
    refine conservative_of_isKantian _ _ ⟨c, fun j k θ => ?_⟩ R (differentiable_affResp L b)
      fun k => (hR k).differentiable (by norm_num)
    simp [constA, fderiv_affResp, hc]

/-! ## Rank-one responses: `∃ j, L j ≠ 0` is not enough for `operator_iff` -/

/-- **The one-dimensional phenomenon returns through the channel.** If every slot sees my policy only through one
scalar `φ(θ)` (`L j = φ ⊗ u j`) and the learner's assumed responses factor through the same scalar
(`M j k = φ ⊗ u' j k`, with `u'` arbitrary), the field is `ψ(φ θ) φ` for a continuous `ψ`, hence a gradient for
every C¹ family, however wrong `u'` is. -/
theorem conservative_rank_one (φ : V →L[ℝ] ℝ) (u : N → V) (b : N → V) (u' : N → K → V)
    (R : K → (N → V) → ℝ) (hR : ∀ k, ContDiff ℝ 1 (R k)) :
    Conservative (causalField (affResp (fun j => φ.smulRight (u j)) b)
      (constA fun j k => φ.smulRight (u' j k)) R) := by
  set xt : ℝ → (N → V) := fun t i => t • u i + b i with hxt
  have hxc : Continuous xt := continuous_pi fun i => (continuous_id.smul continuous_const).add continuous_const
  set ψ : ℝ → ℝ := fun t => ∑ j, ∑ k, fderiv ℝ (R k) (xt t) (Pi.single j (u' j k)) with hψ
  have hψc : Continuous ψ := by
    refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
    exact (((hR k).continuous_fderiv (by norm_num)).comp hxc).clm_apply continuous_const
  have hstate : ∀ θ, state (affResp (fun j => φ.smulRight (u j)) b) θ = xt (φ θ) := by
    intro θ; funext i; simp [state, affResp, xt]
  have hfield : ∀ θ, causalField (affResp (fun j => φ.smulRight (u j)) b)
      (constA fun j k => φ.smulRight (u' j k)) R θ = ψ (φ θ) • φ := by
    intro θ
    ext h
    simp only [causalField, hstate, constA, FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, smul_eq_mul, hψ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm, ← smul_eq_mul, ← map_smul]
    congr 1
    simp [slot]
  refine ⟨fun θ => ∫ t in (0 : ℝ)..φ θ, ψ t, fun θ => ?_⟩
  rw [hfield]
  exact ((hψc.integral_hasStrictDerivAt 0 (φ θ)).hasDerivAt).comp_hasFDerivAt θ φ.hasFDerivAt

/-- **The bijectivity hypothesis of `operator_iff` cannot be weakened to `∃ j, L j ≠ 0`.** In `V = ℝ²` let every
slot respond through `L = e₀ ⊗ (proj 0)` (nonzero, rank one) and let the learner credit through
`M = e₁ ⊗ (proj 0)`: `M` is not `c • L` for any `c`, yet the field is conservative for every C² family. -/
theorem rank_one_counterexample [Nonempty N] [Nonempty K] (b : N → Fin 2 → ℝ) :
    ((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight (Pi.single 0 1 : Fin 2 → ℝ)) ≠ 0 ∧
    ¬ (∃ c : K → ℝ, ∀ (_ : N) (k : K),
      ((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight (Pi.single 1 1 : Fin 2 → ℝ)) =
        c k • ((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight (Pi.single 0 1 : Fin 2 → ℝ))) ∧
    ∀ R : K → (N → Fin 2 → ℝ) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) →
      Conservative (causalField
        (affResp (fun _ => (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight (Pi.single 0 1)) b)
        (constA fun _ _ => (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight (Pi.single 1 1)) R) := by
  refine ⟨?_, ?_, fun R hR => conservative_rank_one _ _ b _ R fun k => (hR k).of_le (by norm_num)⟩
  · intro h
    have := congrArg (fun T : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) => T (Pi.single 0 1) 0) h
    simp at this
  · rintro ⟨c, hc⟩
    obtain ⟨j⟩ := ‹Nonempty N›
    obtain ⟨k⟩ := ‹Nonempty K›
    have := congrArg (fun T : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) => T (Pi.single 0 1) 1) (hc j k)
    simp at this

end BoundaryTheorem.Causal
