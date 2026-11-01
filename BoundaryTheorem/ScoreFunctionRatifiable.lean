import Mathlib

/-!
# The bridge: score-function (REINFORCE) stationarity = ratifiability, and the direct/indirect split

Setting. A finite nonempty set of actions `A`, a logit vector `θ : A → ℝ`, the full-support softmax policy
`softmax θ a = exp(θ a) / Σ_b exp(θ b)`, and a Newcomb-like decision problem given by a payoff
`Q : (A → ℝ) → A → ℝ`: `Q π a` is the expected payoff of action `a` when the world (e.g. a predictor)
responds to the *policy* `π`. Expected return `J Q θ = Σ_a softmax θ a * Q (softmax θ) a`.

Three results, in the order of the prose claim.

**(1) Decomposition** (`hasFDerivAt_J`, `fderiv_J_single`). For `Q` differentiable in `π` at `softmax θ`,
`∂J/∂θ_k = reinforce Q θ k + indirect Q θ k`, where
* `reinforce Q θ k = Σ_a π_a · score θ a k · Q(π,a)` is the *expected REINFORCE update*
  (`score θ a k = ∂ log π_a / ∂θ_k`, proved in `score_eq_fderiv_log_softmax`); it equals the
  "direct effect" `Σ_a (∂π_a/∂θ_k) Q(π,a)` (`reinforce_eq_direct`), which treats `Q(π,·)` as fixed, and
* `indirect Q θ k = Σ_a π_a · ∂/∂θ_k [Q(softmax θ, a)]` is the "indirect effect / interference" term, the
  part that only policy-level credit sees.

**(2) Stationarity ⇒ ratifiability** (`reinforce_eq_zero_iff_ratifiable`, `reinforce_eq`,
`reinforce_eq_zero_iff_const`). `reinforce Q θ k = π_k (Q(π,k) − J)`, so the expected REINFORCE update
vanishes iff `Q(π,·)` is constant iff `π` is ratifiable (every supported action is a best response to `π`),
and conversely. On the simplex (`scoreUpdate`): ratifiable ⇒ stationary for every `π`
(`scoreUpdate_eq_zero_of_ratifiable`); stationary ⇒ ratifiable needs full support
(`ratifiable_of_scoreUpdate_eq_zero`), and `newcomb_pure_scoreUpdate_zero` / `newcomb_pure_not_ratifiable`
show the full-support hypothesis cannot be dropped.

**(3) Separation** (`AO_*`). The adversarial offer with two boxes and a decline option, prize 3, price 1,
predictor reading the policy: `Q(π, buy i) = 3(1 − π_i) − 1`, `Q(π, decline) = 0`. `J ≤ 2/3` everywhere with
equality exactly at the uniform policy (`θ = 0`), so `θ = 0` is a global maximiser of `J` over all of `ℝ³` and a
stationary point of the total gradient (`AO_hasFDerivAt_J_zero`), but it is **not** ratifiable
(`AO_not_ratifiable`) and the expected REINFORCE update there is `(1/9, 1/9, −2/9) ≠ 0`
(`AO_reinforce_zero`); the indirect term exactly cancels it (`AO_indirect_zero`).

**Further sections** (added after adversarial review, round 1).
* *Boundary stationarity is vacuous*: `scoreUpdate_single_eq_zero` (every vertex is score-stationary for every `Q`).
* *`AO` has no interior ratifiable policy*: `AO_not_ratifiable_all`, `AO_reinforce_ne_zero_all`,
  `AO_ratifiable_iff` (the only ratifiable simplex point is `(1/2,1/2,0)`), `AO_value_gap` (`1/2 < 2/3`).
* *General parametrised policies* `π = f w` (`Jp`, `frozen`, `directP`, `indirectP`, `FirstOrderRatifiable`):
  `hasFDerivAt_frozen`, `hasFDerivAt_Jp`, `directP_eq_zero_iff_firstOrderRatifiable`,
  `firstOrderRatifiable_softmax_iff` (tabular softmax ⇒ BLOS ratifiability), `firstOrderRatifiable_const`
  (in general it is weaker).
* *Policy-level randomisation*: `antithetic`, `tendsto_symmDiff`, `tendsto_antithetic_grad`,
  `tendsto_antithetic_J` (the `σ → 0` limit of the antithetic estimator is `reinforce + indirect`).
* *Boundary limits*: `limit_const_on_support` (limits of convergent interior REINFORCE trajectories have `Q`
  constant on their support) — the within-support half of boundary ratifiability only.

Everything is about the *mean* (expected) update and the exact gradient; see `FIDELITY_ratifiable.md` for what
is not covered (stochastic iterates, the unplayed-action half at the boundary, finite-`σ` smoothing bias, Adam,
action-reading predictors, conditional independence of the world's response from the sampled action).
-/

open Finset
open ContinuousLinearMap (proj)

namespace BoundaryTheorem.ScoreFunctionRatifiable

set_option linter.unusedSectionVars false

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-! ## Softmax and its exact derivative -/

/-- The partition function `Z θ = Σ_b exp(θ b)`. -/
noncomputable def Z (θ : A → ℝ) : ℝ := ∑ b, Real.exp (θ b)

/-- The softmax policy `π_θ(a) = exp(θ a) / Z θ`. -/
noncomputable def softmax (θ : A → ℝ) : A → ℝ := fun a => Real.exp (θ a) / Z θ

theorem Z_pos (θ : A → ℝ) : 0 < Z θ :=
  Finset.sum_pos (fun b _ => Real.exp_pos (θ b)) Finset.univ_nonempty

/-- Full support: every softmax probability is strictly positive. -/
theorem softmax_pos (θ : A → ℝ) (a : A) : 0 < softmax θ a :=
  div_pos (Real.exp_pos _) (Z_pos θ)

theorem softmax_nonneg (θ : A → ℝ) (a : A) : 0 ≤ softmax θ a := (softmax_pos θ a).le

/-- `softmax θ` is a probability vector. -/
theorem sum_softmax (θ : A → ℝ) : ∑ a, softmax θ a = 1 := by
  unfold softmax
  rw [← Finset.sum_div]
  exact div_self (Z_pos θ).ne'

/-- The REINFORCE score `∂ log π_a / ∂θ_k = 1_{a = k} − π_k` (see `score_eq_fderiv_log_softmax`). -/
noncomputable def score (θ : A → ℝ) (a k : A) : ℝ := (if a = k then 1 else 0) - softmax θ k

/-- The derivative of `θ ↦ softmax θ a`, as a covector: `π_a • (e_a − Σ_b π_b e_b)`. -/
noncomputable def softmaxDeriv (θ : A → ℝ) (a : A) : (A → ℝ) →L[ℝ] ℝ :=
  softmax θ a • ((proj a : (A → ℝ) →L[ℝ] ℝ) - ∑ b, softmax θ b • (proj b : (A → ℝ) →L[ℝ] ℝ))

/-- `∂π_a/∂θ_k = π_a (1_{a=k} − π_k)`: the softmax-gradient identity. -/
theorem softmaxDeriv_single (θ : A → ℝ) (a k : A) :
    softmaxDeriv θ a (Pi.single k 1) = softmax θ a * score θ a k := by
  simp only [softmaxDeriv, score, smul_apply, sub_apply, _root_.sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  congr 2
  · exact Pi.single_apply k (1 : ℝ) a
  · simp [Pi.single_apply, Finset.sum_ite_eq']

theorem hasFDerivAt_Z (θ : A → ℝ) :
    HasFDerivAt Z (∑ b, Real.exp (θ b) • (proj b : (A → ℝ) →L[ℝ] ℝ)) θ := by
  have h := HasFDerivAt.sum (u := Finset.univ) (x := θ)
    (A := fun b (θ : A → ℝ) => Real.exp (θ b)) (A' := fun b => Real.exp (θ b) • proj b)
    (fun b _ => (hasFDerivAt_apply b θ).exp)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun θ => by simp [Z, Finset.sum_apply])

/-- Softmax is differentiable, coordinatewise, with the derivative `softmaxDeriv`. -/
theorem hasFDerivAt_softmax_apply (θ : A → ℝ) (a : A) :
    HasFDerivAt (fun θ => softmax θ a) (softmaxDeriv θ a) θ := by
  have hnum : HasFDerivAt (fun θ : A → ℝ => Real.exp (θ a)) (Real.exp (θ a) • proj a) θ :=
    (hasFDerivAt_apply a θ).exp
  have hinv : HasFDerivAt (fun θ => (Z θ)⁻¹)
      ((-(Z θ ^ 2)⁻¹) • ∑ b, Real.exp (θ b) • (proj b : (A → ℝ) →L[ℝ] ℝ)) θ :=
    (hasDerivAt_inv (Z_pos θ).ne').comp_hasFDerivAt θ (hasFDerivAt_Z θ)
  have h := hnum.mul hinv
  have h2 : HasFDerivAt (fun θ => softmax θ a) _ θ :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun θ => by
      simp [softmax, div_eq_mul_inv])
  refine h2.congr_fderiv ?_
  ext v
  simp only [softmaxDeriv, add_apply, smul_apply, sub_apply, _root_.sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, softmax]
  have hS : ∑ b, Real.exp (θ b) / Z θ * v b = (∑ b, Real.exp (θ b) * v b) / Z θ := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun b _ => by ring
  rw [hS]
  have hZ := (Z_pos θ).ne'
  field_simp
  ring

/-- The full derivative `softmaxFDeriv θ : (A → ℝ) →L[ℝ] (A → ℝ)` of `softmax` at `θ`. -/
noncomputable def softmaxFDeriv (θ : A → ℝ) : (A → ℝ) →L[ℝ] (A → ℝ) :=
  ContinuousLinearMap.pi (fun a => softmaxDeriv θ a)

theorem hasFDerivAt_softmax (θ : A → ℝ) : HasFDerivAt softmax (softmaxFDeriv θ) θ :=
  hasFDerivAt_pi.2 (fun a => hasFDerivAt_softmax_apply θ a)

/-- The score is the gradient of the log-policy: `score θ a k = ∂ log π_a / ∂θ_k`. -/
theorem score_eq_fderiv_log_softmax (θ : A → ℝ) (a k : A) :
    fderiv ℝ (fun θ => Real.log (softmax θ a)) θ (Pi.single k 1) = score θ a k := by
  rw [((hasFDerivAt_softmax_apply θ a).log (softmax_pos θ a).ne').fderiv]
  simp only [smul_apply, smul_eq_mul, softmaxDeriv_single]
  rw [← mul_assoc, inv_mul_cancel₀ (softmax_pos θ a).ne', one_mul]

/-! ## Expected return, the REINFORCE mean update, the direct and indirect terms -/

/-- Expected return `J(θ) = Σ_a π_θ(a) Q(π_θ, a)` when the world responds to the policy. -/
noncomputable def J (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) : ℝ := ∑ a, softmax θ a * Q (softmax θ) a

/-- The **expected REINFORCE (score-function) update**, component `k`:
`E_{a ∼ π_θ}[ (∂ log π_θ(a)/∂θ_k) · Q(π_θ, a) ]`. The sampled score never sees how `Q(π,·)` depends on `θ`. -/
noncomputable def reinforce (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) (k : A) : ℝ :=
  ∑ a, softmax θ a * score θ a k * Q (softmax θ) a

/-- The **direct effect** `Σ_a (∂π_a/∂θ_k) Q(π,a)` (Q held fixed). -/
noncomputable def direct (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) (k : A) : ℝ :=
  ∑ a, fderiv ℝ (fun θ => softmax θ a) θ (Pi.single k 1) * Q (softmax θ) a

/-- The **indirect effect / interference** term `Σ_a π_a · ∂/∂θ_k [Q(π_θ, a)]`. -/
noncomputable def indirect (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) (k : A) : ℝ :=
  ∑ a, softmax θ a * fderiv ℝ (fun θ => Q (softmax θ) a) θ (Pi.single k 1)

/-- REINFORCE's expected update *is* the direct-effect term. -/
theorem reinforce_eq_direct (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) (k : A) :
    reinforce Q θ k = direct Q θ k := by
  unfold reinforce direct
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [(hasFDerivAt_softmax_apply θ a).fderiv, softmaxDeriv_single]

/-- **(1) Decomposition, operator form.** For `Q` differentiable in `π` at `π_θ` with derivative `Q' a`,
`dJ = Σ_a Q(π,a) • dπ_a + Σ_a π_a • (Q' a ∘ dπ)`. -/
theorem hasFDerivAt_J (Q : (A → ℝ) → A → ℝ) (Q' : A → (A → ℝ) →L[ℝ] ℝ) (θ : A → ℝ)
    (hQ : ∀ a, HasFDerivAt (fun π => Q π a) (Q' a) (softmax θ)) :
    HasFDerivAt (J Q)
      (∑ a, Q (softmax θ) a • softmaxDeriv θ a +
        ∑ a, softmax θ a • (Q' a).comp (softmaxFDeriv θ)) θ := by
  have hterm : ∀ a ∈ (Finset.univ : Finset A),
      HasFDerivAt (fun θ => softmax θ a * Q (softmax θ) a)
        (softmax θ a • (Q' a).comp (softmaxFDeriv θ) + Q (softmax θ) a • softmaxDeriv θ a) θ := by
    intro a _
    have hc : HasFDerivAt (fun θ => Q (softmax θ) a) ((Q' a).comp (softmaxFDeriv θ)) θ :=
      (hQ a).comp θ (hasFDerivAt_softmax θ)
    exact (hasFDerivAt_softmax_apply θ a).mul hc
  have h := HasFDerivAt.sum hterm
  have h2 : HasFDerivAt (J Q) _ θ :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun θ => by simp [J, Finset.sum_apply])
  refine h2.congr_fderiv ?_
  rw [Finset.sum_add_distrib, add_comm]

/-- **(1) Decomposition, component form.** `∂J/∂θ_k = reinforce Q θ k + indirect Q θ k`:
the expected REINFORCE update plus the interference term. -/
theorem fderiv_J_single (Q : (A → ℝ) → A → ℝ) (Q' : A → (A → ℝ) →L[ℝ] ℝ) (θ : A → ℝ)
    (hQ : ∀ a, HasFDerivAt (fun π => Q π a) (Q' a) (softmax θ)) (k : A) :
    fderiv ℝ (J Q) θ (Pi.single k 1) = reinforce Q θ k + indirect Q θ k := by
  rw [(hasFDerivAt_J Q Q' θ hQ).fderiv]
  simp only [add_apply, _root_.sum_apply, smul_apply, smul_eq_mul, softmaxDeriv_single]
  congr 1
  · unfold reinforce
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  · unfold indirect
    refine Finset.sum_congr rfl fun a _ => ?_
    have hc : HasFDerivAt (fun θ => Q (softmax θ) a) ((Q' a).comp (softmaxFDeriv θ)) θ :=
      (hQ a).comp θ (hasFDerivAt_softmax θ)
    rw [hc.fderiv]

/-- Differentiability of `J` (so the `fderiv` in `fderiv_J_single` is the honest derivative). -/
theorem differentiableAt_J (Q : (A → ℝ) → A → ℝ) (Q' : A → (A → ℝ) →L[ℝ] ℝ) (θ : A → ℝ)
    (hQ : ∀ a, HasFDerivAt (fun π => Q π a) (Q' a) (softmax θ)) :
    DifferentiableAt ℝ (J Q) θ :=
  (hasFDerivAt_J Q Q' θ hQ).differentiableAt

/-! ## (2) Stationarity of the REINFORCE mean dynamics ⇔ ratifiability -/

/-- `π` is **ratifiable** (Bell–Linsefors–Oesterheld–Skalse 2021): every action in the support of `π` is a best
response to `π` itself, i.e. `supp π ⊆ argmax_a Q(π, a)`. -/
def Ratifiable (Q : (A → ℝ) → A → ℝ) (π : A → ℝ) : Prop :=
  ∀ a, 0 < π a → ∀ b, Q π b ≤ Q π a

/-- Closed form of the expected REINFORCE update: `reinforce Q θ k = π_k (Q(π,k) − J(θ))`. -/
theorem reinforce_eq (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) (k : A) :
    reinforce Q θ k = softmax θ k * (Q (softmax θ) k - J Q θ) := by
  unfold reinforce J score
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · simp [mul_ite, ite_mul, Finset.sum_ite_eq']
  · refine Finset.sum_congr rfl fun a _ => ?_
    ring

/-- The expected REINFORCE update vanishes iff `Q(π_θ, ·)` is constant. -/
theorem reinforce_eq_zero_iff_const (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) :
    reinforce Q θ = 0 ↔ ∀ a b, Q (softmax θ) a = Q (softmax θ) b := by
  constructor
  · intro h a b
    have ha := congrFun h a
    have hb := congrFun h b
    rw [reinforce_eq] at ha hb
    have ha' : Q (softmax θ) a - J Q θ = 0 :=
      (mul_eq_zero.1 ha).resolve_left (softmax_pos θ a).ne'
    have hb' : Q (softmax θ) b - J Q θ = 0 :=
      (mul_eq_zero.1 hb).resolve_left (softmax_pos θ b).ne'
    linarith
  · intro h
    funext k
    rw [reinforce_eq, Pi.zero_apply]
    have hJ : J Q θ = Q (softmax θ) k := by
      unfold J
      calc ∑ a, softmax θ a * Q (softmax θ) a = ∑ a, softmax θ a * Q (softmax θ) k :=
            Finset.sum_congr rfl fun a _ => by rw [h a k]
        _ = Q (softmax θ) k := by rw [← Finset.sum_mul, sum_softmax, one_mul]
    rw [hJ, sub_self, mul_zero]

/-- With full support, ratifiable ⇔ `Q(π,·)` constant. -/
theorem ratifiable_iff_const_of_pos (Q : (A → ℝ) → A → ℝ) (π : A → ℝ) (hπ : ∀ a, 0 < π a) :
    Ratifiable Q π ↔ ∀ a b, Q π a = Q π b := by
  constructor
  · intro h a b
    exact le_antisymm (h b (hπ b) a) (h a (hπ a) b)
  · intro h a _ b
    exact (h b a).le

/-- **(2) Stationarity ⇔ ratifiability.** For the full-support softmax policy, the expected REINFORCE update
vanishes at `θ` iff `π_θ` is ratifiable. -/
theorem reinforce_eq_zero_iff_ratifiable (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) :
    reinforce Q θ = 0 ↔ Ratifiable Q (softmax θ) := by
  rw [reinforce_eq_zero_iff_const, ratifiable_iff_const_of_pos Q _ (softmax_pos θ)]

/-- Every REINFORCE-stationary softmax policy is ratifiable (the direction the bridge needs). -/
theorem ratifiable_of_reinforce_eq_zero (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) (h : reinforce Q θ = 0) :
    Ratifiable Q (softmax θ) :=
  (reinforce_eq_zero_iff_ratifiable Q θ).1 h

/-! ### The same statement on the simplex, with the full-support hypothesis made explicit -/

/-- The mean REINFORCE update written in policy coordinates: `π_k (Q(π,k) − Σ_a π_a Q(π,a))`.
On the softmax image it coincides with `reinforce` (`reinforce_eq_scoreUpdate`). -/
noncomputable def scoreUpdate (Q : (A → ℝ) → A → ℝ) (π : A → ℝ) (k : A) : ℝ :=
  π k * (Q π k - ∑ a, π a * Q π a)

theorem reinforce_eq_scoreUpdate (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) :
    reinforce Q θ = scoreUpdate Q (softmax θ) := by
  funext k; rw [reinforce_eq]; rfl

/-- Ratifiable ⇒ score-function stationary, for *every* `π` on the simplex (no full-support needed). -/
theorem scoreUpdate_eq_zero_of_ratifiable (Q : (A → ℝ) → A → ℝ) (π : A → ℝ)
    (hπ0 : ∀ a, 0 ≤ π a) (hπ1 : ∑ a, π a = 1) (h : Ratifiable Q π) : scoreUpdate Q π = 0 := by
  funext k
  unfold scoreUpdate
  rcases (hπ0 k).lt_or_eq with hk | hk
  · have hsum : ∑ a, π a * Q π a = Q π k := by
      calc ∑ a, π a * Q π a = ∑ a, π a * Q π k := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rcases (hπ0 a).lt_or_eq with ha | ha
            · rw [le_antisymm (h k hk a) (h a ha k)]
            · rw [← ha, zero_mul, zero_mul]
        _ = Q π k := by rw [← Finset.sum_mul, hπ1, one_mul]
    rw [hsum, sub_self, mul_zero, Pi.zero_apply]
  · rw [← hk, zero_mul, Pi.zero_apply]

/-- Score-function stationary ⇒ ratifiable, **given full support**. -/
theorem ratifiable_of_scoreUpdate_eq_zero (Q : (A → ℝ) → A → ℝ) (π : A → ℝ)
    (hπ : ∀ a, 0 < π a) (h : scoreUpdate Q π = 0) : Ratifiable Q π := by
  have hc : ∀ a, Q π a = ∑ b, π b * Q π b := by
    intro a
    have := congrFun h a
    unfold scoreUpdate at this
    rw [Pi.zero_apply] at this
    have := (mul_eq_zero.1 this).resolve_left (hπ a).ne'
    linarith
  intro a _ b
  rw [hc a, hc b]

/-! ## (3) Separation: the adversarial offer -/

/-- **Policy-reading adversarial-offer variant** (two boxes + decline; prize 3, price 1). This is *not* the
textbook (Spencer–Wells) adversarial offer, whose predictor predicts the realised *action*; here the seller's
predictor reads the *policy* and fills box `i` with probability `1 − π_i` (the probability that the agent does
not buy it). So `Q(π, buy i) = 3(1 − π_i) − 1 = 2 − 3π_i` for `i = 0, 1`, and `Q(π, decline) = 0` for action
`2`. Its optimum (uniform policy, `J = 2/3`) differs from the textbook analysis. -/
noncomputable def AO : (Fin 3 → ℝ) → Fin 3 → ℝ := fun π a => if a = 2 then 0 else 2 - 3 * π a

/-- Derivative of `AO` in `π`, actionwise. -/
noncomputable def AO' (a : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  if a = 2 then 0 else -((3 : ℝ) • (proj a : (Fin 3 → ℝ) →L[ℝ] ℝ))

theorem AO_hasFDerivAt (π : Fin 3 → ℝ) (a : Fin 3) : HasFDerivAt (fun π => AO π a) (AO' a) π := by
  fin_cases a
  · simp only [AO, AO', Fin.zero_eta, Fin.isValue, Fin.reduceEq, ite_false]
    exact ((hasFDerivAt_apply (0 : Fin 3) π).const_mul 3).const_sub 2
  · simp only [AO, AO', Fin.mk_one, Fin.isValue, Fin.reduceEq, ite_false]
    exact ((hasFDerivAt_apply (1 : Fin 3) π).const_mul 3).const_sub 2
  · simp only [AO, AO', Fin.reduceFinMk, Fin.isValue, ite_true]
    exact hasFDerivAt_const 0 π

/-- The uniform policy: `softmax 0 = (1/3, 1/3, 1/3)`. -/
theorem softmax_zero_fin3 (a : Fin 3) : softmax (0 : Fin 3 → ℝ) a = 1 / 3 := by
  simp [softmax, Z]

/-- `J(θ) = Σ_{i<2} (2π_i − 3π_i²)` for the adversarial offer. -/
theorem AO_J (θ : Fin 3 → ℝ) :
    J AO θ = softmax θ 0 * (2 - 3 * softmax θ 0) + softmax θ 1 * (2 - 3 * softmax θ 1) := by
  simp [J, AO, Fin.sum_univ_three]

/-- `J ≤ 2/3` for every logit vector (indeed for every `π ∈ ℝ³`). -/
theorem AO_J_le (θ : Fin 3 → ℝ) : J AO θ ≤ 2 / 3 := by
  rw [AO_J]
  nlinarith [sq_nonneg (softmax θ 0 - 1 / 3), sq_nonneg (softmax θ 1 - 1 / 3)]

/-- The bound is attained at the uniform policy `θ = 0`. -/
theorem AO_J_zero : J AO (0 : Fin 3 → ℝ) = 2 / 3 := by
  rw [AO_J, softmax_zero_fin3, softmax_zero_fin3]; norm_num

/-- The maximisers of `J` are exactly the logits whose policy is uniform. -/
theorem AO_J_eq_iff (θ : Fin 3 → ℝ) :
    J AO θ = 2 / 3 ↔ softmax θ 0 = 1 / 3 ∧ softmax θ 1 = 1 / 3 := by
  rw [AO_J]
  constructor
  · intro h
    have h0 := sq_nonneg (softmax θ 0 - 1 / 3)
    have h1 := sq_nonneg (softmax θ 1 - 1 / 3)
    have hsum : 3 * (softmax θ 0 - 1 / 3) ^ 2 + 3 * (softmax θ 1 - 1 / 3) ^ 2 = 0 := by nlinarith
    constructor <;> nlinarith
  · rintro ⟨h0, h1⟩; rw [h0, h1]; norm_num

/-- `θ = 0` is a global maximiser of `J` over all of `ℝ³`. -/
theorem AO_isMaxOn : ∀ θ : Fin 3 → ℝ, J AO θ ≤ J AO 0 := by
  intro θ; rw [AO_J_zero]; exact AO_J_le θ

/-- **(3a) Total-gradient stationarity.** `J` is differentiable at `θ = 0` with derivative `0`
(direct + indirect effect vanish together). -/
theorem AO_hasFDerivAt_J_zero : HasFDerivAt (J AO) (0 : (Fin 3 → ℝ) →L[ℝ] ℝ) (0 : Fin 3 → ℝ) := by
  have h := hasFDerivAt_J AO AO' 0 (fun a => AO_hasFDerivAt _ a)
  have hmax : IsLocalMax (J AO) (0 : Fin 3 → ℝ) := Filter.Eventually.of_forall AO_isMaxOn
  rw [← hmax.hasFDerivAt_eq_zero h]
  exact h

theorem AO_fderiv_J_zero : fderiv ℝ (J AO) (0 : Fin 3 → ℝ) = 0 :=
  AO_hasFDerivAt_J_zero.fderiv

/-- **(3b) Not ratifiable.** At the uniform policy, `decline` is in the support but `buy 0` pays `1 > 0`. -/
theorem AO_not_ratifiable : ¬ Ratifiable AO (softmax (0 : Fin 3 → ℝ)) := by
  intro h
  have := h 2 (by rw [softmax_zero_fin3]; norm_num) 0
  norm_num [AO, softmax_zero_fin3] at this

/-- **(3c) The expected REINFORCE update at the maximiser is `(1/9, 1/9, −2/9)`.** -/
theorem AO_reinforce_zero (k : Fin 3) :
    reinforce AO (0 : Fin 3 → ℝ) k = if k = 2 then -2 / 9 else 1 / 9 := by
  rw [reinforce_eq, AO_J_zero, softmax_zero_fin3]
  fin_cases k <;> simp [AO, softmax_zero_fin3] <;> norm_num

theorem AO_reinforce_ne_zero : reinforce AO (0 : Fin 3 → ℝ) ≠ 0 := by
  intro h
  have := congrFun h 2
  rw [AO_reinforce_zero] at this
  norm_num at this

/-- Hence `θ = 0` is not a stationary point of the REINFORCE mean dynamics (via (2)). -/
theorem AO_not_reinforce_stationary : ¬ reinforce AO (0 : Fin 3 → ℝ) = 0 := AO_reinforce_ne_zero

/-- **(3d) The indirect term exactly cancels the direct one:** `indirect = (−1/9, −1/9, 2/9)`. -/
theorem AO_indirect_zero (k : Fin 3) :
    indirect AO (0 : Fin 3 → ℝ) k = if k = 2 then 2 / 9 else -1 / 9 := by
  have h := fderiv_J_single AO AO' 0 (fun a => AO_hasFDerivAt _ a) k
  rw [AO_fderiv_J_zero, zero_apply, AO_reinforce_zero] at h
  split_ifs at h ⊢ <;> linarith

/-! ## Newcomb's problem: boundary maximiser, never REINFORCE-stationary in the interior -/

/-- **Newcomb** (payoffs in thousands). Action `0` = one-box, `1` = two-box. The predictor reads the policy and
fills the opaque box with probability `π_0`: `Q(π, one-box) = 1000 π_0`, `Q(π, two-box) = 1000 π_0 + 1`. -/
noncomputable def newcomb : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun π a => if a = 0 then 1000 * π 0 else 1000 * π 0 + 1

/-- `J = 999 π_0 + 1`. -/
theorem newcomb_J (θ : Fin 2 → ℝ) : J newcomb θ = 999 * softmax θ 0 + 1 := by
  have h := sum_softmax θ
  rw [Fin.sum_univ_two] at h
  have h1 : softmax θ 1 = 1 - softmax θ 0 := by linarith
  unfold J newcomb
  rw [Fin.sum_univ_two, h1]
  simp
  ring

/-- No softmax policy is REINFORCE-stationary for Newcomb (two-boxing always pays 1 more). -/
theorem newcomb_reinforce_ne_zero (θ : Fin 2 → ℝ) : reinforce newcomb θ ≠ 0 := by
  rw [Ne, reinforce_eq_zero_iff_const]
  intro h
  have := h 0 1
  simp [newcomb] at this

/-- `J < 1000` on every softmax policy: the supremum `1000` (pure one-boxing) is not attained in the interior. -/
theorem newcomb_J_lt (θ : Fin 2 → ℝ) : J newcomb θ < 1000 := by
  rw [newcomb_J]
  have h1 := sum_softmax θ
  have h2 := softmax_pos θ 1
  simp [Fin.sum_univ_two] at h1
  linarith

/-- The pure one-boxing policy `(1, 0)`. -/
noncomputable def oneBox : Fin 2 → ℝ := ![1, 0]

/-- On the boundary, the score-function update vanishes at pure one-boxing … -/
theorem newcomb_pure_scoreUpdate_zero : scoreUpdate newcomb oneBox = 0 := by
  funext k
  fin_cases k <;> simp [scoreUpdate, newcomb, oneBox, Fin.sum_univ_two]

/-- … but pure one-boxing is **not** ratifiable: two-boxing is a strictly better response to it. So the
"stationary ⇒ ratifiable" direction of (2) genuinely needs full support. -/
theorem newcomb_pure_not_ratifiable : ¬ Ratifiable newcomb oneBox := by
  intro h
  have := h 0 (by simp [oneBox]) 1
  simp [newcomb, oneBox] at this
  linarith


/-! ## Boundary stationarity is vacuous -/

/-- At a pure policy (vertex `Pi.single a 1`) the score-function update vanishes for **every** payoff `Q`.
Boundary stationarity therefore carries no information about ratifiability at all. -/
theorem scoreUpdate_single_eq_zero (Q : (A → ℝ) → A → ℝ) (a : A) :
    scoreUpdate Q (Pi.single a 1) = 0 := by
  funext k
  unfold scoreUpdate
  have hs : ∑ b, (Pi.single a (1 : ℝ) : A → ℝ) b * Q (Pi.single a 1) b = Q (Pi.single a 1) a := by
    simp [Pi.single_apply]
  rw [hs, Pi.zero_apply]
  by_cases hk : k = a
  · subst hk; simp
  · simp [hk]

theorem oneBox_eq_single : oneBox = Pi.single (0 : Fin 2) (1 : ℝ) := by
  funext k; fin_cases k <;> simp [oneBox]

/-- `newcomb_pure_scoreUpdate_zero` is an instance of the general vertex lemma. -/
theorem newcomb_pure_scoreUpdate_zero' : scoreUpdate newcomb oneBox = 0 := by
  rw [oneBox_eq_single]; exact scoreUpdate_single_eq_zero newcomb 0

/-! ## The adversarial-offer variant has no interior ratifiable policy at all -/

/-- Expected return in policy coordinates, `Jpol Q π = Σ_a π_a Q(π,a)`; on the softmax image it is `J`. -/
noncomputable def Jpol (Q : (A → ℝ) → A → ℝ) (π : A → ℝ) : ℝ := ∑ a, π a * Q π a

theorem J_eq_Jpol (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) : J Q θ = Jpol Q (softmax θ) := rfl

/-- On the simplex, no policy that plays `decline` with positive probability is ratifiable for `AO`
(it would need `π_0, π_1 ≥ 2/3`). -/
theorem AO_not_ratifiable_of_decline_pos (π : Fin 3 → ℝ) (h1 : ∑ a, π a = 1) (h2 : 0 < π 2) : ¬ Ratifiable AO π := by
  intro h
  have ha := h 2 h2 0
  have hb := h 2 h2 1
  simp [AO] at ha hb
  rw [Fin.sum_univ_three] at h1
  linarith

/-- **No softmax policy is ratifiable for `AO`.** Hence *every* interior fixed point of *any* update rule
(REINFORCE, finite differences, ES at any `σ`, …) on this instance is non-ratifiable. -/
theorem AO_not_ratifiable_all (θ : Fin 3 → ℝ) : ¬ Ratifiable AO (softmax θ) :=
  AO_not_ratifiable_of_decline_pos _ (sum_softmax θ) (softmax_pos θ 2)

/-- The REINFORCE mean field has **no** zero anywhere on the softmax parametrisation of `AO`. -/
theorem AO_reinforce_ne_zero_all (θ : Fin 3 → ℝ) : reinforce AO θ ≠ 0 := fun h =>
  AO_not_ratifiable_all θ (ratifiable_of_reinforce_eq_zero AO θ h)

/-- The boundary point `(1/2, 1/2, 0)`: the only ratifiable policy of `AO` on the simplex. -/
noncomputable def AOratif : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]

/-- **The ratifiable policies of `AO` on the simplex are exactly `(1/2, 1/2, 0)`.** -/
theorem AO_ratifiable_iff (π : Fin 3 → ℝ) (h0 : ∀ a, 0 ≤ π a) (h1 : ∑ a, π a = 1) :
    Ratifiable AO π ↔ π = AOratif := by
  constructor
  · intro h
    have h2 : π 2 = 0 := by
      rcases (h0 2).lt_or_eq with hlt | heq
      · exact absurd h (AO_not_ratifiable_of_decline_pos π h1 hlt)
      · exact heq.symm
    rw [Fin.sum_univ_three, h2, add_zero] at h1
    have hp0 : 0 < π 0 := by
      rcases (h0 0).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hπ1 : π 1 = 1 := by linarith
        have := h 1 (by rw [hπ1]; norm_num) 0
        simp [AO, hπ1, ← heq] at this
        norm_num at this
    have hp1 : 0 < π 1 := by
      rcases (h0 1).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hπ0 : π 0 = 1 := by linarith
        have := h 0 (by rw [hπ0]; norm_num) 1
        simp [AO, hπ0, ← heq] at this
        norm_num at this
    have hA := h 0 hp0 1
    have hB := h 1 hp1 0
    simp [AO] at hA hB
    funext a
    fin_cases a <;> simp [AOratif] <;> linarith
  · rintro rfl
    intro a ha b
    fin_cases a <;> fin_cases b <;> simp [AO, AOratif] at ha ⊢ <;> norm_num

theorem AOratif_simplex : (∀ a, 0 ≤ AOratif a) ∧ ∑ a, AOratif a = 1 := by
  refine ⟨fun a => ?_, ?_⟩
  · fin_cases a <;> simp [AOratif]
  · simp [AOratif, Fin.sum_univ_three]; norm_num

/-- The value gap: the unique ratifiable policy earns `1/2`, the optimum earns `2/3`. -/
theorem AO_Jpol_ratif : Jpol AO AOratif = 1 / 2 := by
  simp [Jpol, AO, AOratif, Fin.sum_univ_three]; norm_num

theorem AO_value_gap : Jpol AO AOratif < J AO 0 := by
  rw [AO_Jpol_ratif, AO_J_zero]; norm_num


/-! ## General parametrised policies `π = f w` (LLM / LoRA setting)

Everything above is for the free-logit (tabular) softmax. Here `f : W → (A → ℝ)` is any policy family with
Jacobian `f'` at `w` (`HasFDerivAt f f' w`). The mean score-function update is the derivative of the
**frozen-world** objective `w' ↦ Σ_a f(w')_a Q(f(w), a)`; the true gradient adds the indirect term; and
"stationary" is equivalent only to *first-order* ratifiability relative to the family, which for the tabular
softmax (and only there, in general) is BLOS ratifiability. -/

section Parametrised

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Expected return of the parametrised policy, `Jp Q f w = Σ_a f(w)_a Q(f(w), a)`. -/
noncomputable def Jp (Q : (A → ℝ) → A → ℝ) (f : W → A → ℝ) (w : W) : ℝ := ∑ a, f w a * Q (f w) a

/-- **Frozen-world objective**: the world's response is frozen at the current policy `f w`; only the acting
policy `f w'` varies. REINFORCE's expected update is the derivative of this in `w'` at `w' = w`. -/
noncomputable def frozen (Q : (A → ℝ) → A → ℝ) (f : W → A → ℝ) (w w' : W) : ℝ := ∑ a, f w' a * Q (f w) a

/-- Direct term / mean score-function update for a parametrised policy: `Σ_a Q(π,a) · dπ_a`, as a covector. -/
noncomputable def directP (Q : (A → ℝ) → A → ℝ) (f : W → A → ℝ) (f' : W →L[ℝ] (A → ℝ)) (w : W) :
    W →L[ℝ] ℝ :=
  ∑ a, Q (f w) a • (proj a : (A → ℝ) →L[ℝ] ℝ).comp f'

/-- Indirect / interference term for a parametrised policy: `Σ_a π_a · (dQ(·,a) ∘ dπ)`. -/
noncomputable def indirectP (Q' : A → (A → ℝ) →L[ℝ] ℝ) (f : W → A → ℝ)
    (f' : W →L[ℝ] (A → ℝ)) (w : W) : W →L[ℝ] ℝ :=
  ∑ a, f w a • (Q' a).comp f'

theorem directP_apply (Q : (A → ℝ) → A → ℝ) (f : W → A → ℝ) (f' : W →L[ℝ] (A → ℝ)) (w v : W) :
    directP Q f f' w v = ∑ a, f' v a * Q (f w) a := by
  simp [directP, mul_comm]

/-- **The mean score-function update is the derivative of the frozen-world objective.** -/
theorem hasFDerivAt_frozen (Q : (A → ℝ) → A → ℝ) {f : W → A → ℝ} {f' : W →L[ℝ] (A → ℝ)} {w : W}
    (hf : HasFDerivAt f f' w) : HasFDerivAt (frozen Q f w) (directP Q f f' w) w := by
  have hterm : ∀ a ∈ (Finset.univ : Finset A),
      HasFDerivAt (fun w' => f w' a * Q (f w) a) (Q (f w) a • (proj a : (A → ℝ) →L[ℝ] ℝ).comp f') w := by
    intro a _
    have h : HasFDerivAt (fun w' => f w' a) ((proj a : (A → ℝ) →L[ℝ] ℝ).comp f') w :=
      hasFDerivAt_pi'.1 hf a
    exact h.mul_const _
  have h := HasFDerivAt.sum hterm
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w' => by simp [frozen, Finset.sum_apply])

/-- **(1) Decomposition for any parametrised policy.** `dJp = directP + indirectP`. -/
theorem hasFDerivAt_Jp (Q : (A → ℝ) → A → ℝ) (Q' : A → (A → ℝ) →L[ℝ] ℝ) {f : W → A → ℝ}
    {f' : W →L[ℝ] (A → ℝ)} {w : W} (hf : HasFDerivAt f f' w)
    (hQ : ∀ a, HasFDerivAt (fun π => Q π a) (Q' a) (f w)) :
    HasFDerivAt (Jp Q f) (directP Q f f' w + indirectP Q' f f' w) w := by
  have hterm : ∀ a ∈ (Finset.univ : Finset A),
      HasFDerivAt (fun w' => f w' a * Q (f w') a)
        (f w a • (Q' a).comp f' + Q (f w) a • (proj a : (A → ℝ) →L[ℝ] ℝ).comp f') w := by
    intro a _
    have h1 : HasFDerivAt (fun w' => f w' a) ((proj a : (A → ℝ) →L[ℝ] ℝ).comp f') w :=
      hasFDerivAt_pi'.1 hf a
    have h2 : HasFDerivAt (fun w' => Q (f w') a) ((Q' a).comp f') w := (hQ a).comp w hf
    exact h1.mul h2
  have h := HasFDerivAt.sum hterm
  have h2 : HasFDerivAt (Jp Q f) _ w :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w' => by simp [Jp, Finset.sum_apply])
  refine h2.congr_fderiv ?_
  rw [Finset.sum_add_distrib, add_comm]; rfl

/-- The REINFORCE form of `directP` under full support: `Σ_a π_a · ∂_v log π_a · Q(π,a)`. -/
theorem directP_eq_score (Q : (A → ℝ) → A → ℝ) {f : W → A → ℝ} {f' : W →L[ℝ] (A → ℝ)} {w : W}
    (hf : HasFDerivAt f f' w) (hpos : ∀ a, 0 < f w a) (v : W) :
    directP Q f f' w v = ∑ a, f w a * fderiv ℝ (fun w => Real.log (f w a)) w v * Q (f w) a := by
  rw [directP_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : HasFDerivAt (fun w' => f w' a) ((proj a : (A → ℝ) →L[ℝ] ℝ).comp f') w :=
    hasFDerivAt_pi'.1 hf a
  rw [(h.log (hpos a).ne').fderiv]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  have hne := (hpos a).ne'
  field_simp

/-- **First-order ratifiability** relative to the family `f`: no tangent direction of the family improves the
frozen-world payoff, i.e. `w` is a first-order stationary point of `w' ↦ Σ_a f(w')_a Q(f(w), a)`. Stated with
`HasFDerivAt … 0`, so it cannot hold by a junk `fderiv`. -/
def FirstOrderRatifiable (Q : (A → ℝ) → A → ℝ) (f : W → A → ℝ) (w : W) : Prop :=
  HasFDerivAt (frozen Q f w) (0 : W →L[ℝ] ℝ) w

/-- **(2′) Score-function stationary ⇔ first-order ratifiable**, for any differentiable policy family. -/
theorem directP_eq_zero_iff_firstOrderRatifiable (Q : (A → ℝ) → A → ℝ) {f : W → A → ℝ}
    {f' : W →L[ℝ] (A → ℝ)} {w : W} (hf : HasFDerivAt f f' w) :
    directP Q f f' w = 0 ↔ FirstOrderRatifiable Q f w := by
  constructor
  · intro h; unfold FirstOrderRatifiable; rw [← h]; exact hasFDerivAt_frozen Q hf
  · intro h; exact (hasFDerivAt_frozen Q hf).unique h

/-- Tangent-space form: stationary iff `Q(π,·)` is orthogonal to every tangent direction `f' v` of the family. -/
theorem directP_eq_zero_iff_orth (Q : (A → ℝ) → A → ℝ) (f : W → A → ℝ) (f' : W →L[ℝ] (A → ℝ)) (w : W) :
    directP Q f f' w = 0 ↔ ∀ v, ∑ a, f' v a * Q (f w) a = 0 := by
  constructor
  · intro h v; rw [← directP_apply, h]; rfl
  · intro h; ext v; rw [directP_apply, h v]; rfl

/-- First-order ratifiability is relative to the class: a *constant* family is first-order ratifiable at every
`w` for every `Q`, whatever the policy. -/
theorem firstOrderRatifiable_const (Q : (A → ℝ) → A → ℝ) (π₀ : A → ℝ) (w : W) :
    FirstOrderRatifiable Q (fun _ => π₀) w :=
  hasFDerivAt_const _ _

/-- In particular the (non-ratifiable) uniform policy of `AO` is first-order ratifiable in a one-point family. -/
theorem AO_firstOrderRatifiable_const_not_ratifiable :
    FirstOrderRatifiable AO (fun _ : ℝ => softmax (0 : Fin 3 → ℝ)) 0 ∧
      ¬ Ratifiable AO (softmax (0 : Fin 3 → ℝ)) :=
  ⟨firstOrderRatifiable_const _ _ _, AO_not_ratifiable⟩

end Parametrised

/-! ### The tabular softmax recovers the earlier results -/

theorem Jp_softmax (Q : (A → ℝ) → A → ℝ) : Jp Q softmax = J Q := rfl

/-- For the softmax family the direct covector evaluated on `e_k` is the REINFORCE mean update. -/
theorem directP_softmax (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) (k : A) :
    directP Q softmax (softmaxFDeriv θ) θ (Pi.single k 1) = reinforce Q θ k := by
  rw [directP_apply, reinforce_eq_direct]
  unfold direct
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [(hasFDerivAt_softmax_apply θ a).fderiv]
  rfl

theorem sum_softmaxDeriv (θ : A → ℝ) (v : A → ℝ) : ∑ a, softmaxDeriv θ a v = 0 := by
  simp only [softmaxDeriv, smul_apply, sub_apply, _root_.sum_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, sum_softmax, one_mul, sub_self]

theorem directP_softmax_eq_zero_iff (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) :
    directP Q softmax (softmaxFDeriv θ) θ = 0 ↔ reinforce Q θ = 0 := by
  constructor
  · intro h; funext k; rw [← directP_softmax, h]; rfl
  · intro h
    have hc := (reinforce_eq_zero_iff_const Q θ).1 h
    ext v
    rw [directP_apply, zero_apply]
    obtain ⟨a₀⟩ := (inferInstance : Nonempty A)
    calc ∑ a, softmaxFDeriv θ v a * Q (softmax θ) a = ∑ a, softmaxDeriv θ a v * Q (softmax θ) a₀ :=
          Finset.sum_congr rfl fun a _ => by rw [hc a a₀]; rfl
      _ = 0 := by rw [← Finset.sum_mul, sum_softmaxDeriv, zero_mul]

/-- **For the tabular softmax, first-order ratifiability is BLOS ratifiability.** In general it is weaker
(`firstOrderRatifiable_const`). -/
theorem firstOrderRatifiable_softmax_iff (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) :
    FirstOrderRatifiable Q softmax θ ↔ Ratifiable Q (softmax θ) := by
  rw [← directP_eq_zero_iff_firstOrderRatifiable Q (hasFDerivAt_softmax θ), directP_softmax_eq_zero_iff,
    reinforce_eq_zero_iff_ratifiable]


/-! ## Policy-level (whole-policy) randomisation: antithetic finite differences estimate the total gradient

A policy-level estimator perturbs the *parameters* and reads off the realised return of the perturbed policy with
the world responding to that perturbed policy. Its symmetric (antithetic) form along a finite design of
directions `ε i` is `Σ_i ((F(w + σε_i) − F(w − σε_i)) / 2σ) • ε_i`. We prove the deterministic identity: as
`σ → 0` this converges to `Σ_i dF(ε_i) • ε_i`, which for an isotropic design (`Σ_i ε_i ε_iᵀ = I`) is the
gradient of `F`; applied to `F = J` it is `reinforce + indirect`. Nothing is proved about finite `σ`
(smoothing bias) or about random designs beyond finite uniform ones (expectation = this sum up to the constant
`1/|ι|`, absorbed into the scale of `ε`). -/

section PolicyLevel

open Filter Topology

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Antithetic policy-level estimate of `∇F(w)` from the finite design `ε : ι → W` at scale `σ`. -/
noncomputable def antithetic {ι : Type*} [Fintype ι] (F : W → ℝ) (ε : ι → W) (w : W) (σ : ℝ) : W :=
  ∑ i, ((F (w + σ • ε i) - F (w - σ • ε i)) / (2 * σ)) • ε i

/-- The symmetric difference quotient of a differentiable `F` converges to the directional derivative. -/
theorem tendsto_symmDiff {F : W → ℝ} {F' : W →L[ℝ] ℝ} {w : W} (hF : HasFDerivAt F F' w) (v : W) :
    Tendsto (fun σ : ℝ => (F (w + σ • v) - F (w - σ • v)) / (2 * σ)) (𝓝[≠] 0) (𝓝 (F' v)) := by
  -- `g σ = F (w + σ • v)` has derivative `F' v` at `σ = 0`.
  have hpath : HasDerivAt (fun σ : ℝ => w + σ • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  have hF0 : HasFDerivAt F F' (w + (0 : ℝ) • v) := by simpa using hF
  have hg : HasDerivAt (fun σ : ℝ => F (w + σ • v)) (F' v) 0 := hF0.comp_hasDerivAt (0 : ℝ) hpath
  have h1 : Tendsto (fun t : ℝ => t⁻¹ • (F (w + t • v) - F (w + (0 : ℝ) • v))) (𝓝[≠] 0) (𝓝 (F' v)) := by
    have := hasDerivAt_iff_tendsto_slope_zero.1 hg
    simpa using this
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun t ht => neg_ne_zero.2 ht
  have h2 := h1.comp hneg
  have h3 := (h1.add h2).const_mul (1 / 2 : ℝ)
  have hlim : (1 / 2 : ℝ) * (F' v + F' v) = F' v := by ring
  rw [hlim] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Function.comp, zero_smul, add_zero, smul_eq_mul, neg_smul, ← sub_eq_add_neg]
  field_simp
  ring

/-- **Deterministic limit of the antithetic estimator:** `antithetic F ε w σ → Σ_i dF(ε_i) • ε_i` as `σ → 0`. -/
theorem tendsto_antithetic {ι : Type*} [Fintype ι] {F : W → ℝ} {F' : W →L[ℝ] ℝ} {w : W}
    (hF : HasFDerivAt F F' w) (ε : ι → W) :
    Tendsto (antithetic F ε w) (𝓝[≠] 0) (𝓝 (∑ i, F' (ε i) • ε i)) :=
  tendsto_finsetSum _ fun i _ => (tendsto_symmDiff hF (ε i)).smul_const (ε i)

end PolicyLevel

section PolicyLevelLogits

open Filter Topology

/-- An **isotropic** design on logit space: `Σ_i ε_i ε_iᵀ = I`, written row-wise. The coordinate design
`ε k = e_k` (central finite differences) is one (`isotropic_single`); a uniform random design with
`E[ε εᵀ] = I` is another, up to the scale `|ι|^{-1/2}`. -/
def Isotropic {ι : Type*} [Fintype ι] (ε : ι → A → ℝ) : Prop :=
  ∀ k, ∑ i, ε i k • ε i = Pi.single k 1

theorem isotropic_single : Isotropic (fun k : A => (Pi.single k 1 : A → ℝ)) := by
  intro k
  simp [Pi.single_apply]

/-- **Antithetic policy-level estimation recovers the full gradient** `k ↦ dF(e_k)` for an isotropic design. -/
theorem tendsto_antithetic_grad {ι : Type*} [Fintype ι] {F : (A → ℝ) → ℝ} {F' : (A → ℝ) →L[ℝ] ℝ} {θ : A → ℝ}
    (hF : HasFDerivAt F F' θ) {ε : ι → A → ℝ} (hε : Isotropic ε) :
    Tendsto (antithetic F ε θ) (𝓝[≠] 0) (𝓝 (fun k => F' (Pi.single k 1))) := by
  have h := tendsto_antithetic hF ε
  convert h using 2
  funext k
  rw [← hε k, map_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **(3′) The estimator half of the bridge, in the limit `σ → 0`:** on the softmax parametrisation, antithetic
policy-level estimation of `J` converges to `reinforce + indirect` — the total gradient, interference included. -/
theorem tendsto_antithetic_J {ι : Type*} [Fintype ι] (Q : (A → ℝ) → A → ℝ) (Q' : A → (A → ℝ) →L[ℝ] ℝ)
    (θ : A → ℝ) (hQ : ∀ a, HasFDerivAt (fun π => Q π a) (Q' a) (softmax θ)) {ε : ι → A → ℝ}
    (hε : Isotropic ε) :
    Tendsto (antithetic (J Q) ε θ) (𝓝[≠] 0) (𝓝 (fun k => reinforce Q θ k + indirect Q θ k)) := by
  have h := tendsto_antithetic_grad (hasFDerivAt_J Q Q' θ hQ) hε
  convert h using 2
  funext k
  rw [← fderiv_J_single Q Q' θ hQ k, (hasFDerivAt_J Q Q' θ hQ).fderiv]

/-- On `AO` at the optimum the antithetic estimator tends to `0`, while the REINFORCE mean field is
`(1/9, 1/9, −2/9)`: the two methods have different fixed points. -/
theorem AO_tendsto_antithetic_zero {ι : Type*} [Fintype ι] {ε : ι → Fin 3 → ℝ} (hε : Isotropic ε) :
    Tendsto (antithetic (J AO) ε 0) (𝓝[≠] 0) (𝓝 0) := by
  have h := tendsto_antithetic_grad AO_hasFDerivAt_J_zero hε
  exact h

end PolicyLevelLogits


/-! ## Boundary limits of REINFORCE trajectories (partial)

The separating instance's own REINFORCE flow leaves the interior (`AO_reinforce_ne_zero_all`), so the bridge
needs a statement about *limits* of interior trajectories. Here is the half we can prove: along a solution of
`θ̇ = reinforce Q θ` whose policy converges to `π*`, the payoff `Q(π*,·)` is constant on the support of `π*`.
The other half of ratifiability at the boundary — no *unplayed* action strictly beats the played ones — is
**not** proved; see `FIDELITY_ratifiable.md`. -/

section Trajectory

open Filter Topology

/-- A differentiable `f : ℝ → ℝ` that converges at `+∞` and whose derivative converges has derivative limit `0`. -/
theorem deriv_limit_eq_zero_of_tendsto {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) {L M : ℝ}
    (hL : Tendsto f atTop (𝓝 L)) (hM : Tendsto f' atTop (𝓝 M)) : M = 0 := by
  have hξ : ∀ n : ℕ, ∃ ξ ∈ Set.Ioo (n : ℝ) (n + 1), f' ξ = f (n + 1) - f n := by
    intro n
    have hcont : ContinuousOn f (Set.Icc (n : ℝ) (n + 1)) :=
      fun t _ => (hf t).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, h⟩ :=
      exists_hasDerivAt_eq_slope f f' (by linarith : (n : ℝ) < n + 1) hcont (fun t _ => hf t)
    exact ⟨ξ, hξ, by rw [h]; simp⟩
  choose ξ hξmem hξeq using hξ
  have hξtop : Tendsto ξ atTop atTop :=
    tendsto_atTop_mono (fun n => (hξmem n).1.le) tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => f' (ξ n)) atTop (𝓝 M) := hM.comp hξtop
  have h2 : Tendsto (fun n : ℕ => f ((n : ℝ) + 1) - f n) atTop (𝓝 (L - L)) := by
    have ha : Tendsto (fun n : ℕ => f ((n : ℝ) + 1)) atTop (𝓝 L) :=
      hL.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    exact ha.sub (hL.comp tendsto_natCast_atTop_atTop)
  rw [sub_self] at h2
  have : (fun n : ℕ => f' (ξ n)) = fun n : ℕ => f ((n : ℝ) + 1) - f n := funext hξeq
  rw [this] at h1
  exact tendsto_nhds_unique h1 h2

/-- `θ_a − θ_b = log π_a − log π_b`. -/
theorem sub_eq_log_softmax_sub (θ : A → ℝ) (a b : A) :
    θ a - θ b = Real.log (softmax θ a) - Real.log (softmax θ b) := by
  simp only [softmax, Real.log_div (Real.exp_pos _).ne' (Z_pos θ).ne', Real.log_exp]; ring

/-- The mean field is continuous in `π` wherever `Q` is. -/
theorem tendsto_scoreUpdate_of_tendsto (Q : (A → ℝ) → A → ℝ) {u : ℝ → A → ℝ} {π' : A → ℝ}
    (hu : Tendsto u atTop (𝓝 π')) (hQ : ∀ a, ContinuousAt (fun π => Q π a) π') (k : A) :
    Tendsto (fun t => scoreUpdate Q (u t) k) atTop (𝓝 (scoreUpdate Q π' k)) := by
  have hc : ∀ c, Tendsto (fun t => u t c) atTop (𝓝 (π' c)) := fun c => tendsto_pi_nhds.1 hu c
  have hQt : ∀ c, Tendsto (fun t => Q (u t) c) atTop (𝓝 (Q π' c)) := fun c => (hQ c).tendsto.comp hu
  have hJt : Tendsto (fun t => ∑ c, u t c * Q (u t) c) atTop (𝓝 (∑ c, π' c * Q π' c)) :=
    tendsto_finsetSum _ fun c _ => (hc c).mul (hQt c)
  exact (hc k).mul ((hQt k).sub hJt)

/-- **Limits of convergent interior REINFORCE trajectories have `Q` constant on their support.**
If `θ : ℝ → (A → ℝ)` solves `θ̇ = reinforce Q θ` for all `t`, `softmax (θ t) → π*` as `t → ∞`, and every
`Q(·,a)` is continuous at `π*`, then `Q(π*, a) = Jpol Q π*` for every `a` with `π*_a > 0`. This is the
"within-support" half of ratifiability at the boundary; the "no unplayed action does better" half is NOT
proved (see `FIDELITY_ratifiable.md`). -/
theorem limit_const_on_support (Q : (A → ℝ) → A → ℝ) (θ : ℝ → A → ℝ)
    (hθ : ∀ t k, HasDerivAt (fun t => θ t k) (reinforce Q (θ t) k) t)
    (π' : A → ℝ) (hlim : Tendsto (fun t => softmax (θ t)) atTop (𝓝 π'))
    (hQ : ∀ a, ContinuousAt (fun π => Q π a) π') :
    ∀ a, 0 < π' a → Q π' a = Jpol Q π' := by
  have hc : ∀ c, Tendsto (fun t => softmax (θ t) c) atTop (𝓝 (π' c)) := fun c => tendsto_pi_nhds.1 hlim c
  have hnn : ∀ c, 0 ≤ π' c := fun c => ge_of_tendsto' (hc c) fun t => softmax_nonneg _ _
  have hsum : ∑ c, π' c = 1 := by
    have h := tendsto_finsetSum (Finset.univ : Finset A) fun c _ => hc c
    have h' : Tendsto (fun t => ∑ c, softmax (θ t) c) atTop (𝓝 1) := by
      simp only [sum_softmax]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h h'
  have hsc : ∀ k, Tendsto (fun t => scoreUpdate Q (softmax (θ t)) k) atTop (𝓝 (scoreUpdate Q π' k)) :=
    fun k => tendsto_scoreUpdate_of_tendsto Q hlim hQ k
  -- Step 1: the mean field has equal components on the support of the limit.
  have hequal : ∀ a b, 0 < π' a → 0 < π' b → scoreUpdate Q π' a = scoreUpdate Q π' b := by
    intro a b ha hb
    have hf : ∀ t, HasDerivAt (fun t => θ t a - θ t b)
        (scoreUpdate Q (softmax (θ t)) a - scoreUpdate Q (softmax (θ t)) b) t := by
      intro t
      have := (hθ t a).sub (hθ t b)
      rwa [reinforce_eq_scoreUpdate] at this
    have hL : Tendsto (fun t => θ t a - θ t b) atTop (𝓝 (Real.log (π' a) - Real.log (π' b))) := by
      have ha' := ((Real.continuousAt_log ha.ne').tendsto.comp (hc a))
      have hb' := ((Real.continuousAt_log hb.ne').tendsto.comp (hc b))
      have := ha'.sub hb'
      refine this.congr fun t => ?_
      simp only [Function.comp]
      exact (sub_eq_log_softmax_sub (θ t) a b).symm
    have hM := (hsc a).sub (hsc b)
    have := deriv_limit_eq_zero_of_tendsto hf hL hM
    linarith
  -- Step 2: the components sum to zero and vanish off the support, so they vanish on it.
  have htotal : ∑ k, scoreUpdate Q π' k = 0 := by
    simp only [scoreUpdate, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hsum, one_mul, sub_self]
  intro a ha
  have hoff : ∀ k, scoreUpdate Q π' k = if 0 < π' k then scoreUpdate Q π' a else 0 := by
    intro k
    split_ifs with hk
    · exact hequal k a hk ha
    · have : π' k = 0 := le_antisymm (not_lt.1 hk) (hnn k)
      simp [scoreUpdate, this]
  rw [Finset.sum_congr rfl fun k _ => hoff k, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul] at htotal
  have hcard : (0 : ℝ) < ((Finset.univ.filter fun k => 0 < π' k).card : ℝ) := by
    have : a ∈ Finset.univ.filter fun k => 0 < π' k := Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩
    exact_mod_cast Finset.card_pos.2 ⟨a, this⟩
  have hz : scoreUpdate Q π' a = 0 := (mul_eq_zero.1 htotal).resolve_left hcard.ne'
  unfold scoreUpdate at hz
  have := (mul_eq_zero.1 hz).resolve_left ha.ne'
  unfold Jpol
  linarith

end Trajectory

end BoundaryTheorem.ScoreFunctionRatifiable
