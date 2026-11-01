import BoundaryTheorem.ScoreFunctionRatifiable

/-!
# Strongest true versions of "REINFORCE's fixed points are the ratifiable policies"

Setting as in `ScoreFunctionRatifiable`: finite actions `A`, payoff `Q : (A → ℝ) → A → ℝ` (the world responds to
the *policy*). Fidelity record: `FIDELITY_ratifiable_strong.md`.

* **T2** `scoreUpdate_eq_zero_iff_constOnSupp`: on the closed simplex the mean score-function update vanishes iff
  `Q(π,·)` is constant on `supp π` (vertices: `scoreUpdate_single_eq_zero'`).
* **T1** general differentiable families `f : W → (A → ℝ)`:
  `faceTangent_fderiv` (a simplex-valued family has `range f' ⊆ T_S`),
  `directP_eq_zero_iff_constOnSupp` (face version: `range f' ⊇ T_S` ⇒ stationary ⇔ `Q` constant on `S`),
  `directP_eq_zero_iff_ratifiable` / `firstOrderRatifiable_iff_ratifiable` (full support, `range f' ⊇ T`),
  `exists_bandit_stationary_not_ratifiable` / `exists_bandit_stationary_not_constOnSupp` (if `range f'` misses a
  tangent direction, some bandit makes `π` stationary but not ratifiable: full rank is exactly the condition).
* **T3a** replicator = natural-gradient REINFORCE: `fisher_natField`, `fisher_eq_reinforce_iff`,
  `hasDerivAt_softmax_natField`; folk theorem `replicator_limit_ratifiable`, `natural_limit_ratifiable`;
  interiority `replicator_pos`; stability `ratifiable_of_replicatorStable`.
* **T3b** plain (vanilla) mean REINFORCE on softmax logits: `reinforce_limit_ratifiable` — limits of trajectories
  are ratifiable, boundary included (via the conservation law `sum_reinforce`). Corollaries
  `newcomb_oneBox_not_limit`, `AO_reinforce_limit`.
* **T4** `vertex_asymptoticallyStable` (strictly ratifiable vertex ⇒ asymptotically stable for the replicator);
  `interior_strictlyRatifiable_not_asymptoticallyStable` (the interior version is false).

Trajectories are functions `ℝ → (A → ℝ)` with `HasDerivAt` at every `t ≥ T₀`; no ODE existence theory is used.
-/

open Finset Filter Topology
open ContinuousLinearMap (proj)

namespace BoundaryTheorem.RatifiableStrong

open BoundaryTheorem.ScoreFunctionRatifiable

set_option linter.unusedSectionVars false

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-! ## T2. The exact stationary set of the mean score-function update on the closed simplex -/

/-- **Support-restricted ratifiability**: `Q(π, ·)` is constant on the support of `π`. -/
def ConstOnSupp (Q : (A → ℝ) → A → ℝ) (π : A → ℝ) : Prop :=
  ∀ a b, 0 < π a → 0 < π b → Q π a = Q π b

/-- A probability vector has an action in its support. -/
theorem exists_pos_of_sum_eq_one {π : A → ℝ} (h0 : ∀ a, 0 ≤ π a) (h1 : ∑ a, π a = 1) :
    ∃ a, 0 < π a := by
  by_contra h
  push Not at h
  have : ∑ a, π a = 0 := Finset.sum_eq_zero fun a _ => le_antisymm (h a) (h0 a)
  linarith

/-- On the support, the expected payoff equals the common value of `Q`. -/
theorem sum_mul_eq_of_constOnSupp {Q : (A → ℝ) → A → ℝ} {π : A → ℝ} (h0 : ∀ a, 0 ≤ π a)
    (h1 : ∑ a, π a = 1) (h : ConstOnSupp Q π) {a₀ : A} (ha₀ : 0 < π a₀) :
    ∑ a, π a * Q π a = Q π a₀ := by
  calc ∑ a, π a * Q π a = ∑ a, π a * Q π a₀ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rcases (h0 a).lt_or_eq with ha | ha
        · rw [h a a₀ ha ha₀]
        · rw [← ha, zero_mul, zero_mul]
    _ = Q π a₀ := by rw [← Finset.sum_mul, h1, one_mul]

/-- **T2.** On the closed simplex, the mean score-function (REINFORCE) update vanishes **iff** `Q(π,·)` is
constant on the support of `π`. No full-support hypothesis. -/
theorem scoreUpdate_eq_zero_iff_constOnSupp (Q : (A → ℝ) → A → ℝ) (π : A → ℝ) (h0 : ∀ a, 0 ≤ π a)
    (h1 : ∑ a, π a = 1) : scoreUpdate Q π = 0 ↔ ConstOnSupp Q π := by
  constructor
  · intro h a b ha hb
    have hc : ∀ c, 0 < π c → Q π c = ∑ d, π d * Q π d := by
      intro c hc
      have := congrFun h c
      unfold scoreUpdate at this
      rw [Pi.zero_apply] at this
      have := (mul_eq_zero.1 this).resolve_left hc.ne'
      linarith
    rw [hc a ha, hc b hb]
  · intro h
    obtain ⟨a₀, ha₀⟩ := exists_pos_of_sum_eq_one h0 h1
    have hJ := sum_mul_eq_of_constOnSupp h0 h1 h ha₀
    funext k
    unfold scoreUpdate
    rw [hJ, Pi.zero_apply]
    rcases (h0 k).lt_or_eq with hk | hk
    · rw [h k a₀ hk ha₀, sub_self, mul_zero]
    · rw [← hk, zero_mul]

/-- Ratifiability = support-restricted ratifiability + "no unplayed action beats a played one". -/
theorem ratifiable_iff_constOnSupp_and (Q : (A → ℝ) → A → ℝ) (π : A → ℝ) (h0 : ∀ a, 0 ≤ π a) :
    Ratifiable Q π ↔ ConstOnSupp Q π ∧ ∀ a b, 0 < π a → π b = 0 → Q π b ≤ Q π a := by
  constructor
  · intro h
    exact ⟨fun a b ha hb => le_antisymm (h b hb a) (h a ha b), fun a b ha _ => h a ha b⟩
  · rintro ⟨hc, hu⟩ a ha b
    rcases (h0 b).lt_or_eq with hb | hb
    · exact (hc a b ha hb).ge
    · exact hu a b ha hb.symm

theorem constOnSupp_of_ratifiable {Q : (A → ℝ) → A → ℝ} {π : A → ℝ} (h : Ratifiable Q π) :
    ConstOnSupp Q π := fun a b ha hb => le_antisymm (h b hb a) (h a ha b)

/-- Corollary of T2: every vertex is stationary for every `Q` (re-derives `scoreUpdate_single_eq_zero`). -/
theorem scoreUpdate_single_eq_zero' (Q : (A → ℝ) → A → ℝ) (a : A) :
    scoreUpdate Q (Pi.single a 1) = 0 := by
  rw [scoreUpdate_eq_zero_iff_constOnSupp]
  · intro b c hb hc
    have hb' : b = a := by
      by_contra hne; simp [hne] at hb
    have hc' : c = a := by
      by_contra hne; simp [hne] at hc
    rw [hb', hc']
  · intro b; by_cases hb : b = a <;> simp [hb]
  · simp

/-- Corollary of T2: at full support, stationary ⇔ ratifiable (re-derives the tabular result). -/
theorem scoreUpdate_eq_zero_iff_ratifiable_of_pos (Q : (A → ℝ) → A → ℝ) (π : A → ℝ)
    (hpos : ∀ a, 0 < π a) (h1 : ∑ a, π a = 1) : scoreUpdate Q π = 0 ↔ Ratifiable Q π := by
  rw [scoreUpdate_eq_zero_iff_constOnSupp Q π (fun a => (hpos a).le) h1,
    ratifiable_iff_constOnSupp_and Q π (fun a => (hpos a).le)]
  constructor
  · intro h; exact ⟨h, fun a b _ hb => absurd hb (hpos b).ne'⟩
  · exact fun h => h.1

/-! ## T1. General differentiable policy families -/

section Family

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- `v` is a tangent direction of the face of the simplex spanned by `{a | 0 < π a}`:
`Σ_a v_a = 0` and `v_a = 0` off the support of `π`. For full-support `π` this is the tangent space
`T = {v | Σ_a v_a = 0}` of the simplex. -/
def FaceTangent (π v : A → ℝ) : Prop := (∑ a, v a = 0) ∧ ∀ a, ¬ 0 < π a → v a = 0

/-- If the family stays in the hyperplane `Σ = 1` near `w`, every direction it can move in sums to zero:
`range f' ⊆ T`. -/
theorem sum_fderiv_eq_zero {f : W → A → ℝ} {f' : W →L[ℝ] (A → ℝ)} {w : W} (hf : HasFDerivAt f f' w)
    (hsum : ∀ᶠ w' in 𝓝 w, ∑ a, f w' a = 1) (u : W) : ∑ a, f' u a = 0 := by
  have hS : HasFDerivAt (fun w' => ∑ a, f w' a)
      (∑ a, (proj a : (A → ℝ) →L[ℝ] ℝ).comp f') w := by
    have h := HasFDerivAt.sum (u := Finset.univ) (A := fun a w' => f w' a)
      (A' := fun a => (proj a : (A → ℝ) →L[ℝ] ℝ).comp f') (fun a _ => hasFDerivAt_pi'.1 hf a)
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun w' => by simp [Finset.sum_apply])
  have hc : HasFDerivAt (fun w' => ∑ a, f w' a) (0 : W →L[ℝ] ℝ) w :=
    (hasFDerivAt_const (1 : ℝ) w).congr_of_eventuallyEq hsum
  have := congrArg (fun L : W →L[ℝ] ℝ => L u) (hS.unique hc)
  simpa using this

/-- If the family is nonnegative near `w` and `f(w)_a = 0`, then it cannot move in direction `a` to first
order: `w` is a local minimum of `f(·)_a`, so `f'(u)_a = 0`. -/
theorem fderiv_apply_eq_zero_of_zero {f : W → A → ℝ} {f' : W →L[ℝ] (A → ℝ)} {w : W}
    (hf : HasFDerivAt f f' w) (hnn : ∀ᶠ w' in 𝓝 w, ∀ a, 0 ≤ f w' a) {a : A} (ha : f w a = 0)
    (u : W) : f' u a = 0 := by
  have hmin : IsLocalMin (fun w' => f w' a) w := by
    filter_upwards [hnn] with w' hw'
    rw [ha]; exact hw' a
  have := hmin.hasFDerivAt_eq_zero (hasFDerivAt_pi'.1 hf a)
  simpa using congrArg (fun L : W →L[ℝ] ℝ => L u) this

/-- **For a simplex-valued family, `range f' ⊆ T_S`** (the tangent space of the face of the current support). -/
theorem faceTangent_fderiv {f : W → A → ℝ} {f' : W →L[ℝ] (A → ℝ)} {w : W} (hf : HasFDerivAt f f' w)
    (hsimp : ∀ᶠ w' in 𝓝 w, (∀ a, 0 ≤ f w' a) ∧ ∑ a, f w' a = 1) (u : W) :
    FaceTangent (f w) (f' u) := by
  refine ⟨sum_fderiv_eq_zero hf (hsimp.mono fun _ h => h.2) u, fun a ha => ?_⟩
  have h0 : 0 ≤ f w a := (hsimp.self_of_nhds).1 a
  exact fderiv_apply_eq_zero_of_zero hf (hsimp.mono fun _ h => h.1) (le_antisymm (not_lt.1 ha) h0) u

/-- `Σ_c (e_a − e_b)_c q_c = q_a − q_b`. -/
theorem sum_single_sub_mul (q : A → ℝ) (a b : A) :
    ∑ c, (Pi.single a (1:ℝ) - Pi.single b (1:ℝ) : A → ℝ) c * q c = q a - q b := by
  simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply]

theorem faceTangent_single_sub {π : A → ℝ} {a b : A} (ha : 0 < π a) (hb : 0 < π b) :
    FaceTangent π ((Pi.single a 1 : A → ℝ) - Pi.single b 1) := by
  refine ⟨by simp [Finset.sum_sub_distrib], fun c hc => ?_⟩
  have hca : c ≠ a := fun h => hc (h ▸ ha)
  have hcb : c ≠ b := fun h => hc (h ▸ hb)
  simp [hca, hcb]

/-- **T1, face version.** Let `f : W → (A → ℝ)` be simplex-valued near `w` (so `range f' ⊆ T_S` automatically,
`faceTangent_fderiv`), differentiable at `w`, and suppose its derivative reaches every tangent direction of
the face of the support `S` of `π = f w` (`range f' ⊇ T_S`). Then the mean score-function update `directP`
vanishes iff `Q(π,·)` is constant on `S`. -/
theorem directP_eq_zero_iff_constOnSupp (Q : (A → ℝ) → A → ℝ) {f : W → A → ℝ}
    {f' : W →L[ℝ] (A → ℝ)} {w : W} (hf : HasFDerivAt f f' w)
    (hsimp : ∀ᶠ w' in 𝓝 w, (∀ a, 0 ≤ f w' a) ∧ ∑ a, f w' a = 1)
    (hrank : ∀ v, FaceTangent (f w) v → ∃ u, f' u = v) :
    directP Q f f' w = 0 ↔ ConstOnSupp Q (f w) := by
  rw [directP_eq_zero_iff_orth]
  constructor
  · intro h a b ha hb
    obtain ⟨u, hu⟩ := hrank _ (faceTangent_single_sub ha hb)
    have := h u
    rw [hu, sum_single_sub_mul] at this
    linarith
  · intro h u
    have h0 : ∀ a, 0 ≤ f w a := (hsimp.self_of_nhds).1
    obtain ⟨a₀, ha₀⟩ := exists_pos_of_sum_eq_one h0 (hsimp.self_of_nhds).2
    obtain ⟨hs, hoff⟩ := faceTangent_fderiv hf hsimp u
    calc ∑ a, f' u a * Q (f w) a = ∑ a, f' u a * Q (f w) a₀ := by
          refine Finset.sum_congr rfl fun a _ => ?_
          by_cases ha : 0 < f w a
          · rw [h a a₀ ha ha₀]
          · rw [hoff a ha, zero_mul, zero_mul]
      _ = 0 := by rw [← Finset.sum_mul, hs, zero_mul]

/-- **T1 (main).** For a policy family `f` that stays in the hyperplane `Σ = 1` near `w` (true of any family of
probability vectors), differentiable at `w`, with full-support `π = f w`, and whose derivative reaches the whole
tangent space `T = {v | Σ v = 0}` (full rank onto the simplex): the mean score-function (REINFORCE) update
vanishes **iff** `π` is ratifiable. -/
theorem directP_eq_zero_iff_ratifiable (Q : (A → ℝ) → A → ℝ) {f : W → A → ℝ}
    {f' : W →L[ℝ] (A → ℝ)} {w : W} (hf : HasFDerivAt f f' w) (hpos : ∀ a, 0 < f w a)
    (hsum : ∀ᶠ w' in 𝓝 w, ∑ a, f w' a = 1)
    (hrank : ∀ v : A → ℝ, ∑ a, v a = 0 → ∃ u, f' u = v) :
    directP Q f f' w = 0 ↔ Ratifiable Q (f w) := by
  rw [directP_eq_zero_iff_orth, ratifiable_iff_const_of_pos Q _ hpos]
  constructor
  · intro h a b
    obtain ⟨u, hu⟩ := hrank _ (faceTangent_single_sub (hpos a) (hpos b)).1
    have := h u
    rw [hu, sum_single_sub_mul] at this
    linarith
  · intro h u
    obtain ⟨a₀⟩ := (inferInstance : Nonempty A)
    calc ∑ a, f' u a * Q (f w) a = ∑ a, f' u a * Q (f w) a₀ :=
          Finset.sum_congr rfl fun a _ => by rw [h a a₀]
      _ = 0 := by rw [← Finset.sum_mul, sum_fderiv_eq_zero hf hsum u, zero_mul]

/-- T1 in the language of the earlier file: under the same hypotheses, first-order ratifiability relative to
the family coincides with (BLOS) ratifiability. -/
theorem firstOrderRatifiable_iff_ratifiable (Q : (A → ℝ) → A → ℝ) {f : W → A → ℝ}
    {f' : W →L[ℝ] (A → ℝ)} {w : W} (hf : HasFDerivAt f f' w) (hpos : ∀ a, 0 < f w a)
    (hsum : ∀ᶠ w' in 𝓝 w, ∑ a, f w' a = 1)
    (hrank : ∀ v : A → ℝ, ∑ a, v a = 0 → ∃ u, f' u = v) :
    FirstOrderRatifiable Q f w ↔ Ratifiable Q (f w) := by
  rw [← directP_eq_zero_iff_firstOrderRatifiable Q hf, directP_eq_zero_iff_ratifiable Q hf hpos hsum hrank]

/-- A linear functional on `A → ℝ` is a dot product with its values on the basis vectors. -/
theorem dual_apply_eq_sum (φ : Module.Dual ℝ (A → ℝ)) (x : A → ℝ) :
    φ x = ∑ a, x a * φ (Pi.single a 1) := by
  conv_lhs => rw [show x = ∑ a, x a • (Pi.single a 1 : A → ℝ) by
    funext c; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, map_smul]

/-- **T1, converse obstruction (face version).** If the derivative of the family misses some tangent direction
of the face of the support of `π = f w` (`range f' ⊉ T_S`), then there is a payoff — in fact a plain bandit
`Q(π, a) = q a` that ignores the policy — for which the mean score-function update vanishes at `w` but `Q(π,·)`
is **not** constant on the support, hence `π` is not ratifiable. -/
theorem exists_bandit_stationary_not_constOnSupp {f : W → A → ℝ} {f' : W →L[ℝ] (A → ℝ)} {w : W}
    (hrank : ¬ ∀ v, FaceTangent (f w) v → ∃ u, f' u = v) :
    ∃ q : A → ℝ, directP (fun _ => q) f f' w = 0 ∧ ¬ ConstOnSupp (fun _ => q) (f w) ∧
      ¬ Ratifiable (fun _ => q) (f w) := by
  push Not at hrank
  obtain ⟨v, hvT, hvR⟩ := hrank
  have hv : v ∉ LinearMap.range (f' : W →ₗ[ℝ] (A → ℝ)) := by
    rintro ⟨u, hu⟩; exact hvR u hu
  obtain ⟨φ, hφv, hφR⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hφ0 : ∀ u, φ (f' u) = 0 := by
    intro u
    have : φ (f' u) ∈ (LinearMap.range (f' : W →ₗ[ℝ] (A → ℝ))).map φ :=
      Submodule.mem_map_of_mem ⟨u, rfl⟩
    rw [hφR] at this; simpa using this
  set q : A → ℝ := fun a => φ (Pi.single a 1) with hq
  have hnc : ¬ ConstOnSupp (fun _ => q) (f w) := by
    intro hc
    apply hφv
    rw [dual_apply_eq_sum]
    by_cases hS : ∃ a₀, 0 < f w a₀
    · obtain ⟨a₀, ha₀⟩ := hS
      calc ∑ a, v a * φ (Pi.single a 1) = ∑ a, v a * q a₀ := by
            refine Finset.sum_congr rfl fun a _ => ?_
            by_cases ha : 0 < f w a
            · exact congrArg _ (hc a a₀ ha ha₀)
            · rw [hvT.2 a ha, zero_mul, zero_mul]
        _ = 0 := by rw [← Finset.sum_mul, hvT.1, zero_mul]
    · push Not at hS
      exact Finset.sum_eq_zero fun a _ => by rw [hvT.2 a (not_lt.2 (hS a)), zero_mul]
  refine ⟨q, ?_, hnc, fun h => hnc (constOnSupp_of_ratifiable h)⟩
  rw [directP_eq_zero_iff_orth]
  intro u
  rw [← hφ0 u, dual_apply_eq_sum]

/-- **T1, converse obstruction (full support).** At a full-support `π = f w`, if `range f' ⊉ T` there is a
bandit `q` for which `π` is score-function stationary but not ratifiable. So "range f' ⊇ T" is exactly the
right condition in T1. -/
theorem exists_bandit_stationary_not_ratifiable {f : W → A → ℝ} {f' : W →L[ℝ] (A → ℝ)} {w : W}
    (hpos : ∀ a, 0 < f w a) (hrank : ¬ ∀ v : A → ℝ, ∑ a, v a = 0 → ∃ u, f' u = v) :
    ∃ q : A → ℝ, directP (fun _ => q) f f' w = 0 ∧ ¬ Ratifiable (fun _ => q) (f w) := by
  have h' : ¬ ∀ v, FaceTangent (f w) v → ∃ u, f' u = v := by
    intro h; exact hrank fun v hv => h v ⟨hv, fun a ha => absurd (hpos a) ha⟩
  obtain ⟨q, h1, _, h3⟩ := exists_bandit_stationary_not_constOnSupp h'
  exact ⟨q, h1, h3⟩

end Family


/-! ## T3. Which fixed points can REINFORCE reach? Limits of interior trajectories

Trajectories are stated abstractly: a function of time with a derivative (`HasDerivAt`) satisfying the flow
equation for all `t ≥ T₀`. No existence or uniqueness theory is used or needed for these results. -/

section Dynamics

/-- Monotonicity from a nonnegative derivative on `[T, ∞)` (mean value theorem). -/
theorem le_of_hasDerivAt_nonneg {g g' : ℝ → ℝ} {T : ℝ} (hg : ∀ t, T ≤ t → HasDerivAt g (g' t) t)
    (h : ∀ t, T ≤ t → 0 ≤ g' t) : ∀ t, T ≤ t → g T ≤ g t := by
  intro t ht
  rcases ht.lt_or_eq with ht | ht
  · have hcont : ContinuousOn g (Set.Icc T t) :=
      fun s hs => (hg s hs.1).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hξeq⟩ :=
      exists_hasDerivAt_eq_slope g g' ht hcont (fun s hs => hg s hs.1.le)
    have h1 := h ξ hξ.1.le
    rw [hξeq] at h1
    have h2 : 0 < t - T := by linarith
    have := (div_nonneg_iff.1 h1)
    rcases this with ⟨h3, _⟩ | ⟨_, h4⟩
    · linarith
    · linarith
  · rw [ht]

/-- If `x' → D > 0` then `x → +∞`; so a function bounded above whose derivative converges has a nonpositive
derivative limit. -/
theorem deriv_limit_nonpos_of_bddAbove {x x' : ℝ → ℝ} {T₀ : ℝ}
    (hx : ∀ t, T₀ ≤ t → HasDerivAt x (x' t) t) {B : ℝ} (hB : ∀ᶠ t in atTop, x t ≤ B) {D : ℝ}
    (hD : Tendsto x' atTop (𝓝 D)) : D ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hev : ∀ᶠ t in atTop, D / 2 ≤ x' t :=
    hD.eventually (le_mem_nhds (by linarith))
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 hev
  set T := max T₀ T₁
  have hg : ∀ t, T ≤ t → HasDerivAt (fun s => x s - D / 2 * s) (x' t - D / 2 * 1) t :=
    fun t ht => (hx t (le_trans (le_max_left _ _) ht)).sub ((hasDerivAt_id t).const_mul _)
  have hmono := le_of_hasDerivAt_nonneg hg (fun t ht => by
    have := hT₁ t (le_trans (le_max_right _ _) ht); linarith)
  have htop : Tendsto x atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_left atTop (x T - D / 2 * T)
      (tendsto_id.const_mul_atTop (by linarith : (0 : ℝ) < D / 2)))
    filter_upwards [eventually_ge_atTop T] with t ht
    have := hmono t ht
    simp only [id] at this ⊢
    linarith
  obtain ⟨t, ht1, ht2⟩ := (hB.and (htop.eventually_gt_atTop B)).exists
  linarith

/-- The general "log-ratio" folk argument. Let `p a, p b : ℝ → ℝ` converge to `pa* > 0` and `pb*`, be
positive, and let `x = log p_b − log p_a` have derivative `x'` converging to `D`. Then `D ≤ 0`. -/
theorem logratio_deriv_limit_nonpos {pa pb x' : ℝ → ℝ} {pa' pb' : ℝ} (ha : Tendsto pa atTop (𝓝 pa'))
    (hb : Tendsto pb atTop (𝓝 pb')) (ha' : 0 < pa') {T₀ : ℝ} (hpos : ∀ t, T₀ ≤ t → 0 < pa t ∧ 0 < pb t)
    (hx : ∀ t, T₀ ≤ t → HasDerivAt (fun s => Real.log (pb s) - Real.log (pa s)) (x' t) t) {D : ℝ}
    (hD : Tendsto x' atTop (𝓝 D)) : D ≤ 0 := by
  refine deriv_limit_nonpos_of_bddAbove hx (B := Real.log (pb' + 1) - Real.log (pa' / 2)) ?_ hD
  filter_upwards [ha.eventually (lt_mem_nhds (half_lt_self ha')),
    hb.eventually (gt_mem_nhds (lt_add_one pb')), eventually_ge_atTop T₀] with t h1 h2 hT
  have h3 : Real.log (pb t) ≤ Real.log (pb' + 1) :=
    Real.log_le_log (hpos t hT).2 h2.le
  have h4 : Real.log (pa' / 2) ≤ Real.log (pa t) :=
    Real.log_le_log (by linarith) h1.le
  linarith

/-- Expected payoff along a convergent path converges (continuity of `Q` at the limit). -/
theorem tendsto_Jpol {Q : (A → ℝ) → A → ℝ} {u : ℝ → A → ℝ} {π' : A → ℝ}
    (hu : Tendsto u atTop (𝓝 π')) (hQ : ∀ a, ContinuousAt (fun π => Q π a) π') :
    Tendsto (fun t => Jpol Q (u t)) atTop (𝓝 (Jpol Q π')) :=
  tendsto_finsetSum _ fun c _ => (tendsto_pi_nhds.1 hu c).mul ((hQ c).tendsto.comp hu)

theorem tendsto_Q {Q : (A → ℝ) → A → ℝ} {u : ℝ → A → ℝ} {π' : A → ℝ}
    (hu : Tendsto u atTop (𝓝 π')) (hQ : ∀ a, ContinuousAt (fun π => Q π a) π') (a : A) :
    Tendsto (fun t => Q (u t) a) atTop (𝓝 (Q π' a)) := (hQ a).tendsto.comp hu

/-- A limit of probability vectors is a probability vector. -/
theorem simplex_of_tendsto {u : ℝ → A → ℝ} {π' : A → ℝ} (hu : Tendsto u atTop (𝓝 π'))
    (h0 : ∀ t a, 0 ≤ u t a) (h1 : ∀ t, ∑ a, u t a = 1) : (∀ a, 0 ≤ π' a) ∧ ∑ a, π' a = 1 := by
  have hc : ∀ c, Tendsto (fun t => u t c) atTop (𝓝 (π' c)) := fun c => tendsto_pi_nhds.1 hu c
  refine ⟨fun c => ge_of_tendsto' (hc c) fun t => h0 t c, ?_⟩
  have h := tendsto_finsetSum (Finset.univ : Finset A) fun c _ => hc c
  have h' : Tendsto (fun t => ∑ c, u t c) atTop (𝓝 1) := by simp only [h1]; exact tendsto_const_nhds
  exact tendsto_nhds_unique h h'

/-! ### T3a. The replicator flow = natural-gradient REINFORCE -/

/-- **T3a (folk theorem, π-space).** Let `π : ℝ → (A → ℝ)` solve the replicator equation
`π̇_a = π_a (Q(π,a) − Σ_c π_c Q(π,c))` (this is `scoreUpdate`) for all `t ≥ T₀`, stay interior (`π t a > 0`),
and converge to `π*`, with each `Q(·,a)` continuous at `π*`. Then `π*` is **ratifiable**. -/
theorem replicator_limit_ratifiable (Q : (A → ℝ) → A → ℝ) (π : ℝ → A → ℝ) {T₀ : ℝ}
    (hπ : ∀ t, T₀ ≤ t → ∀ a, HasDerivAt (fun s => π s a) (scoreUpdate Q (π t) a) t)
    (hpos : ∀ t, T₀ ≤ t → ∀ a, 0 < π t a) (π' : A → ℝ) (hlim : Tendsto π atTop (𝓝 π'))
    (hQ : ∀ a, ContinuousAt (fun p => Q p a) π') : Ratifiable Q π' := by
  intro a ha b
  have hc : ∀ c, Tendsto (fun t => π t c) atTop (𝓝 (π' c)) := fun c => tendsto_pi_nhds.1 hlim c
  have hlog : ∀ c t, T₀ ≤ t → HasDerivAt (fun s => Real.log (π s c))
      (Q (π t) c - Jpol Q (π t)) t := by
    intro c t ht
    have := (hπ t ht c).log (hpos t ht c).ne'
    convert this using 1
    unfold scoreUpdate Jpol
    field_simp [(hpos t ht c).ne']
  have hD : Tendsto (fun t => (Q (π t) b - Jpol Q (π t)) - (Q (π t) a - Jpol Q (π t))) atTop
      (𝓝 ((Q π' b - Jpol Q π') - (Q π' a - Jpol Q π'))) :=
    ((tendsto_Q hlim hQ b).sub (tendsto_Jpol hlim hQ)).sub ((tendsto_Q hlim hQ a).sub (tendsto_Jpol hlim hQ))
  have := logratio_deriv_limit_nonpos (hc a) (hc b) ha (fun t ht => ⟨hpos t ht a, hpos t ht b⟩)
    (fun t ht => (hlog b t ht).sub (hlog a t ht)) hD
  linarith

/-- The **natural-gradient REINFORCE field** in logit coordinates: `θ̇_k = Q(π_θ, k) − J(θ)`. -/
noncomputable def natField (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) (k : A) : ℝ := Q (softmax θ) k - J Q θ

/-- The **Fisher information** of the softmax family, `F_{jk} = Σ_a π_a ∂_j log π_a ∂_k log π_a`, applied to `x`. -/
noncomputable def fisher (θ x : A → ℝ) (j : A) : ℝ :=
  ∑ a, softmax θ a * score θ a j * ∑ k, score θ a k * x k

/-- Closed form: `(F x)_j = π_j (x_j − Σ_k π_k x_k)`. -/
theorem fisher_eq (θ x : A → ℝ) (j : A) :
    fisher θ x j = softmax θ j * (x j - ∑ k, softmax θ k * x k) := by
  set xb := ∑ k, softmax θ k * x k with hxb
  have hs : ∀ a, ∑ k, score θ a k * x k = x a - xb := by
    intro a
    simp [score, sub_mul, Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_eq, hxb]
  have h2 : ∑ a, softmax θ a * (x a - xb) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, sum_softmax, one_mul, hxb, sub_self]
  simp only [fisher, hs]
  calc ∑ a, softmax θ a * score θ a j * (x a - xb)
      = ∑ a, ((if a = j then softmax θ a * (x a - xb) else 0) - softmax θ j * (softmax θ a * (x a - xb))) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [score]; split_ifs <;> ring
    _ = softmax θ j * (x j - xb) := by
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', ← Finset.mul_sum, h2]; simp

/-- **Natural gradient = `natField`.** `F · natField = reinforce`: the natural-gradient direction (Fisher⁻¹ times the
vanilla mean REINFORCE update) is `natField`, and it is unique up to adding a constant vector, which does not
change the policy (`fisher_eq_zero_iff`, `softmax_add_const`). -/
theorem fisher_natField (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) :
    fisher θ (natField Q θ) = reinforce Q θ := by
  funext j
  rw [fisher_eq, reinforce_eq]
  have : ∑ k, softmax θ k * natField Q θ k = 0 := by
    simp only [natField, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, sum_softmax, one_mul]; unfold J; ring
  rw [this, sub_zero]; rfl

theorem fisher_eq_zero_iff (θ x : A → ℝ) : fisher θ x = 0 ↔ ∃ c, ∀ k, x k = c := by
  constructor
  · intro h
    refine ⟨∑ k, softmax θ k * x k, fun j => ?_⟩
    have := congrFun h j
    rw [fisher_eq, Pi.zero_apply] at this
    have := (mul_eq_zero.1 this).resolve_left (softmax_pos θ j).ne'
    linarith
  · rintro ⟨c, hc⟩
    funext j
    rw [fisher_eq, Pi.zero_apply, hc j]
    simp only [hc, ← Finset.sum_mul, sum_softmax, one_mul, sub_self, mul_zero]

theorem fisher_linear (θ x y : A → ℝ) : fisher θ (x - y) = fisher θ x - fisher θ y := by
  funext j
  simp only [fisher_eq, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Every solution `x` of the natural-gradient equation `F x = reinforce` is `natField + c·𝟙`. -/
theorem fisher_eq_reinforce_iff (Q : (A → ℝ) → A → ℝ) (θ x : A → ℝ) :
    fisher θ x = reinforce Q θ ↔ ∃ c, ∀ k, x k = natField Q θ k + c := by
  rw [← fisher_natField, ← sub_eq_zero, ← fisher_linear, fisher_eq_zero_iff]
  simp only [Pi.sub_apply, sub_eq_iff_eq_add']

theorem softmax_add_const (θ : A → ℝ) (c : ℝ) : softmax (fun k => θ k + c) = softmax θ := by
  funext a
  simp only [softmax, Z, Real.exp_add, ← Finset.sum_mul]
  field_simp

/-- **The natural-gradient logit flow induces the replicator flow on policies.** If `θ̇ = natField Q θ` then
`π = softmax θ` satisfies `π̇_a = π_a (Q(π,a) − J)`. -/
theorem hasDerivAt_softmax_natField (Q : (A → ℝ) → A → ℝ) (θ : ℝ → A → ℝ) (t : ℝ)
    (hθ : ∀ k, HasDerivAt (fun s => θ s k) (natField Q (θ t) k) t) (a : A) :
    HasDerivAt (fun s => softmax (θ s) a) (scoreUpdate Q (softmax (θ t)) a) t := by
  have hθ' : HasDerivAt θ (natField Q (θ t)) t := hasDerivAt_pi.2 hθ
  have h := (hasFDerivAt_softmax_apply (θ t) a).comp_hasDerivAt t hθ'
  refine h.congr_deriv ?_
  simp only [softmaxDeriv, smul_apply, sub_apply,
    _root_.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  have : ∑ b, softmax (θ t) b * natField Q (θ t) b = 0 := by
    simp only [natField, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, sum_softmax, one_mul]; unfold J; ring
  rw [this, sub_zero]
  unfold scoreUpdate natField J
  rfl

/-- **T3a (folk theorem, natural-gradient REINFORCE).** If `θ̇ = natField Q θ` for `t ≥ T₀` and
`softmax (θ t) → π*` with `Q(·,a)` continuous at `π*`, then `π*` is ratifiable. (Interiority is automatic.) -/
theorem natural_limit_ratifiable (Q : (A → ℝ) → A → ℝ) (θ : ℝ → A → ℝ) {T₀ : ℝ}
    (hθ : ∀ t, T₀ ≤ t → ∀ k, HasDerivAt (fun s => θ s k) (natField Q (θ t) k) t)
    (π' : A → ℝ) (hlim : Tendsto (fun t => softmax (θ t)) atTop (𝓝 π'))
    (hQ : ∀ a, ContinuousAt (fun p => Q p a) π') : Ratifiable Q π' :=
  replicator_limit_ratifiable Q (fun t => softmax (θ t))
    (fun t ht a => hasDerivAt_softmax_natField Q θ t (hθ t ht) a) (fun _ _ _ => softmax_pos _ _) π' hlim hQ

/-! ### T3b. Plain (vanilla) mean REINFORCE on softmax logits: the boundary half holds too -/

/-- Antitonicity from a nonpositive derivative on `[T, ∞)`. -/
theorem le_of_hasDerivAt_nonpos {g g' : ℝ → ℝ} {T : ℝ} (hg : ∀ t, T ≤ t → HasDerivAt g (g' t) t)
    (h : ∀ t, T ≤ t → g' t ≤ 0) : ∀ t, T ≤ t → g t ≤ g T := by
  intro t ht
  have := le_of_hasDerivAt_nonneg (g := fun s => -g s) (g' := fun s => -g' s)
    (fun s hs => (hg s hs).neg) (fun s hs => by linarith [h s hs]) t ht
  linarith

/-- **Conservation law of the vanilla flow**: `Σ_k θ̇_k = Σ_k π_k (Q_k − J) = 0`. -/
theorem sum_reinforce (Q : (A → ℝ) → A → ℝ) (θ : A → ℝ) : ∑ k, reinforce Q θ k = 0 := by
  simp only [reinforce_eq, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, sum_softmax, one_mul]; unfold J; ring

/-- `e^{−θ_x} π_x = 1/Z`, the same for every action. -/
theorem exp_neg_mul_softmax (θ : A → ℝ) (x : A) : Real.exp (-θ x) * softmax θ x = (Z θ)⁻¹ := by
  unfold softmax
  rw [Real.exp_neg]
  have := (Z_pos θ).ne'
  have := Real.exp_pos (θ x)
  field_simp

theorem softmax_eq_mul_exp (θ : A → ℝ) (a b : A) :
    softmax θ b = softmax θ a * Real.exp (θ b - θ a) := by
  unfold softmax
  rw [Real.exp_sub]
  have := (Z_pos θ).ne'
  have := Real.exp_pos (θ a)
  field_simp

/-- Along the vanilla flow, `d/dt e^{−θ_x} = −(Q(π,x) − J)/Z`. -/
theorem hasDerivAt_exp_neg_theta (Q : (A → ℝ) → A → ℝ) {θ : ℝ → A → ℝ} {t : ℝ} {x : A}
    (h : HasDerivAt (fun s => θ s x) (reinforce Q (θ t) x) t) :
    HasDerivAt (fun s => Real.exp (-θ s x))
      (-((Z (θ t))⁻¹ * (Q (softmax (θ t)) x - J Q (θ t)))) t := by
  have := h.neg.exp
  refine this.congr_deriv ?_
  rw [reinforce_eq, ← exp_neg_mul_softmax]
  simp only [Pi.neg_apply]
  ring

theorem tendsto_reinforce_of_tendsto {Q : (A → ℝ) → A → ℝ} {θ : ℝ → A → ℝ} {π' : A → ℝ}
    (hlim : Tendsto (fun t => softmax (θ t)) atTop (𝓝 π')) (hQ : ∀ a, ContinuousAt (fun p => Q p a) π')
    (k : A) : Tendsto (fun t => reinforce Q (θ t) k) atTop (𝓝 (π' k * (Q π' k - Jpol Q π'))) := by
  simp only [reinforce_eq, J_eq_Jpol]
  exact (tendsto_pi_nhds.1 hlim k).mul ((tendsto_Q hlim hQ k).sub (tendsto_Jpol hlim hQ))

/-- Within-support half (re-proved for trajectories defined only on `[T₀, ∞)`). -/
theorem reinforce_limit_const_on_support (Q : (A → ℝ) → A → ℝ) (θ : ℝ → A → ℝ) {T₀ : ℝ}
    (hθ : ∀ t, T₀ ≤ t → ∀ k, HasDerivAt (fun s => θ s k) (reinforce Q (θ t) k) t)
    (π' : A → ℝ) (hlim : Tendsto (fun t => softmax (θ t)) atTop (𝓝 π'))
    (hQ : ∀ a, ContinuousAt (fun p => Q p a) π') : ∀ a, 0 < π' a → Q π' a = Jpol Q π' := by
  have hc : ∀ c, Tendsto (fun t => softmax (θ t) c) atTop (𝓝 (π' c)) := fun c => tendsto_pi_nhds.1 hlim c
  obtain ⟨hnn, hsum⟩ := simplex_of_tendsto hlim (fun t a => softmax_nonneg _ _) (fun t => sum_softmax _)
  set g : A → ℝ := fun k => π' k * (Q π' k - Jpol Q π') with hg
  have hle : ∀ a b, 0 < π' a → 0 < π' b → g b - g a ≤ 0 := by
    intro a b ha hb
    refine logratio_deriv_limit_nonpos (hc a) (hc b) ha (T₀ := T₀)
      (fun t _ => ⟨softmax_pos _ _, softmax_pos _ _⟩)
      (x' := fun t => reinforce Q (θ t) b - reinforce Q (θ t) a) ?_
      ((tendsto_reinforce_of_tendsto hlim hQ b).sub (tendsto_reinforce_of_tendsto hlim hQ a))
    intro t ht
    refine ((hθ t ht b).sub (hθ t ht a)).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [Pi.sub_apply]
    have := sub_eq_log_softmax_sub (θ s) b a
    linarith
  have hequal : ∀ a b, 0 < π' a → 0 < π' b → g a = g b := fun a b ha hb =>
    le_antisymm (by linarith [hle b a hb ha]) (by linarith [hle a b ha hb])
  have htotal : ∑ k, g k = 0 := by
    simp only [hg, Jpol, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hsum, one_mul, sub_self]
  intro a ha
  have hoff : ∀ k, g k = if 0 < π' k then g a else 0 := by
    intro k
    split_ifs with hk
    · exact hequal k a hk ha
    · have : π' k = 0 := le_antisymm (not_lt.1 hk) (hnn k)
      simp [hg, this]
  rw [Finset.sum_congr rfl fun k _ => hoff k, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul] at htotal
  have hcard : (0 : ℝ) < ((Finset.univ.filter fun k => 0 < π' k).card : ℝ) := by
    have : a ∈ Finset.univ.filter fun k => 0 < π' k := Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩
    exact_mod_cast Finset.card_pos.2 ⟨a, this⟩
  have hz : g a = 0 := (mul_eq_zero.1 htotal).resolve_left hcard.ne'
  have := (mul_eq_zero.1 hz).resolve_left ha.ne'
  linarith

/-- **T3b (boundary folk theorem for plain mean REINFORCE).** Let `θ : ℝ → (A → ℝ)` solve the vanilla
softmax-logit REINFORCE flow `θ̇_k = π_k (Q(π,k) − J)` (`reinforce`) for all `t ≥ T₀`, and suppose the policy
`softmax (θ t)` converges to `π*` (possibly on the boundary of the simplex), with every `Q(·,a)` continuous at
`π*`. Then `π*` is **ratifiable**: no action — played or unplayed — does strictly better against `π*` than a
played one. So plain REINFORCE cannot converge to a non-ratifiable boundary point either.

Proof idea: if an unplayed `b` had `Q(π*,b) > J(π*)`, then `θ_b` is eventually nondecreasing and
`d/dt e^{−θ_b} ≤ −β/Z`; for every action `u`, `d/dt e^{−θ_u} ≤ Γ/Z`; so `e^{−θ_u} + (Γ/β) e^{−θ_b}` is
nonincreasing and every logit is bounded below. The conservation law `Σ_k θ_k = const` then bounds the support
logits above, so `π_b = π_a e^{θ_b − θ_a}` stays bounded away from `0`: contradiction. -/
theorem reinforce_limit_ratifiable (Q : (A → ℝ) → A → ℝ) (θ : ℝ → A → ℝ) {T₀ : ℝ}
    (hθ : ∀ t, T₀ ≤ t → ∀ k, HasDerivAt (fun s => θ s k) (reinforce Q (θ t) k) t)
    (π' : A → ℝ) (hlim : Tendsto (fun t => softmax (θ t)) atTop (𝓝 π'))
    (hQ : ∀ a, ContinuousAt (fun p => Q p a) π') : Ratifiable Q π' := by
  have hc : ∀ c, Tendsto (fun t => softmax (θ t) c) atTop (𝓝 (π' c)) := fun c => tendsto_pi_nhds.1 hlim c
  obtain ⟨hnn, hsum⟩ := simplex_of_tendsto hlim (fun t a => softmax_nonneg _ _) (fun t => sum_softmax _)
  have hsupp := reinforce_limit_const_on_support Q θ hθ π' hlim hQ
  set dstar : A → ℝ := fun k => Q π' k - Jpol Q π' with hdstar
  set d : ℝ → A → ℝ := fun t k => Q (softmax (θ t)) k - J Q (θ t) with hd
  have hdlim : ∀ k, Tendsto (fun t => d t k) atTop (𝓝 (dstar k)) := fun k => by
    simp only [hd, hdstar, J_eq_Jpol]; exact (tendsto_Q hlim hQ k).sub (tendsto_Jpol hlim hQ)
  -- It suffices to show `dstar b ≤ 0` for every `b`.
  suffices hmain : ∀ b, dstar b ≤ 0 by
    intro a ha b
    have := hmain b
    have := hsupp a ha
    simp only [hdstar] at *
    linarith
  intro b
  by_contra hbpos
  push Not at hbpos
  have hb0 : π' b = 0 := by
    rcases (hnn b).lt_or_eq with h | h
    · have := hsupp b h; simp only [hdstar] at hbpos; linarith
    · exact h.symm
  obtain ⟨a, ha⟩ := exists_pos_of_sum_eq_one hnn hsum
  set β := dstar b / 2 with hβ
  have hβpos : 0 < β := by rw [hβ]; linarith
  set Γ : A → ℝ := fun u => |dstar u| + 1 with hΓ
  have hΓnn : ∀ u, 0 ≤ Γ u := fun u => by simp only [hΓ]; positivity
  -- Eventually: `d_b ≥ β`, `d_u ≥ −Γ_u`, `π_k ≥ π*_k / 2` on the support.
  have ev1 : ∀ᶠ t in atTop, β ≤ d t b := (hdlim b).eventually (le_mem_nhds (by rw [hβ]; linarith))
  have ev2 : ∀ᶠ t in atTop, ∀ u, -Γ u ≤ d t u := eventually_all.2 fun u =>
    (hdlim u).eventually (le_mem_nhds (by simp only [hΓ]; linarith [neg_abs_le (dstar u)]))
  have ev3 : ∀ᶠ t in atTop, ∀ k, 0 < π' k → π' k / 2 ≤ softmax (θ t) k := eventually_all.2 fun k => by
    by_cases hk : 0 < π' k
    · exact ((hc k).eventually (le_mem_nhds (half_lt_self hk))).mono fun t ht _ => ht
    · exact Eventually.of_forall fun t h => absurd h hk
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (ev1.and (ev2.and ev3))
  set T := max T₀ T₁ with hT
  have hTT₀ : ∀ t, T ≤ t → T₀ ≤ t := fun t ht => le_trans (le_max_left _ _) ht
  have hTT₁ : ∀ t, T ≤ t → T₁ ≤ t := fun t ht => le_trans (le_max_right _ _) ht
  -- (1) `θ_b` is nondecreasing on `[T, ∞)`.
  have hθb : ∀ t, T ≤ t → θ T b ≤ θ t b := by
    refine le_of_hasDerivAt_nonneg (fun t ht => hθ t (hTT₀ t ht) b) (fun t ht => ?_)
    rw [reinforce_eq]
    exact mul_nonneg (softmax_nonneg _ _) (le_trans hβpos.le (hT₁ t (hTT₁ t ht)).1)
  -- (2) every logit is bounded below on `[T, ∞)`.
  set G : A → ℝ → ℝ := fun u s => Real.exp (-θ s u) + Γ u / β * Real.exp (-θ s b) with hG
  have hGanti : ∀ u t, T ≤ t → G u t ≤ G u T := by
    intro u
    refine le_of_hasDerivAt_nonpos (g' := fun t => -((Z (θ t))⁻¹ * d t u) +
        Γ u / β * -((Z (θ t))⁻¹ * d t b)) (fun t ht => ?_) (fun t ht => ?_)
    · exact (hasDerivAt_exp_neg_theta Q (hθ t (hTT₀ t ht) u)).add
        ((hasDerivAt_exp_neg_theta Q (hθ t (hTT₀ t ht) b)).const_mul _)
    · obtain ⟨h1, h2, _⟩ := hT₁ t (hTT₁ t ht)
      have hZ : 0 < (Z (θ t))⁻¹ := inv_pos.2 (Z_pos _)
      have h3 : Γ u ≤ Γ u / β * d t b := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hβpos]
        exact mul_le_mul_of_nonneg_left h1 (hΓnn u)
      have h4 : 0 ≤ d t u + Γ u / β * d t b := by linarith [h2 u]
      have : 0 ≤ (Z (θ t))⁻¹ * (d t u + Γ u / β * d t b) := mul_nonneg hZ.le h4
      nlinarith
  have hGpos : ∀ u, 0 < G u T := fun u => by
    simp only [hG]; have := hΓnn u; positivity
  have hlow : ∀ u t, T ≤ t → -Real.log (G u T) ≤ θ t u := by
    intro u t ht
    have h1 : Real.exp (-θ t u) ≤ G u T := by
      have := hGanti u t ht
      have : 0 ≤ Γ u / β * Real.exp (-θ t b) := by have := hΓnn u; positivity
      simp only [hG] at *
      linarith
    have := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at this
    linarith
  -- (3) conservation: `Σ_k θ_k` is constant.
  have hcons : ∀ t, T ≤ t → ∑ k, θ t k = ∑ k, θ T k := by
    have hder : ∀ t, T ≤ t → HasDerivAt (fun s => ∑ k, θ s k) (∑ k, reinforce Q (θ t) k) t := by
      intro t ht
      have h := HasDerivAt.sum (u := Finset.univ) (A := fun k s => θ s k) fun k _ => hθ t (hTT₀ t ht) k
      convert h using 1
      funext s; simp [Finset.sum_apply]
    intro t ht
    exact le_antisymm (le_of_hasDerivAt_nonpos hder (fun s hs => (sum_reinforce Q _).le) t ht)
      (le_of_hasDerivAt_nonneg hder (fun s hs => (sum_reinforce Q _).ge) t ht)
  -- (4) the support logits stay bounded above (relative to the conserved sum).
  set B : A → ℝ := fun k => if 0 < π' k then Real.log (π' k / 2) else -Real.log (G k T) with hB
  have hθa : ∀ t, T ≤ t → θ t a ≤ max 0 (∑ k, θ T k - ∑ k, B k) := by
    intro t ht
    have hk : ∀ k, (if 0 < π' k then (1 : ℝ) else 0) * θ t a + B k ≤ θ t k := by
      intro k
      simp only [hB]
      split_ifs with hk
      · have h1 := (hT₁ t (hTT₁ t ht)).2.2 k hk
        have h2 := sub_eq_log_softmax_sub (θ t) k a
        have h3 : Real.log (π' k / 2) ≤ Real.log (softmax (θ t) k) :=
          Real.log_le_log (by linarith) h1
        have h4 : Real.log (softmax (θ t) a) ≤ 0 := by
          apply Real.log_nonpos (softmax_nonneg _ _)
          have := sum_softmax (θ t)
          calc softmax (θ t) a ≤ ∑ c, softmax (θ t) c :=
                Finset.single_le_sum (f := fun c => softmax (θ t) c) (fun c _ => softmax_nonneg _ _)
                  (Finset.mem_univ a)
            _ = 1 := this
        linarith
      · linarith [hlow k t ht]
    have hsumk := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hk k
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hcons t ht] at hsumk
    have hN : 1 ≤ ∑ k, (if 0 < π' k then (1 : ℝ) else 0) := by
      calc (1 : ℝ) = if 0 < π' a then (1 : ℝ) else 0 := by simp [ha]
        _ ≤ ∑ k, (if 0 < π' k then (1 : ℝ) else 0) :=
          Finset.single_le_sum (f := fun k => if 0 < π' k then (1 : ℝ) else 0)
            (fun c _ => by split_ifs <;> norm_num) (Finset.mem_univ a)
    rcases le_or_gt (θ t a) 0 with h | h
    · exact le_trans h (le_max_left _ _)
    · have : θ t a ≤ (∑ k, (if 0 < π' k then (1 : ℝ) else 0)) * θ t a := by nlinarith
      exact le_trans (by linarith) (le_max_right _ _)
  -- (5) so `π_b` stays bounded away from 0, contradicting `π_b → 0`.
  set Θ := max 0 (∑ k, θ T k - ∑ k, B k)
  set c := π' a / 2 * Real.exp (θ T b - Θ) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; have := ha; positivity
  have hlowb : ∀ t, T ≤ t → c ≤ softmax (θ t) b := by
    intro t ht
    rw [softmax_eq_mul_exp (θ t) a b, hcdef]
    have h1 := (hT₁ t (hTT₁ t ht)).2.2 a ha
    have h2 : Real.exp (θ T b - Θ) ≤ Real.exp (θ t b - θ t a) :=
      Real.exp_le_exp.2 (by linarith [hθb t ht, hθa t ht])
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (softmax_nonneg _ _)
  have hev : ∀ᶠ t in atTop, softmax (θ t) b < c := by
    have := (hc b).eventually (gt_mem_nhds (show π' b < c by rw [hb0]; exact hcpos))
    exact this
  obtain ⟨t, ht1, ht2⟩ := (hev.and (eventually_ge_atTop T)).exists
  linarith [hlowb t ht2]

/-! ### T3a (continued). Positivity, Lyapunov stability ⇒ ratifiability -/

/-- **Positivity is preserved by a linear scalar ODE with bounded coefficient.** If `ẏ = g(t) y` on `[0, t₁]`
with `|g| ≤ M` there and `y 0 > 0`, then `y t₁ > 0`. (Backward uniqueness for `ẏ = g y`, which is
`M`-Lipschitz in `y`; no continuity of `g` in `t` is needed.) -/
theorem pos_of_linear_ode {y g : ℝ → ℝ} {t₁ M : ℝ} (ht₁ : 0 ≤ t₁)
    (hy : ∀ t ∈ Set.Icc 0 t₁, HasDerivAt y (g t * y t) t) (hg : ∀ t ∈ Set.Icc 0 t₁, |g t| ≤ M)
    (h0 : 0 < y 0) : 0 < y t₁ := by
  by_contra hneg
  push Not at hneg
  have hcont : ContinuousOn y (Set.Icc 0 t₁) := fun t ht => (hy t ht).continuousAt.continuousWithinAt
  obtain ⟨τ, hτ, hyτ⟩ := intermediate_value_Icc' ht₁ hcont ⟨hneg, h0.le⟩
  have hsub : Set.Icc 0 τ ⊆ Set.Icc 0 t₁ := Set.Icc_subset_Icc le_rfl hτ.2
  have hlip : ∀ t ∈ Set.Ioc (0 : ℝ) τ, LipschitzOnWith (Real.toNNReal M) (fun x => g t * x) Set.univ := by
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul fun x _ z _ => ?_
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right ((hg t (hsub (Set.Ioc_subset_Icc_self ht))).trans
      (Real.le_coe_toNNReal M)) (abs_nonneg _)
  have heq := ODE_solution_unique_of_mem_Icc_left (v := fun t x => g t * x) (s := fun _ => Set.univ)
    (f := y) (g := fun _ => 0) hlip (hcont.mono hsub)
    (fun t ht => (hy t (hsub (Set.Ioc_subset_Icc_self ht))).hasDerivWithinAt)
    (fun _ _ => Set.mem_univ _) continuousOn_const
    (fun t _ => by simpa using (hasDerivWithinAt_const t (Set.Iic t) (0 : ℝ)))
    (fun _ _ => Set.mem_univ _) hyτ
  have := heq (Set.left_mem_Icc.2 hτ.1)
  simp only at this
  linarith

/-- **Interiority is preserved by the replicator flow** (so T3a's interiority hypothesis follows from an
interior initial condition). If `π` solves the replicator equation for `t ≥ 0`, `π 0` is interior, and each
`Q(·,c)` is continuous at every point `π t` of the trajectory, then `π t` is interior for all `t ≥ 0`. -/
theorem replicator_pos (Q : (A → ℝ) → A → ℝ) (π : ℝ → A → ℝ)
    (hπ : ∀ t, 0 ≤ t → ∀ a, HasDerivAt (fun s => π s a) (scoreUpdate Q (π t) a) t)
    (hQc : ∀ t, 0 ≤ t → ∀ c, ContinuousAt (fun p => Q p c) (π t))
    (h0 : ∀ a, 0 < π 0 a) : ∀ t, 0 ≤ t → ∀ a, 0 < π t a := by
  intro t₁ ht₁ a
  set g : ℝ → ℝ := fun t => Q (π t) a - Jpol Q (π t) with hg
  have hπc : ∀ t, 0 ≤ t → ContinuousAt π t := fun t ht =>
    continuousAt_pi.2 fun c => (hπ t ht c).continuousAt
  have hgc : ContinuousOn g (Set.Icc 0 t₁) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have hQt : ∀ c, ContinuousAt (fun s => Q (π s) c) t := fun c =>
      ContinuousAt.comp (f := π) (g := fun p => Q p c) (hQc t ht.1 c) (hπc t ht.1)
    refine (hQt a).sub ?_
    unfold Jpol
    exact tendsto_finsetSum _ fun c _ => ((continuousAt_pi.1 (hπc t ht.1) c)).mul (hQt c)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  refine pos_of_linear_ode ht₁ (y := fun s => π s a) (g := g) (M := M) (fun t ht => ?_) (fun t ht => by
    simpa [Real.norm_eq_abs] using hM t ht) (h0 a)
  refine (hπ t ht.1 a).congr_deriv ?_
  simp only [scoreUpdate, hg, Jpol]; ring

/-- **T3a, combined.** A replicator trajectory from an interior starting point, with `Q` continuous along the
trajectory and at its limit, can only converge to a ratifiable policy. -/
theorem replicator_limit_ratifiable_of_interior_start (Q : (A → ℝ) → A → ℝ) (π : ℝ → A → ℝ)
    (hπ : ∀ t, 0 ≤ t → ∀ a, HasDerivAt (fun s => π s a) (scoreUpdate Q (π t) a) t)
    (hQc : ∀ t, 0 ≤ t → ∀ c, ContinuousAt (fun p => Q p c) (π t))
    (h0 : ∀ a, 0 < π 0 a) (π' : A → ℝ) (hlim : Tendsto π atTop (𝓝 π'))
    (hQ : ∀ a, ContinuousAt (fun p => Q p a) π') : Ratifiable Q π' :=
  replicator_limit_ratifiable Q π hπ (replicator_pos Q π hπ hQc h0) π' hlim hQ

/-- **Stability with existence built in** (for the replicator flow): for every `ε > 0` there is `δ > 0` such that
from **every interior** starting point within `δ` of `π*` **some** forward solution exists and stays within `ε`
of `π*` forever. Standard Lyapunov stability (every forward solution from a nearby point stays near) implies
this whenever forward solutions from interior points exist, so assuming this is *weaker*. -/
def ReplicatorStable (Q : (A → ℝ) → A → ℝ) (π' : A → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x₀ : A → ℝ, (∀ a, 0 < x₀ a) → ∑ a, x₀ a = 1 → dist x₀ π' < δ →
    ∃ π : ℝ → A → ℝ, π 0 = x₀ ∧
      (∀ t, 0 ≤ t → ∀ a, HasDerivAt (fun s => π s a) (scoreUpdate Q (π t) a) t) ∧
      ∀ t, 0 ≤ t → dist (π t) π' < ε

/-- Interior points arbitrarily close to any simplex point. -/
theorem exists_interior_near (π' : A → ℝ) (h0 : ∀ a, 0 ≤ π' a) (h1 : ∑ a, π' a = 1) {δ : ℝ}
    (hδ : 0 < δ) : ∃ x₀ : A → ℝ, (∀ a, 0 < x₀ a) ∧ ∑ a, x₀ a = 1 ∧ dist x₀ π' < δ := by
  set n : ℝ := (Fintype.card A : ℝ)
  have hn : 0 < n := by simp only [n]; exact_mod_cast Fintype.card_pos
  set l : ℝ := min (1 / 2) (δ / 2)
  have hl : 0 < l := lt_min (by norm_num) (by linarith)
  have hl1 : l ≤ 1 / 2 := min_le_left _ _
  have hlδ : l < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hle1 : ∀ a, π' a ≤ 1 := fun a => by
    rw [← h1]; exact Finset.single_le_sum (f := π') (fun c _ => h0 c) (Finset.mem_univ a)
  refine ⟨fun a => (1 - l) * π' a + l / n, fun a => ?_, ?_, ?_⟩
  · have := h0 a; have : 0 < l / n := div_pos hl hn; nlinarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp; ring
  · refine (dist_pi_lt_iff hδ).2 fun a => ?_
    rw [Real.dist_eq]
    have e : (1 - l) * π' a + l / n - π' a = l * (1 / n - π' a) := by ring
    rw [e, abs_mul, abs_of_pos hl]
    have h1n : 1 / n ≤ 1 := by
      rw [div_le_one hn]; simp only [n]; exact_mod_cast Fintype.card_pos
    have h1n0 : 0 < 1 / n := by positivity
    have : |1 / n - π' a| ≤ 1 := abs_le.2 ⟨by linarith [hle1 a], by linarith [h0 a]⟩
    calc l * |1 / n - π' a| ≤ l * 1 := mul_le_mul_of_nonneg_left this hl.le
      _ < δ := by linarith

/-- **T3a (Lyapunov stability ⇒ ratifiability).** Let `π*` be a simplex point with each `Q(·,a)` continuous at
`π*`. If `π*` is stable for the replicator flow (`ReplicatorStable`, which is implied by Lyapunov stability
whenever forward solutions from interior points exist), then `π*` is ratifiable. -/
theorem ratifiable_of_replicatorStable (Q : (A → ℝ) → A → ℝ) (π' : A → ℝ) (h0 : ∀ a, 0 ≤ π' a)
    (h1 : ∑ a, π' a = 1) (hQ : ∀ a, ContinuousAt (fun p => Q p a) π') (hst : ReplicatorStable Q π') :
    Ratifiable Q π' := by
  by_contra hnr
  obtain ⟨b, -, hbmax⟩ := Finset.exists_max_image Finset.univ (fun c => Q π' c) Finset.univ_nonempty
  have hJlt : Jpol Q π' < Q π' b := by
    unfold Ratifiable at hnr
    push Not at hnr
    obtain ⟨a, ha, c, hc⟩ := hnr
    have hlt : ∑ x, π' x * Q π' x < ∑ x, π' x * Q π' b :=
      Finset.sum_lt_sum (fun x _ => mul_le_mul_of_nonneg_left (hbmax x (Finset.mem_univ x)) (h0 x))
        ⟨a, Finset.mem_univ a, mul_lt_mul_of_pos_left (lt_of_lt_of_le hc (hbmax c (Finset.mem_univ c))) ha⟩
    rw [← Finset.sum_mul, h1, one_mul] at hlt
    exact hlt
  set δ' := (Q π' b - Jpol Q π') / 2 with hδ'
  have hδ'pos : 0 < δ' := by rw [hδ']; linarith
  have hcont : ContinuousAt (fun p => Q p b - Jpol Q p) π' := by
    refine (hQ b).sub ?_
    unfold Jpol
    exact tendsto_finsetSum _ fun c _ => (continuousAt_apply c π').mul (hQ c)
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.1 hcont δ' hδ'pos
  obtain ⟨δ, hδ, hstab⟩ := hst ε hε
  obtain ⟨x₀, hx0pos, hx0sum, hx0d⟩ := exists_interior_near π' h0 h1 hδ
  obtain ⟨π, hπ0, hπ, hπε⟩ := hstab x₀ hx0pos hx0sum hx0d
  set g : ℝ → ℝ := fun t => Q (π t) b - Jpol Q (π t) with hgdef
  have hg : ∀ t, 0 ≤ t → δ' ≤ g t ∧ g t ≤ 3 * δ' := by
    intro t ht
    have := hball (hπε t ht)
    rw [Real.dist_eq, abs_lt] at this
    simp only [hgdef]
    constructor <;> linarith
  have hy : ∀ t, 0 ≤ t → HasDerivAt (fun s => π s b) (g t * π t b) t := by
    intro t ht
    refine (hπ t ht b).congr_deriv ?_
    simp only [scoreUpdate, hgdef, Jpol]; ring
  have hpos : ∀ t, 0 ≤ t → 0 < π t b := by
    intro t ht
    refine pos_of_linear_ode ht (y := fun s => π s b) (g := g) (M := 3 * δ')
      (fun s hs => hy s hs.1) (fun s hs => ?_) (by rw [hπ0]; exact hx0pos b)
    obtain ⟨h1, h2⟩ := hg s hs.1
    rw [abs_le]; constructor <;> linarith
  have hlog : ∀ t, 0 ≤ t → HasDerivAt (fun s => Real.log (π s b) - δ' * s) (g t - δ' * 1) t := by
    intro t ht
    refine (((hy t ht).log (hpos t ht).ne').sub ((hasDerivAt_id t).const_mul δ')).congr_deriv ?_
    field_simp [(hpos t ht).ne']
  have hmono := le_of_hasDerivAt_nonneg (T := 0) hlog (fun t ht => by linarith [(hg t ht).1])
  have hub : ∀ t, 0 ≤ t → π t b < π' b + ε := by
    intro t ht
    have := lt_of_le_of_lt (dist_le_pi_dist (π t) π' b) (hπε t ht)
    rw [Real.dist_eq, abs_lt] at this
    linarith
  have htop : Tendsto (fun t => Real.log (π 0 b) + δ' * t) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hδ'pos)
  obtain ⟨t, ht0, htbig⟩ :=
    ((eventually_ge_atTop 0).and (htop.eventually_gt_atTop (Real.log (π' b + ε)))).exists
  have h1' := hmono t ht0
  simp only [mul_zero, sub_zero] at h1'
  have h2' : Real.log (π t b) < Real.log (π' b + ε) :=
    Real.log_lt_log (hpos t ht0) (hub t ht0)
  linarith

/-! ### T4. Strict ratifiability and asymptotic stability (replicator flow) -/

/-- **Strict ratifiability**: ratifiable, and every unplayed action is strictly worse than the played ones. -/
def StrictlyRatifiable (Q : (A → ℝ) → A → ℝ) (π : A → ℝ) : Prop :=
  Ratifiable Q π ∧ ∀ a b, 0 < π a → π b = 0 → Q π b < Q π a

/-- MVT on a bounded interval. -/
theorem le_of_hasDerivAt_nonneg_Icc {g g' : ℝ → ℝ} {x t : ℝ} (hxt : x ≤ t)
    (hg : ∀ s ∈ Set.Icc x t, HasDerivAt g (g' s) s) (h : ∀ s ∈ Set.Ioo x t, 0 ≤ g' s) : g x ≤ g t := by
  rcases hxt.lt_or_eq with hlt | heq
  · have hcont : ContinuousOn g (Set.Icc x t) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope g g' hlt hcont
      (fun s hs => hg s (Set.Ioo_subset_Icc_self hs))
    have h1 := h ξ hξ
    rw [hξeq] at h1
    rcases div_nonneg_iff.1 h1 with ⟨h3, _⟩ | ⟨_, h4⟩
    · linarith
    · linarith
  · rw [heq]

/-- **Barrier lemma**: if `y' ≥ 0` whenever `y > c`, and `y 0 > c`, then `y t ≥ y 0` for all `t ≥ 0`. -/
theorem barrier {y y' : ℝ → ℝ} {c : ℝ} (hy : ∀ t, 0 ≤ t → HasDerivAt y (y' t) t) (h0 : c < y 0)
    (hpos : ∀ t, 0 ≤ t → c < y t → 0 ≤ y' t) : ∀ t, 0 ≤ t → y 0 ≤ y t := by
  intro t₁ ht₁
  have hcont : ContinuousOn y (Set.Icc 0 t₁) := fun t ht => (hy t ht.1).continuousAt.continuousWithinAt
  have hclosed : IsClosed ({t | y 0 ≤ y t} ∩ Set.Icc 0 t₁) := by
    have := hcont.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := y 0))
    rw [Set.inter_comm]; exact this
  have hsub := IsClosed.Icc_subset_of_forall_mem_nhdsWithin hclosed (show y 0 ≤ y 0 from le_rfl) ?_
  · exact hsub ⟨ht₁, le_rfl⟩
  rintro x ⟨hx, hxI⟩
  have hx' : c < y x := lt_of_lt_of_le h0 hx
  obtain ⟨ρ, hρ, hρball⟩ := Metric.eventually_nhds_iff.1
    ((hy x hxI.1).continuousAt.eventually (lt_mem_nhds hx'))
  rw [mem_nhdsGT_iff_exists_Ioo_subset]
  refine ⟨x + ρ, by simp [hρ], fun t ht => ?_⟩
  have : y x ≤ y t := by
    refine le_of_hasDerivAt_nonneg_Icc ht.1.le (fun s hs => hy s (le_trans hxI.1 hs.1))
      (fun s hs => hpos s (le_trans hxI.1 hs.1.le) (hρball ?_))
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2, ht.2]
  exact le_trans hx this

/-- On the simplex, the distance (sup metric) to the vertex `e_a` is `1 − p_a`. -/
theorem dist_single_eq {p : A → ℝ} (h0 : ∀ c, 0 ≤ p c) (h1 : ∑ c, p c = 1) (a : A) :
    dist p (Pi.single a 1) = 1 - p a := by
  have hle1 : ∀ c, p c ≤ 1 := fun c => by
    rw [← h1]; exact Finset.single_le_sum (f := p) (fun c _ => h0 c) (Finset.mem_univ c)
  have hoff : ∀ c, c ≠ a → p c ≤ 1 - p a := by
    intro c hc
    have : p c + p a ≤ ∑ x, p x := by
      rw [← Finset.sum_pair hc]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => h0 x)
    linarith
  apply le_antisymm
  · refine (dist_pi_le_iff (by linarith [hle1 a])).2 fun c => ?_
    rw [Real.dist_eq]
    by_cases hc : c = a
    · subst hc; simp only [Pi.single_eq_same]; rw [abs_of_nonpos (by linarith [hle1 c])]; linarith
    · simp only [Pi.single_eq_of_ne hc, sub_zero]; rw [abs_of_nonneg (h0 c)]; exact hoff c hc
  · have := dist_le_pi_dist p (Pi.single a 1) a
    rw [Real.dist_eq, Pi.single_eq_same, abs_of_nonpos (by linarith [hle1 a])] at this
    linarith

/-- **T4, vertex case.** A strictly ratifiable vertex `e_a` (every other action strictly worse against `e_a`),
with `Q` continuous there, is **asymptotically stable** for the replicator flow: there is `η > 0` such that
every simplex-valued solution starting within `η` of `e_a` stays at least as close as it started
(Lyapunov stability) and converges to `e_a`. -/
theorem vertex_asymptoticallyStable (Q : (A → ℝ) → A → ℝ) (a : A)
    (hstrict : StrictlyRatifiable Q (Pi.single a 1))
    (hQ : ∀ c, ContinuousAt (fun p => Q p c) (Pi.single a 1)) :
    ∃ η > 0, ∀ π : ℝ → A → ℝ, (∀ t, 0 ≤ t → ∀ c, 0 ≤ π t c) → (∀ t, 0 ≤ t → ∑ c, π t c = 1) →
      (∀ t, 0 ≤ t → ∀ c, HasDerivAt (fun s => π s c) (scoreUpdate Q (π t) c) t) →
      dist (π 0) (Pi.single a 1) < η →
      (∀ t, 0 ≤ t → dist (π t) (Pi.single a 1) ≤ dist (π 0) (Pi.single a 1)) ∧
        Tendsto π atTop (𝓝 (Pi.single a 1)) := by
  set e : A → ℝ := Pi.single a 1 with he
  -- a uniform gap `κ > 0` at the vertex
  set f : A → ℝ := fun u => if u = a then 1 else (Q e a - Q e u) / 2 with hf
  have hfpos : ∀ u, 0 < f u := by
    intro u
    simp only [hf]
    split_ifs with hu
    · norm_num
    · have := hstrict.2 a u (by simp [he]) (by simp [he, hu])
      linarith
  obtain ⟨u₀, -, hu₀⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  set κ := f u₀ with hκ
  have hκpos : 0 < κ := hfpos u₀
  -- near the vertex, `Q(p,a) − Q(p,u) ≥ κ` for every `u ≠ a`
  have hev : ∀ᶠ p in 𝓝 e, ∀ u, u ≠ a → κ ≤ Q p a - Q p u := by
    refine eventually_all.2 fun u => ?_
    by_cases hu : u = a
    · exact Eventually.of_forall fun _ h => absurd hu h
    · have hlim : Tendsto (fun p => Q p a - Q p u) (𝓝 e) (𝓝 (Q e a - Q e u)) := (hQ a).sub (hQ u)
      have hfu : f u = (Q e a - Q e u) / 2 := by simp [hf, hu]
      have hgap : κ < Q e a - Q e u := by
        have := hu₀ u (Finset.mem_univ u)
        have := hfpos u
        rw [hfu] at *; linarith
      exact (hlim.eventually (lt_mem_nhds hgap)).mono fun p hp _ => hp.le
  obtain ⟨ρ, hρ, hρball⟩ := Metric.eventually_nhds_iff.1 hev
  set η := min ρ (1 / 2) with hη
  have hηpos : 0 < η := lt_min hρ (by norm_num)
  have hη2 : η ≤ 1 / 2 := min_le_right _ _
  have hηρ : η ≤ ρ := min_le_left _ _
  refine ⟨η, hηpos, fun π hπ0 hπ1 hπ hstart => ?_⟩
  have hdist : ∀ t, 0 ≤ t → dist (π t) e = 1 - π t a := fun t ht => dist_single_eq (hπ0 t ht) (hπ1 t ht) a
  -- key inequality: `Q_a − J ≥ κ (1 − p_a)` near the vertex
  have hkey : ∀ t, 0 ≤ t → 1 - η < π t a →
      κ * (1 - π t a) ≤ Q (π t) a - Jpol Q (π t) := by
    intro t ht hta
    have hnear : dist (π t) e < ρ := by
      rw [hdist t ht]; linarith
    have hgap := hρball hnear
    have hexp : Q (π t) a - Jpol Q (π t) = ∑ u, π t u * (Q (π t) a - Q (π t) u) := by
      simp only [Jpol, mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, hπ1 t ht, one_mul]
    have hsplit : 1 - π t a = ∑ u, (if u = a then 0 else π t u) := by
      rw [← hπ1 t ht, Finset.sum_ite, Finset.sum_const_zero, zero_add]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun u => u = a)]
      simp [Finset.filter_eq']
    rw [hexp, hsplit, Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    by_cases hu : u = a
    · subst hu; simp
    · simp only [hu, ite_false]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hgap u hu) (hπ0 t ht u)
  have hstart' : 1 - η < π 0 a := by have := hdist 0 le_rfl; linarith
  -- (i) `π_a` never decreases: barrier
  have hmono : ∀ t, 0 ≤ t → π 0 a ≤ π t a := by
    refine barrier (y := fun s => π s a) (y' := fun t => scoreUpdate Q (π t) a) (c := 1 - η)
      (fun t ht => hπ t ht a) hstart' (fun t ht hta => ?_)
    have := hkey t ht hta
    have h1 : 0 ≤ κ * (1 - π t a) := by
      have : π t a ≤ 1 := by
        rw [← hπ1 t ht]; exact Finset.single_le_sum (f := π t) (fun c _ => hπ0 t ht c) (Finset.mem_univ a)
      nlinarith
    exact mul_nonneg (hπ0 t ht a) (by unfold Jpol at this; linarith)
  refine ⟨fun t ht => by rw [hdist t ht, hdist 0 le_rfl]; linarith [hmono t ht], ?_⟩
  -- (ii) exponential convergence of `r = 1 − π_a`
  have hrdecay : ∀ t, 0 ≤ t → (1 - π t a) * Real.exp (κ / 2 * t) ≤ 1 - π 0 a := by
    have hder : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 - π s a) * Real.exp (κ / 2 * s))
        ((-scoreUpdate Q (π t) a) * Real.exp (κ / 2 * t) +
          (1 - π t a) * (Real.exp (κ / 2 * t) * (κ / 2 * 1))) t := by
      intro t ht
      exact ((hπ t ht a).const_sub 1).mul (((hasDerivAt_id t).const_mul (κ / 2)).exp)
    have := le_of_hasDerivAt_nonpos (T := 0) hder (fun t ht => ?_)
    · intro t ht; have := this t ht; simpa using this
    have hta : 1 - η < π t a := lt_of_lt_of_le hstart' (hmono t ht)
    have hk := hkey t ht hta
    have hhalf : 1 / 2 ≤ π t a := by linarith
    have hr0 : 0 ≤ 1 - π t a := by
      have : π t a ≤ 1 := by
        rw [← hπ1 t ht]; exact Finset.single_le_sum (f := π t) (fun c _ => hπ0 t ht c) (Finset.mem_univ a)
      linarith
    have hsu : κ / 2 * (1 - π t a) ≤ scoreUpdate Q (π t) a := by
      unfold scoreUpdate
      have : κ * (1 - π t a) ≤ Q (π t) a - ∑ c, π t c * Q (π t) c := hk
      have hX : 0 ≤ Q (π t) a - ∑ c, π t c * Q (π t) c := le_trans (mul_nonneg hκpos.le hr0) this
      have := mul_le_mul_of_nonneg_right hhalf hX
      linarith
    have hE := Real.exp_pos (κ / 2 * t)
    nlinarith
  rw [tendsto_iff_dist_tendsto_zero]
  have hupper : ∀ t, 0 ≤ t → dist (π t) e ≤ (1 - π 0 a) * Real.exp (-(κ / 2 * t)) := by
    intro t ht
    rw [hdist t ht, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    exact hrdecay t ht
  have hlim0 : Tendsto (fun t => (1 - π 0 a) * Real.exp (-(κ / 2 * t))) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => Real.exp (-(κ / 2 * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_id.const_mul_atTop (by linarith)))
    simpa using this.const_mul (1 - π 0 a)
  refine squeeze_zero' (Eventually.of_forall fun t => dist_nonneg) ?_ hlim0
  filter_upwards [eventually_ge_atTop 0] with t ht using hupper t ht

/-- **T4, interior case: false as stated.** At a full-support policy "every unplayed action is strictly worse" is
vacuous, so strict ratifiability is just ratifiability, and it does not give asymptotic stability: with
`Q ≡ 0` on two actions, the uniform policy is strictly ratifiable, but arbitrarily close to it there are
constant (stationary) interior solutions that do not converge to it. -/
theorem interior_strictlyRatifiable_not_asymptoticallyStable :
    let Q : (Fin 2 → ℝ) → Fin 2 → ℝ := fun _ _ => 0
    let u : Fin 2 → ℝ := fun _ => 1 / 2
    StrictlyRatifiable Q u ∧ ∀ η > 0, ∃ π : ℝ → Fin 2 → ℝ, (∀ t c, 0 < π t c) ∧ (∀ t, ∑ c, π t c = 1) ∧
      (∀ t c, HasDerivAt (fun s => π s c) (scoreUpdate Q (π t) c) t) ∧ dist (π 0) u < η ∧
      ¬ Tendsto π atTop (𝓝 u) := by
  intro Q u
  refine ⟨⟨fun a _ b => le_rfl, fun a b _ hb => by simp [u] at hb⟩, fun η hη => ?_⟩
  set s := min (η / 2) (1 / 4) with hs
  have hs0 : 0 < s := lt_min (by linarith) (by norm_num)
  have hs1 : s ≤ 1 / 4 := min_le_right _ _
  have hsη : s < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set x : Fin 2 → ℝ := ![1 / 2 + s, 1 / 2 - s] with hx
  refine ⟨fun _ => x, fun t c => ?_, fun t => ?_, fun t c => ?_, ?_, ?_⟩
  · fin_cases c <;> simp [hx] <;> linarith
  · simp [hx, Fin.sum_univ_two]; norm_num
  · simpa [scoreUpdate, Q] using hasDerivAt_const t (x c)
  · refine (dist_pi_lt_iff hη).2 fun c => ?_
    fin_cases c <;> simp [hx, u, abs_of_pos hs0] <;> linarith
  · intro h
    have := tendsto_nhds_unique tendsto_const_nhds h
    have h0 := congrFun this 0
    simp [hx, u] at h0
    linarith

/-! ### Corollaries on the earlier examples -/

theorem newcomb_continuousAt (π' : Fin 2 → ℝ) (a : Fin 2) : ContinuousAt (fun p => newcomb p a) π' := by
  fin_cases a
  · simp only [newcomb, Fin.zero_eta, Fin.isValue, ite_true]
    exact ((continuous_apply 0).const_smul (1000 : ℝ)).continuousAt
  · simp only [newcomb, Fin.mk_one, Fin.isValue, one_ne_zero, ite_false]
    exact (((continuous_apply 0).const_smul (1000 : ℝ)).add continuous_const).continuousAt

/-- **Newcomb: pure one-boxing is stationary but unreachable.** It is a zero of the mean score-function update
(`newcomb_pure_scoreUpdate_zero`), but no solution of the vanilla REINFORCE flow has its policy converge to it. -/
theorem newcomb_oneBox_not_limit (θ : ℝ → Fin 2 → ℝ) {T₀ : ℝ}
    (hθ : ∀ t, T₀ ≤ t → ∀ k, HasDerivAt (fun s => θ s k) (reinforce newcomb (θ t) k) t) :
    ¬ Tendsto (fun t => softmax (θ t)) atTop (𝓝 oneBox) := fun h =>
  newcomb_pure_not_ratifiable
    (reinforce_limit_ratifiable newcomb θ hθ oneBox h (newcomb_continuousAt oneBox))

theorem AO_continuousAt (π' : Fin 3 → ℝ) (a : Fin 3) : ContinuousAt (fun p => AO p a) π' :=
  (AO_hasFDerivAt π' a).continuousAt

/-- **Adversarial-offer variant: the only possible limit of plain REINFORCE is `(1/2, 1/2, 0)`.** Every solution of the
vanilla flow whose policy converges at all converges to the unique ratifiable policy, which earns `1/2 < 2/3`. -/
theorem AO_reinforce_limit (θ : ℝ → Fin 3 → ℝ) {T₀ : ℝ}
    (hθ : ∀ t, T₀ ≤ t → ∀ k, HasDerivAt (fun s => θ s k) (reinforce AO (θ t) k) t) (π' : Fin 3 → ℝ)
    (h : Tendsto (fun t => softmax (θ t)) atTop (𝓝 π')) : π' = AOratif := by
  obtain ⟨h0, h1⟩ := simplex_of_tendsto h (fun t a => softmax_nonneg _ _) (fun t => sum_softmax _)
  exact (AO_ratifiable_iff π' h0 h1).1 (reinforce_limit_ratifiable AO θ hθ π' h (AO_continuousAt π'))

end Dynamics

end BoundaryTheorem.RatifiableStrong
