import Mathlib

/-!
# U2: minimax regret from a regret saddle point (finite core of PAIRED)

Dennis et al. 2020 ("Emergent Complexity and Zero-shot Transfer via Unsupervised
Environment Design", PAIRED) prove that at a Nash equilibrium of their
protagonist/adversary game, the protagonist policy is a minimax-regret policy.
This file is the finite, deterministic core of that claim.

## Proved (in `U2_minimax_regret.lean`; this file has identical statements)
* `regret_nonneg` : regret is nonnegative.
* `regret_eq_zero_iff` : regret `π e = 0` iff `π` is optimal on `e`.
* `worst_regret_of_saddle` : at a saddle point, worst-case regret of `π*` equals
  `regret π* e*` (the game value).
* `minimax_regret_of_saddle` : at a saddle point `(π*, e*)` of regret,
  `max_e regret π* e ≤ max_e regret π e` for every `π`.
* `isRegretSaddle_iff` (added, beyond the spec) : `(π*, e*)` is a saddle iff
  `max_e regret π* e ≤ min_π regret π e*`, so the minimax property above is one
  half of an exact characterisation.
* `dominantU_saddle` (non-vacuity) : a concrete 2×2 table (`Bool × Bool`) where a
  saddle exists, so the hypothesis of (2) is satisfiable.
* `penniesU_no_saddle` : a concrete 2×2 "matching pennies" table with no pure
  saddle point, so the hypothesis of (2) is a real restriction.

## Interpreted (NOT proved here)
* That this is "PAIRED's" equilibrium: PAIRED estimates regret with an antagonist
  policy and sampled returns over stochastic environments and parameterised
  generators; we model only a finite payoff table `U : Pol → E → ℝ` with the exact
  regret `best e - U π e`. No learning dynamics, no existence of a saddle point
  (pure saddle points need not exist, see `penniesU_no_saddle`; PAIRED's argument
  uses mixed strategies),
  and no approximation guarantees are claimed.
-/

namespace UED

variable {Pol E : Type*} [Fintype Pol] [Nonempty Pol] [Fintype E] [Nonempty E]

/-- Best achievable utility on environment `e`. -/
noncomputable def best (U : Pol → E → ℝ) (e : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun π' => U π' e)

/-- Regret of policy `π` on environment `e`. -/
noncomputable def regret (U : Pol → E → ℝ) (π : Pol) (e : E) : ℝ :=
  best U e - U π e

/-- Worst-case (max over environments) regret of policy `π`. -/
noncomputable def worstRegret (U : Pol → E → ℝ) (π : Pol) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun e => regret U π e)

/-- `(πs, es)` is a saddle point of regret: the adversary (environment) maximises,
the protagonist (policy) minimises. -/
def IsRegretSaddle (U : Pol → E → ℝ) (πs : Pol) (es : E) : Prop :=
  (∀ e, regret U πs e ≤ regret U πs es) ∧ (∀ π, regret U πs es ≤ regret U π es)

/-- (1a) Regret is nonnegative. -/
theorem regret_nonneg (U : Pol → E → ℝ) (π : Pol) (e : E) : 0 ≤ regret U π e := by
  unfold regret best
  have : U π e ≤ Finset.univ.sup' Finset.univ_nonempty (fun π' => U π' e) :=
    Finset.le_sup' (fun π' => U π' e) (Finset.mem_univ π)
  linarith

/-- (1b) Zero regret iff optimal on `e`. -/
theorem regret_eq_zero_iff (U : Pol → E → ℝ) (π : Pol) (e : E) :
    regret U π e = 0 ↔ ∀ π', U π' e ≤ U π e := by
  have hle : U π e ≤ best U e :=
    Finset.le_sup' (fun π' => U π' e) (Finset.mem_univ π)
  constructor
  · intro h0 π'
    have hb : best U e = U π e := by unfold regret at h0; linarith
    have : U π' e ≤ best U e := Finset.le_sup' (fun π' => U π' e) (Finset.mem_univ π')
    linarith
  · intro hopt
    have hb : best U e ≤ U π e := Finset.sup'_le _ _ (fun π' _ => hopt π')
    unfold regret
    linarith

/-- At a saddle point, the worst-case regret of `πs` is the saddle value. -/
theorem worst_regret_of_saddle (U : Pol → E → ℝ) (πs : Pol) (es : E)
    (h : IsRegretSaddle U πs es) : worstRegret U πs = regret U πs es := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun e _ => h.1 e)
  · exact Finset.le_sup' (fun e => regret U πs e) (Finset.mem_univ es)

/-- (2) Minimax regret: a saddle-point policy minimises worst-case regret. -/
theorem minimax_regret_of_saddle (U : Pol → E → ℝ) (πs : Pol) (es : E)
    (h : IsRegretSaddle U πs es) (π : Pol) :
    worstRegret U πs ≤ worstRegret U π := by
  rw [worst_regret_of_saddle U πs es h]
  exact (h.2 π).trans (Finset.le_sup' (fun e => regret U π e) (Finset.mem_univ es))

/-- Best-response (min over policies) regret on environment `e`: the adversary's
guaranteed payoff if it commits to `e`. -/
noncomputable def minRegret (U : Pol → E → ℝ) (e : E) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun π => regret U π e)

/-- (Added, going up) Exact characterisation of regret saddle points:
`(πs, es)` is a saddle iff `max_e regret πs e ≤ min_π regret π es`.
Since `min_π regret π es ≤ regret πs es ≤ max_e regret πs e` always holds, this says
the saddle points are exactly the pairs where the upper value attained by `πs`
meets the lower value attained by `es`. In particular `minimax_regret_of_saddle` is
one direction of a full iff, and the saddle hypothesis is checkable from the two
one-sided values alone. -/
theorem isRegretSaddle_iff (U : Pol → E → ℝ) (πs : Pol) (es : E) :
    IsRegretSaddle U πs es ↔ worstRegret U πs ≤ minRegret U es := by
  constructor
  · intro h
    rw [worst_regret_of_saddle U πs es h]
    exact Finset.le_inf' _ _ (fun π _ => h.2 π)
  · intro hle
    have hmin : minRegret U es ≤ regret U πs es :=
      Finset.inf'_le (fun π => regret U π es) (Finset.mem_univ πs)
    have hworst : regret U πs es ≤ worstRegret U πs :=
      Finset.le_sup' (fun e => regret U πs e) (Finset.mem_univ es)
    refine ⟨fun e => ?_, fun π => ?_⟩
    · have : regret U πs e ≤ worstRegret U πs :=
        Finset.le_sup' (fun e => regret U πs e) (Finset.mem_univ e)
      linarith
    · have : minRegret U es ≤ regret U π es :=
        Finset.inf'_le (fun π => regret U π es) (Finset.mem_univ π)
      linarith

/-! ### Concrete examples (non-vacuity and the "no pure saddle" caveat) -/

/-- A dominant policy: `true` gets utility 1 everywhere, `false` gets 0. -/
noncomputable def dominantU : Bool → Bool → ℝ := fun π _ => if π then 1 else 0

/-- Non-vacuity: the saddle hypothesis is satisfiable (`(true, e)` is a saddle for any `e`). -/
theorem dominantU_saddle (e : Bool) : IsRegretSaddle dominantU true e := by
  have h0 : ∀ e, regret dominantU true e = 0 := fun e =>
    (regret_eq_zero_iff dominantU true e).2 (fun π' => by cases π' <;> simp [dominantU])
  exact ⟨fun e => by rw [h0, h0], fun π => by rw [h0]; exact regret_nonneg _ _ _⟩

/-- Matching pennies as a regret game: policy `b` scores 1 exactly on environment `b`.
Every pure policy has worst-case regret 1, every environment has min-regret 0. -/
noncomputable def penniesU : Bool → Bool → ℝ := fun π e => if π = e then 1 else 0

/-- Pure regret saddle points need not exist, so the hypothesis of
`minimax_regret_of_saddle` is a genuine restriction (PAIRED's own argument uses
mixed strategies, which this file does not model). -/
theorem penniesU_no_saddle : ¬ ∃ πs es, IsRegretSaddle penniesU πs es := by
  rintro ⟨πs, es, h1, h2⟩
  have hdiag : ∀ b, regret penniesU b b = 0 := fun b =>
    (regret_eq_zero_iff penniesU b b).2 (fun π' => by
      cases π' <;> cases b <;> simp [penniesU])
  by_cases hpe : πs = es
  · subst hpe
    -- the adversary deviates to the other environment
    have h := h1 (!πs)
    rw [hdiag] at h
    have hz : regret penniesU πs (!πs) = 0 := le_antisymm h (regret_nonneg _ _ _)
    have := ((regret_eq_zero_iff penniesU πs (!πs)).1 hz) (!πs)
    cases πs <;> simp [penniesU] at this <;> linarith
  · -- the protagonist deviates to the policy matching `es`
    have h := h2 es
    rw [hdiag] at h
    have hz : regret penniesU πs es = 0 := le_antisymm h (regret_nonneg _ _ _)
    have := ((regret_eq_zero_iff penniesU πs es).1 hz) es
    cases πs <;> cases es <;> simp_all [penniesU] <;> linarith

end UED
