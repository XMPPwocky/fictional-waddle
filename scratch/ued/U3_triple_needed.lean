import Mathlib

/-!
# U3: two roles collapse, three do not  (proofs)

Setting.  Finite nonempty policy type `Π`, environment type `E`, utility
`U : Π → E → ℝ`.  An "impossible" environment `e0` is one on which every policy
gets the same value `m`, and `m` is a global floor: `U π e0 = m`, `U π e ≥ m`.

PROVED (in `U3_triple_needed.lean`):
* (1) a two-role (adversarial) designer with score `-U π e` is always maximized
  at `e0`, and at `e0` the protagonist's policy has no effect on its utility;
* (2) the regret designer gives `e0` regret `0`, gives regret `0` to every
  environment on which `π` is already optimal, and any positive-regret
  environment (in particular any regret-maximizer with positive max regret)
  is one some other policy solves strictly better than `π`.  We also prove the
  exact characterisation `0 < regret π e ↔ ∃ π', U π e < U π' e`.
* (added, going up) `regret_zero_all_iff_flat`: zero regret against every
  policy iff the level is flat (all policies tie), with no floor needed;
* (non-vacuity) `toy_nonvacuous`: a 2-policy, 2-level instance meeting every
  hypothesis, with a positive regret-maximizer distinct from `e0`.

INTERPRETED (not proved; reading only):
* "zero learning signal" is read off from `U · e0` being constant in the
  policy; no gradient / learning dynamics are formalised;
* "regret-maximizing levels are the learnable frontier" is the reading of the
  `argmax ⊆ {solvable by someone, not yet by π}` theorem.
-/

open Finset

namespace UED3

variable {P E : Type*} [Fintype P] [Nonempty P]

/-- Best achievable utility on `e` (max over the finite policy set). -/
noncomputable def best (U : P → E → ℝ) (e : E) : ℝ :=
  univ.sup' univ_nonempty (fun p => U p e)

/-- Regret of `π` on `e`. -/
noncomputable def regret (U : P → E → ℝ) (π : P) (e : E) : ℝ :=
  best U e - U π e

/-- Two-role designer's score: protagonist's failure. -/
def score₂ (U : P → E → ℝ) (π : P) (e : E) : ℝ := -U π e

/-- `e0` is impossible with floor `m`. -/
def Impossible (U : P → E → ℝ) (e0 : E) (m : ℝ) : Prop :=
  (∀ π, U π e0 = m) ∧ ∀ π e, m ≤ U π e

/-! ## (1) Two roles collapse -/

/-- PROVED: the adversarial designer is always (weakly) best off at `e0`. -/
theorem score₂_max_at_impossible (U : P → E → ℝ) {e0 : E} {m : ℝ}
    (h : Impossible U e0 m) (π : P) (e : E) :
    score₂ U π e ≤ score₂ U π e0 := by
  simp only [score₂, h.1 π, neg_le_neg_iff]
  exact h.2 π e

/-- PROVED: at `e0` the protagonist's choice does not affect its utility. -/
theorem impossible_no_signal (U : P → E → ℝ) {e0 : E} {m : ℝ}
    (h : Impossible U e0 m) (π π' : P) :
    U π e0 = U π' e0 := by
  rw [h.1 π, h.1 π']

/-! ## (2) Regret designer -/

/-- PROVED: regret is nonnegative. -/
theorem regret_nonneg (U : P → E → ℝ) (π : P) (e : E) : 0 ≤ regret U π e := by
  unfold regret best
  have := Finset.le_sup' (fun p => U p e) (Finset.mem_univ π)
  linarith

/-- PROVED: the impossible environment has zero regret. -/
theorem regret_impossible (U : P → E → ℝ) {e0 : E} {m : ℝ}
    (h : Impossible U e0 m) (π : P) : regret U π e0 = 0 := by
  unfold regret best
  have hb : univ.sup' univ_nonempty (fun p => U p e0) = m := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun p _ => (h.1 p).le)
    · rw [← h.1 π]; exact Finset.le_sup' (fun p => U p e0) (Finset.mem_univ π)
  rw [hb, h.1 π]; ring

/-- PROVED: if some environment has positive regret against `π`, then `e0`
is strictly beaten, hence not a regret-maximizer. -/
theorem impossible_not_regret_max (U : P → E → ℝ) {e0 : E} {m : ℝ}
    (h : Impossible U e0 m) (π : P) (hpos : ∃ e, 0 < regret U π e) :
    ∃ e, regret U π e0 < regret U π e := by
  obtain ⟨e, he⟩ := hpos
  exact ⟨e, by rw [regret_impossible U h π]; exact he⟩

/-- PROVED: an environment on which `π` is already optimal has zero regret. -/
theorem regret_trivial (U : P → E → ℝ) (π : P) (e : E)
    (hopt : ∀ π', U π' e ≤ U π e) : regret U π e = 0 := by
  unfold regret best
  have : univ.sup' univ_nonempty (fun p => U p e) ≤ U π e :=
    Finset.sup'_le _ _ (fun p _ => hopt p)
  have := Finset.le_sup' (fun p => U p e) (Finset.mem_univ π)
  linarith

/-- PROVED (iff, the general form): positive regret exactly when some policy
does strictly better than `π` on `e`. -/
theorem regret_pos_iff (U : P → E → ℝ) (π : P) (e : E) :
    0 < regret U π e ↔ ∃ π', U π e < U π' e := by
  unfold regret best
  rw [sub_pos, Finset.lt_sup'_iff]
  simp

/-- PROVED: when the maximal regret is positive, every regret-maximizer is
solvable (strictly better) by some policy but not yet by `π`. -/
theorem argmax_regret_subset (U : P → E → ℝ) (π : P) (estar : E)
    (hmax : ∀ e, regret U π e ≤ regret U π estar) (hpos : 0 < regret U π estar) :
    estar ∈ {e | ∃ π', U π' e > U π e} := by
  exact (regret_pos_iff U π estar).1 hpos

/-- PROVED (contrast, packaging (1) and (2)): `e0` is in the two-role argmax
for every `π`, but is excluded from the regret argmax whenever any positive
regret exists. -/
theorem two_collapse_three_not (U : P → E → ℝ) {e0 : E} {m : ℝ}
    (h : Impossible U e0 m) (π : P) :
    (∀ e, score₂ U π e ≤ score₂ U π e0) ∧
    ((∃ e, 0 < regret U π e) → ¬ ∀ e, regret U π e ≤ regret U π e0) := by
  refine ⟨score₂_max_at_impossible U h π, ?_⟩
  intro hpos hmax
  obtain ⟨e, he⟩ := impossible_not_regret_max U h π hpos
  exact absurd (hmax e) (not_le.2 he)

/-! ## Going up: the regret designer is blind exactly to zero-signal levels -/

/-- PROVED (added by the second agent; the iff generalising both
`regret_impossible` and `impossible_no_signal`): an environment has zero regret
against *every* policy iff it is *flat*, i.e. all policies tie on it.  No floor
`m` is needed: "impossible" is one special flat level.  So the levels the
regret designer can never use are exactly the zero-signal levels, while the
two-role designer is drawn to the flat level at the global floor. -/
theorem regret_zero_all_iff_flat (U : P → E → ℝ) (e : E) :
    (∀ π, regret U π e = 0) ↔ ∀ π π', U π e = U π' e := by
  constructor
  · intro h π π'
    have hopt : ∀ p q, U q e ≤ U p e := fun p q => by
      by_contra hc
      have := (regret_pos_iff U p e).2 ⟨q, not_le.1 hc⟩
      rw [h p] at this; exact lt_irrefl _ this
    exact le_antisymm (hopt π' π) (hopt π π')
  · intro h π
    exact regret_trivial U π e (fun π' => (h π' π).le)

/-! ## Non-vacuity: a concrete two-policy, two-level instance -/

/-- Toy: policies `Bool`, levels `Bool`.  Level `false` is impossible (everyone
scores 0); on level `true` policy `true` scores 1 and policy `false` scores 0. -/
noncomputable def toyU : Bool → Bool → ℝ := fun p e => if e && p then 1 else 0

/-- PROVED: the toy satisfies every hypothesis of `two_collapse_three_not` with a
positive-regret level, and level `true` is a positive regret-maximizer against
`π = false`, so `argmax_regret_subset` is not vacuous either. -/
theorem toy_nonvacuous :
    Impossible toyU false 0 ∧ 0 < regret toyU false true ∧
    (∀ e, regret toyU false e ≤ regret toyU false true) ∧
    ¬ ∀ e, regret toyU false e ≤ regret toyU false false := by
  have himp : Impossible toyU false 0 :=
    ⟨fun π => by simp [toyU], fun π e => by unfold toyU; split_ifs <;> norm_num⟩
  have hpos : 0 < regret toyU false true :=
    (regret_pos_iff toyU false true).2 ⟨true, by simp [toyU]⟩
  refine ⟨himp, hpos, ?_, ?_⟩
  · intro e; cases e
    · rw [regret_impossible toyU himp false]; exact hpos.le
    · exact le_rfl
  · exact (two_collapse_three_not toyU himp false).2 ⟨true, hpos⟩

end UED3
