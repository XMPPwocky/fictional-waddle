import Mathlib

/-!
# A04: Annihilation and amplification (proofs)

**What is proved (formal content).**
* (a) For states `(L, D) : ℕ × ℕ` with the annihilation relation `(L+1, D+1) → (L, D)`:
  the integer `L - D` is preserved by one annihilation and by any finite sequence
  (`Relation.ReflTransGen`) of them; a birth changes it by `±1`; a finite sequence of
  annihilations removes the same number `k` of each type; from `(L, D)` one can reach the
  terminal state `(L - min L D, D - min L D)`; and if `L ≠ D`, every terminal state
  (some coordinate `0`) reachable by annihilations alone is `(L - D, 0)` or `(0, D - L)`
  (majority type survives), with survivor count exactly `|L - D|` (and nonzero).
* (b) For the Frank vector field `fL = L(1-L-D) - μLD`, `fD = D(1-L-D) - μLD`:
  `fL - fD = (L-D)(1-L-D)` (polynomial identity); the quotient-rule expression for
  `d/dt ((L-D)/(L+D))` equals `2μLD(L-D)/(L+D)^2` whenever `L + D ≠ 0`; along any
  `C¹` curve satisfying the ODE pointwise (`HasDerivAt`), `L - D` and `ee` have these
  derivatives; for `μ > 0`, `L, D > 0`, the sign of the `ee`-rate equals the sign of `ee`;
  for `μ ≥ 0` and a solution staying in `L, D > 0` on `[a, b]` (or on all of `ℝ`),
  `|ee|` is monotone (nondecreasing).

**Interpretation (not formalised).** The discrete part models racemic annihilation
(e.g. heterochiral pairs precipitating / annihilating): annihilation cannot create or
destroy net handedness, it only removes the racemic background, so the relative
excess `ee` is amplified even though `L - D` is fixed. The Frank model is the classic
mutual-antagonism mechanism for spontaneous homochirality; `|ee|` nondecreasing is the
"amplification" statement. Positivity of `L, D` along the solution is *assumed* as a
hypothesis (it is in fact forward-invariant for this ODE, but that is not proved here),
and existence of solutions is not addressed: the theorems are about any curve that
satisfies the ODE. Note `|ee|` nondecreasing does not by itself say `|ee| → 1`.

**Review additions.** `annihs_ee_amplify` (discrete `|ee|` nondecreasing under annihilation,
and `|ee| = 1` at a terminal state from a non-racemic start) and concrete `example`s at the
end: a (5,2) run, and constant solutions (`μ = 1`, `L = D = 1/3`; `μ = 0`, `(1/4, 3/4)`)
that discharge every hypothesis of `abs_ee_monotone`. Caveat found in review: for `μ > 0`
the only constant solution in the open quadrant is racemic (`ee = 0`), so the explicit
`μ > 0` instance witnesses non-vacuity but not strict amplification; no explicit
non-constant `μ > 0` solution is given. The auxiliary `ee_hasDerivAt_at` was added to the
statements file so the two files list identical statements.
-/

namespace A04

/-! ## (a) Discrete annihilation -/

/-- A state: `(L, D)` counts of the two enantiomers. -/
abbrev State := ℕ × ℕ

/-- The conserved quantity `L - D` as an integer. -/
def excess (s : State) : ℤ := (s.1 : ℤ) - (s.2 : ℤ)

/-- One annihilation event: `(L+1, D+1) ↦ (L, D)`, as a relation `s → t`. -/
def Annih (s t : State) : Prop := s.1 = t.1 + 1 ∧ s.2 = t.2 + 1

/-- Birth of an `L`. -/
def birthL (s : State) : State := (s.1 + 1, s.2)

/-- Birth of a `D`. -/
def birthD (s : State) : State := (s.1, s.2 + 1)

/-- One annihilation preserves the integer excess `L - D`. -/
theorem annih_excess {s t : State} (h : Annih s t) : excess s = excess t := by
  obtain ⟨h1, h2⟩ := h
  unfold excess
  rw [h1, h2]
  push_cast
  ring

/-- From `(L+1, D+1)` the only annihilation target is `(L, D)`. -/
theorem annih_iff (L D : ℕ) (t : State) : Annih (L + 1, D + 1) t ↔ t = (L, D) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact Prod.ext (by simpa using h1.symm) (by simpa using h2.symm)
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- A birth of an `L` raises the excess by one. -/
theorem birthL_excess (s : State) : excess (birthL s) = excess s + 1 := by
  unfold excess birthL
  push_cast
  ring

/-- A birth of a `D` lowers the excess by one. -/
theorem birthD_excess (s : State) : excess (birthD s) = excess s - 1 := by
  unfold excess birthD
  push_cast
  ring

/-- Any finite sequence of annihilations (reflexive-transitive closure) preserves `L - D`. -/
theorem annihs_excess {s t : State} (h : Relation.ReflTransGen Annih s t) :
    excess s = excess t := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (annih_excess hbc)

/-- A finite sequence of annihilations removes the same number `k` of each type. -/
theorem annihs_total {s t : State} (h : Relation.ReflTransGen Annih s t) :
    ∃ k : ℕ, s.1 = t.1 + k ∧ s.2 = t.2 + k := by
  induction h with
  | refl => exact ⟨0, rfl, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨k, h1, h2⟩ := ih
    obtain ⟨g1, g2⟩ := hbc
    exact ⟨k + 1, by omega, by omega⟩

/-- `k` annihilations take `(L+k, D+k)` to `(L, D)`. -/
theorem annihs_of_add (L D k : ℕ) :
    Relation.ReflTransGen Annih (L + k, D + k) (L, D) := by
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih =>
    refine Relation.ReflTransGen.head (b := (L + k, D + k)) ?_ ih
    exact ⟨show L + (k + 1) = L + k + 1 by omega, show D + (k + 1) = D + k + 1 by omega⟩

/-- Annihilating `min L D` times reaches a terminal state (one count zero). -/
theorem annihs_reach_terminal (L D : ℕ) :
    Relation.ReflTransGen Annih (L, D) (L - min L D, D - min L D) ∧
      (L - min L D = 0 ∨ D - min L D = 0) := by
  refine ⟨?_, by omega⟩
  have := annihs_of_add (L - min L D) (D - min L D) (min L D)
  rwa [Nat.sub_add_cancel (min_le_left _ _), Nat.sub_add_cancel (min_le_right _ _)] at this

/-- If `D < L`, every terminal state reachable by annihilations is `(L - D, 0)`;
the survivors are all `L`, numbering `|L - D|`. -/
theorem survivor_L_majority {L D : ℕ} (hLD : D < L) {t : State}
    (h : Relation.ReflTransGen Annih (L, D) t) (hterm : t.1 = 0 ∨ t.2 = 0) :
    t = (L - D, 0) ∧ ((t.1 : ℤ) = |(L : ℤ) - D|) := by
  obtain ⟨k, h1, h2⟩ := annihs_total h
  simp only at h1 h2
  have ht2 : t.2 = 0 := by omega
  have ht1 : t.1 = L - D := by omega
  refine ⟨Prod.ext ht1 ht2, ?_⟩
  rw [ht1, Nat.cast_sub hLD.le, abs_of_nonneg (by omega)]

/-- If `L < D`, every terminal state reachable by annihilations is `(0, D - L)`;
the survivors are all `D`, numbering `|L - D|`. -/
theorem survivor_D_majority {L D : ℕ} (hLD : L < D) {t : State}
    (h : Relation.ReflTransGen Annih (L, D) t) (hterm : t.1 = 0 ∨ t.2 = 0) :
    t = (0, D - L) ∧ ((t.2 : ℤ) = |(L : ℤ) - D|) := by
  obtain ⟨k, h1, h2⟩ := annihs_total h
  simp only at h1 h2
  have ht1 : t.1 = 0 := by omega
  have ht2 : t.2 = D - L := by omega
  refine ⟨Prod.ext ht1 ht2, ?_⟩
  rw [ht2, Nat.cast_sub hLD.le, abs_of_nonpos (by omega)]
  ring

/-- If `L ≠ D`, any reachable terminal state has exactly `|L - D|` survivors (nonzero). -/
theorem survivor_count {L D : ℕ} (hLD : L ≠ D) {t : State}
    (h : Relation.ReflTransGen Annih (L, D) t) (hterm : t.1 = 0 ∨ t.2 = 0) :
    ((t.1 + t.2 : ℕ) : ℤ) = |(L : ℤ) - D| ∧ t.1 + t.2 ≠ 0 := by
  rcases Nat.lt_or_gt_of_ne hLD with hlt | hgt
  · obtain ⟨rfl, h2⟩ := survivor_D_majority hlt h hterm
    refine ⟨by simpa using h2, by simp; omega⟩
  · obtain ⟨rfl, h2⟩ := survivor_L_majority hgt h hterm
    refine ⟨by simpa using h2, by simp; omega⟩

/-! ## (b) Continuous Frank model -/

/-- `L'` component of the Frank vector field. -/
def fL (μ L D : ℝ) : ℝ := L * (1 - L - D) - μ * L * D

/-- `D'` component of the Frank vector field. -/
def fD (μ L D : ℝ) : ℝ := D * (1 - L - D) - μ * L * D

/-- Enantiomeric excess. -/
noncomputable def ee (L D : ℝ) : ℝ := (L - D) / (L + D)

/-- Vector-field identity: `L' - D' = (L - D)(1 - L - D)`. -/
theorem field_diff (μ L D : ℝ) : fL μ L D - fD μ L D = (L - D) * (1 - L - D) := by
  unfold fL fD
  ring

/-- Vector-field identity for the quotient-rule numerator of `ee = (L-D)/(L+D)`.
(The hypothesis `L + D ≠ 0` is not needed for the identity itself; it is kept so the
statement matches its use, where it is required for the quotient rule.) -/
theorem field_ee (μ L D : ℝ) (h : L + D ≠ 0) :
    ((fL μ L D - fD μ L D) * (L + D) - (L - D) * (fL μ L D + fD μ L D)) / (L + D) ^ 2
      = 2 * μ * L * D * (L - D) / (L + D) ^ 2 := by
  congr 1
  unfold fL fD
  ring

/-- Along a solution, `d/dt (L - D) = (L - D)(1 - L - D)`. -/
theorem sol_diff_hasDerivAt (μ : ℝ) (L D : ℝ → ℝ)
    (hL : ∀ t, HasDerivAt L (fL μ (L t) (D t)) t)
    (hD : ∀ t, HasDerivAt D (fD μ (L t) (D t)) t) (t : ℝ) :
    HasDerivAt (fun s => L s - D s) ((L t - D t) * (1 - L t - D t)) t := by
  have := (hL t).sub (hD t)
  rwa [field_diff] at this

/-- Pointwise version (auxiliary, not in the statements file): only the derivatives
at the single time `t` are needed. -/
theorem ee_hasDerivAt_at (μ : ℝ) (L D : ℝ → ℝ) (t : ℝ)
    (hL : HasDerivAt L (fL μ (L t) (D t)) t)
    (hD : HasDerivAt D (fD μ (L t) (D t)) t) (ht : L t + D t ≠ 0) :
    HasDerivAt (fun s => ee (L s) (D s))
      (2 * μ * L t * D t * (L t - D t) / (L t + D t) ^ 2) t := by
  have h := (hL.sub hD).div (hL.add hD) ht
  convert h using 1
  · funext s
    rfl
  · rw [← field_ee μ (L t) (D t) ht]
    rfl

/-- Along a solution with `L + D ≠ 0`, `d/dt ee = 2μLD(L-D)/(L+D)^2`. -/
theorem sol_ee_hasDerivAt (μ : ℝ) (L D : ℝ → ℝ)
    (hL : ∀ t, HasDerivAt L (fL μ (L t) (D t)) t)
    (hD : ∀ t, HasDerivAt D (fD μ (L t) (D t)) t) (t : ℝ) (ht : L t + D t ≠ 0) :
    HasDerivAt (fun s => ee (L s) (D s))
      (2 * μ * L t * D t * (L t - D t) / (L t + D t) ^ 2) t := by
  exact ee_hasDerivAt_at μ L D t (hL t) (hD t) ht

/-- For `μ > 0` and `L, D > 0`, the `ee`-rate has the same sign as `ee`. -/
theorem ee_rate_sign {μ L D : ℝ} (hμ : 0 < μ) (hL : 0 < L) (hD : 0 < D) :
    SignType.sign (2 * μ * L * D * (L - D) / (L + D) ^ 2) = SignType.sign (ee L D) := by
  have hc : 0 < 2 * μ * L * D / (L + D) := by positivity
  have hS : L + D ≠ 0 := by positivity
  have : 2 * μ * L * D * (L - D) / (L + D) ^ 2 = ee L D * (2 * μ * L * D / (L + D)) := by
    unfold ee
    field_simp
  rw [this, sign_mul, sign_pos hc, mul_one]

/-- For `μ ≥ 0` and `L, D > 0`, `ee · (d/dt ee) ≥ 0`. -/
theorem ee_mul_rate_nonneg {μ L D : ℝ} (hμ : 0 ≤ μ) (hL : 0 < L) (hD : 0 < D) :
    0 ≤ ee L D * (2 * μ * L * D * (L - D) / (L + D) ^ 2) := by
  have hS : L + D ≠ 0 := by positivity
  have : ee L D * (2 * μ * L * D * (L - D) / (L + D) ^ 2)
      = 2 * μ * L * D * (L - D) ^ 2 / (L + D) ^ 3 := by
    unfold ee
    field_simp
  rw [this]
  have := hL.le
  have := hD.le
  positivity

/-- If the ODE holds and `L, D > 0` at every point of `[a, b]` (`μ ≥ 0`), `|ee|` is
monotone on `[a, b]`. -/
theorem abs_ee_monotoneOn (μ : ℝ) (hμ : 0 ≤ μ) (L D : ℝ → ℝ) (a b : ℝ)
    (hL : ∀ t ∈ Set.Icc a b, HasDerivAt L (fL μ (L t) (D t)) t)
    (hD : ∀ t ∈ Set.Icc a b, HasDerivAt D (fD μ (L t) (D t)) t)
    (hpos : ∀ t ∈ Set.Icc a b, 0 < L t ∧ 0 < D t) :
    MonotoneOn (fun t => |ee (L t) (D t)|) (Set.Icc a b) := by
  -- the square `ee^2` has nonnegative derivative on the interval
  set g : ℝ → ℝ := fun t => ee (L t) (D t) with hg
  have hder : ∀ t ∈ Set.Icc a b, HasDerivAt (fun s => g s * g s)
      (2 * (ee (L t) (D t) * (2 * μ * L t * D t * (L t - D t) / (L t + D t) ^ 2))) t := by
    intro t ht
    have hS : L t + D t ≠ 0 := by have := hpos t ht; linarith
    have h1 := ee_hasDerivAt_at μ L D t (hL t ht) (hD t ht) hS
    have h2 := h1.mul h1
    convert h2 using 1
    ring
  have hsq : MonotoneOn (fun s => g s * g s) (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro t ht
      exact (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hder t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht' := Set.Ioo_subset_Icc_self ht
      rw [(hder t ht').deriv]
      have := ee_mul_rate_nonneg hμ (hpos t ht').1 (hpos t ht').2
      linarith
  intro x hx y hy hxy
  have := hsq hx hy hxy
  simp only at this
  show |g x| ≤ |g y|
  rw [← sq_le_sq]
  nlinarith [this]

/-- If the ODE holds and `L, D > 0` for all times (`μ ≥ 0`), `|ee|` is monotone. -/
theorem abs_ee_monotone (μ : ℝ) (hμ : 0 ≤ μ) (L D : ℝ → ℝ)
    (hL : ∀ t, HasDerivAt L (fL μ (L t) (D t)) t)
    (hD : ∀ t, HasDerivAt D (fD μ (L t) (D t)) t)
    (hpos : ∀ t, 0 < L t ∧ 0 < D t) :
    Monotone (fun t => |ee (L t) (D t)|) := by
  intro a b hab
  exact abs_ee_monotoneOn μ hμ L D a b (fun t _ => hL t) (fun t _ => hD t)
    (fun t _ => hpos t) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab


/-! ## Added by the adversarial review (going up: discrete amplification) -/

/-- **Discrete amplification (added in review).** Along any finite sequence of
annihilations `s →* t`, the enantiomeric excess `|ee| = |L - D| / (L + D)` (computed in
`ℝ`, with Lean's `x / 0 = 0` convention, which only matters at `(0, 0)`) does not decrease;
and if the start is non-racemic (`s.1 ≠ s.2`) and `t` is terminal (one count zero), then
`|ee t| = 1` (homochirality). Proved: exactly this. Interpretation: annihilation removes
only the racemic background, so the relative excess grows, the discrete analogue of
`abs_ee_monotone`. -/
theorem annihs_ee_amplify {s t : State} (h : Relation.ReflTransGen Annih s t) :
    |ee (s.1 : ℝ) s.2| ≤ |ee (t.1 : ℝ) t.2| ∧
      ((t.1 = 0 ∨ t.2 = 0) → s.1 ≠ s.2 → |ee (t.1 : ℝ) t.2| = 1) := by
  obtain ⟨k, h1, h2⟩ := annihs_total h
  constructor
  · rw [h1, h2]
    unfold ee
    push_cast
    have ha : (0 : ℝ) ≤ t.1 := Nat.cast_nonneg _
    have hb : (0 : ℝ) ≤ t.2 := Nat.cast_nonneg _
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have e1 : (t.1 : ℝ) + k - (t.2 + k) = t.1 - t.2 := by ring
    rw [e1]
    rcases eq_or_lt_of_le (add_nonneg ha hb) with h0 | hpos
    · have e2 : (t.1 : ℝ) = 0 := by linarith
      have e3 : (t.2 : ℝ) = 0 := by linarith
      rw [e2, e3]
      norm_num
    · have hpos' : (0 : ℝ) < t.1 + k + (t.2 + k) := by linarith
      rw [abs_div, abs_div, abs_of_pos hpos, abs_of_pos hpos']
      exact div_le_div_of_nonneg_left (abs_nonneg _) hpos (by linarith)
  · intro hterm hne
    have hne' : t.1 ≠ t.2 := by omega
    unfold ee
    rcases hterm with h0 | h0
    · rw [h0] at hne' ⊢
      have : (0 : ℝ) < t.2 := by exact_mod_cast Nat.pos_of_ne_zero (Ne.symm hne')
      rw [Nat.cast_zero, zero_sub, zero_add, neg_div, div_self this.ne', abs_neg, abs_one]
    · rw [h0] at hne' ⊢
      have : (0 : ℝ) < t.1 := by exact_mod_cast Nat.pos_of_ne_zero hne'
      rw [Nat.cast_zero, sub_zero, add_zero, div_self this.ne', abs_one]

/-! ## Concrete instances (added in review; they show the hypotheses are satisfiable) -/

-- Two annihilations take (5,2) to (3,0).

example : Relation.ReflTransGen Annih (5, 2) (3, 0) := annihs_of_add 3 0 2

-- Every terminal state reachable from (5,2) is (3,0): three L survivors.
example {t : State} (h : Relation.ReflTransGen Annih (5, 2) t) (hterm : t.1 = 0 ∨ t.2 = 0) :
    t = (3, 0) ∧ t.1 + t.2 = 3 := by
  obtain ⟨h1, -⟩ := survivor_L_majority (by norm_num) h hterm
  subst h1
  norm_num

-- Discrete amplification on this run: |ee| goes from 3/7 to 1.
example : |ee ((5 : ℕ) : ℝ) ((2 : ℕ) : ℝ)| = 3 / 7 ∧ |ee ((3 : ℕ) : ℝ) ((0 : ℕ) : ℝ)| = 1 := by
  unfold ee; norm_num [abs_of_pos]

-- The racemic fixed point L = D = 1/(2+μ) at μ = 1.
example : fL 1 (1/3) (1/3) = 0 ∧ fD 1 (1/3) (1/3) = 0 := by unfold fL fD; norm_num

-- `abs_ee_monotone` instantiated with μ = 1 and the constant solution L = D = 1/3
-- (all hypotheses are discharged, so they are not vacuous for μ > 0).
example : Monotone (fun t : ℝ => |ee ((fun _ => (1/3 : ℝ)) t) ((fun _ => (1/3 : ℝ)) t)|) :=
  abs_ee_monotone 1 zero_le_one (fun _ => 1/3) (fun _ => 1/3)
    (fun t => by
      have : fL 1 (1/3) (1/3) = 0 := by unfold fL; norm_num
      show HasDerivAt (fun _ => (1/3 : ℝ)) (fL 1 (1/3) (1/3)) t
      rw [this]; exact hasDerivAt_const t _)
    (fun t => by
      have : fD 1 (1/3) (1/3) = 0 := by unfold fD; norm_num
      show HasDerivAt (fun _ => (1/3 : ℝ)) (fD 1 (1/3) (1/3)) t
      rw [this]; exact hasDerivAt_const t _)
    (fun _ => by norm_num)

-- `abs_ee_monotone` instantiated with μ = 0 and the non-racemic constant solution
-- (L, D) = (1/4, 3/4) on the line L + D = 1.
example : Monotone (fun t : ℝ => |ee ((fun _ => (1/4 : ℝ)) t) ((fun _ => (3/4 : ℝ)) t)|) :=
  abs_ee_monotone 0 le_rfl (fun _ => 1/4) (fun _ => 3/4)
    (fun t => by
      have : fL 0 (1/4) (3/4) = 0 := by unfold fL; norm_num
      show HasDerivAt (fun _ => (1/4 : ℝ)) (fL 0 (1/4) (3/4)) t
      rw [this]; exact hasDerivAt_const t _)
    (fun t => by
      have : fD 0 (1/4) (3/4) = 0 := by unfold fD; norm_num
      show HasDerivAt (fun _ => (3/4 : ℝ)) (fD 0 (1/4) (3/4)) t
      rw [this]; exact hasDerivAt_const t _)
    (fun _ => by norm_num)

-- The ee-rate at μ = 1, (L, D) = (1/2, 1/4) is 1/9 > 0, with sign agreeing with ee > 0.
example : 2 * (1 : ℝ) * (1/2) * (1/4) * (1/2 - 1/4) / (1/2 + 1/4) ^ 2 = 1/9 ∧
    SignType.sign (2 * (1 : ℝ) * (1/2) * (1/4) * (1/2 - 1/4) / (1/2 + 1/4) ^ 2) = 1 := by
  refine ⟨by norm_num, ?_⟩
  rw [ee_rate_sign (by norm_num) (by norm_num) (by norm_num)]
  unfold ee; norm_num

end A04
