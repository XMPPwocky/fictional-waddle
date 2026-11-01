import Mathlib

/-!
# Scale and shift invariance of the Nash bargaining solution

Setting: a type of options `X`, `n` players, utilities `u i : X → ℝ`, disagreement
points `d i : ℝ`. An option `x` is feasible when every gain `u i x - d i` is positive.
The Nash welfare is `W u d x = ∑ i, log (u i x - d i)`. A Nash maximizer is a feasible
option whose welfare is at least that of every feasible option.

PROVED:
* `welfare_scale`: for `c i > 0`, rescaling `u i ↦ c i * u i`, `d i ↦ c i * d i` adds the
  constant `∑ i, log (c i)` to `W` at every feasible option.
* `feasible_scale_iff`: rescaling by positive constants preserves feasibility.
* `isNashMax_scale_iff`, `nashMax_set_scale`: the set of Nash maximizers is unchanged by
  positive rescaling.
* `welfare_shift`, `feasible_shift_iff`, `isNashMax_shift_iff`: shifting `u i` and `d i` by
  the same constant `s i` leaves `W` unchanged at every option, preserves feasibility, and
  leaves the set of Nash maximizers unchanged.
* `utilitarian_not_scale_invariant`: an explicit two-player, two-option example
  (`d = 0`; option `0` gives utilities `(2, 1)`, option `1` gives `(1, 3)`; player `0`
  rescaled by `c = 10`) in which the unique utilitarian maximizer moves from option `1`
  to option `0`, while option `1` is the unique Nash maximizer both before and after.

INTERPRETED:
* "The set of maximizers" is read as the set of feasible options maximizing `W` over the
  feasible options; infeasible options (some gain `≤ 0`) are excluded, as in the target.
* The finite-set hypothesis on `X` is not needed for the invariance statements; it matters
  only for existence of a maximizer, which is not claimed.
-/

namespace NashProductScaleInvariantB

open Real

variable {X : Type*} {n : ℕ}

/-- Every player strictly gains over the disagreement point. -/
def Feasible (u : Fin n → X → ℝ) (d : Fin n → ℝ) (x : X) : Prop :=
  ∀ i, d i < u i x

/-- Nash welfare: the sum of log gains. -/
noncomputable def W (u : Fin n → X → ℝ) (d : Fin n → ℝ) (x : X) : ℝ :=
  ∑ i, Real.log (u i x - d i)

/-- `x` maximizes Nash welfare over the feasible options. -/
def IsNashMax (u : Fin n → X → ℝ) (d : Fin n → ℝ) (x : X) : Prop :=
  Feasible u d x ∧ ∀ y, Feasible u d y → W u d y ≤ W u d x

/-- Utilitarian welfare. -/
def U (u : Fin n → X → ℝ) (x : X) : ℝ := ∑ i, u i x

/-- `x` maximizes utilitarian welfare over all options. -/
def IsUtilMax (u : Fin n → X → ℝ) (x : X) : Prop := ∀ y, U u y ≤ U u x

/-- Positive rescaling of utilities. -/
def scaleU (c : Fin n → ℝ) (u : Fin n → X → ℝ) : Fin n → X → ℝ := fun i x => c i * u i x

/-- Positive rescaling of disagreement points. -/
def scaleD (c : Fin n → ℝ) (d : Fin n → ℝ) : Fin n → ℝ := fun i => c i * d i

theorem feasible_scale_iff (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (u : Fin n → X → ℝ) (d : Fin n → ℝ) (x : X) :
    Feasible (scaleU c u) (scaleD c d) x ↔ Feasible u d x := by
  unfold Feasible scaleU scaleD
  exact forall_congr' fun i => mul_lt_mul_iff_of_pos_left (hc i)

theorem welfare_scale (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (u : Fin n → X → ℝ) (d : Fin n → ℝ) (x : X) (hx : Feasible u d x) :
    W (scaleU c u) (scaleD c d) x = W u d x + ∑ i, Real.log (c i) := by
  unfold W scaleU scaleD
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : c i * u i x - c i * d i = c i * (u i x - d i) := by ring
  rw [h1, Real.log_mul (hc i).ne' (sub_pos.mpr (hx i)).ne', add_comm]

theorem isNashMax_scale_iff (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (u : Fin n → X → ℝ) (d : Fin n → ℝ) (x : X) :
    IsNashMax (scaleU c u) (scaleD c d) x ↔ IsNashMax u d x := by
  unfold IsNashMax
  simp only [feasible_scale_iff c hc]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun y hy => ?_⟩
    have := h y hy
    rw [welfare_scale c hc u d y hy, welfare_scale c hc u d x hx] at this
    linarith
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun y hy => ?_⟩
    rw [welfare_scale c hc u d y hy, welfare_scale c hc u d x hx]
    linarith [h y hy]

/-- The maximizer set is unchanged by positive rescaling. -/
theorem nashMax_set_scale (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (u : Fin n → X → ℝ) (d : Fin n → ℝ) :
    {x | IsNashMax (scaleU c u) (scaleD c d) x} = {x | IsNashMax u d x} :=
  Set.ext fun x => isNashMax_scale_iff c hc u d x

/-- Shift of utilities. -/
def shiftU (s : Fin n → ℝ) (u : Fin n → X → ℝ) : Fin n → X → ℝ := fun i x => u i x + s i

/-- Shift of disagreement points. -/
def shiftD (s : Fin n → ℝ) (d : Fin n → ℝ) : Fin n → ℝ := fun i => d i + s i

theorem welfare_shift (s : Fin n → ℝ) (u : Fin n → X → ℝ) (d : Fin n → ℝ) (x : X) :
    W (shiftU s u) (shiftD s d) x = W u d x := by
  unfold W shiftU shiftD
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring

theorem feasible_shift_iff (s : Fin n → ℝ) (u : Fin n → X → ℝ) (d : Fin n → ℝ) (x : X) :
    Feasible (shiftU s u) (shiftD s d) x ↔ Feasible u d x := by
  unfold Feasible shiftU shiftD
  exact forall_congr' fun i => add_lt_add_iff_right (s i)

theorem isNashMax_shift_iff (s : Fin n → ℝ) (u : Fin n → X → ℝ) (d : Fin n → ℝ) (x : X) :
    IsNashMax (shiftU s u) (shiftD s d) x ↔ IsNashMax u d x := by
  unfold IsNashMax
  simp only [feasible_shift_iff, welfare_shift]

/-! ### The utilitarian counterexample -/

/-- Two players, two options: option `0` gives `(2, 1)`, option `1` gives `(1, 3)`. -/
def exU : Fin 2 → Fin 2 → ℝ := ![![2, 1], ![1, 3]]

/-- Disagreement point zero. -/
def exD : Fin 2 → ℝ := ![0, 0]

/-- Rescale player `0` by `10`, player `1` by `1`. -/
def exC : Fin 2 → ℝ := ![10, 1]

theorem exC_pos : ∀ i, 0 < exC i := by
  intro i; fin_cases i <;> norm_num [exC]

theorem ex_feasible (x : Fin 2) : Feasible exU exD x := by
  intro i; fin_cases i <;> fin_cases x <;> norm_num [exU, exD]

theorem ex_W0 : W exU exD 0 = Real.log 2 := by
  simp [W, exU, exD, Fin.sum_univ_two]

theorem ex_W1 : W exU exD 1 = Real.log 3 := by
  simp [W, exU, exD, Fin.sum_univ_two]

/-- Before rescaling, option `1` is the unique Nash maximizer. -/
theorem ex_nash_before (x : Fin 2) : IsNashMax exU exD x ↔ x = 1 := by
  have hlt : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  constructor
  · rintro ⟨_, h⟩
    by_contra hx
    have hx0 : x = 0 := by fin_cases x <;> simp_all
    subst hx0
    have := h 1 (ex_feasible 1)
    rw [ex_W0, ex_W1] at this
    linarith
  · rintro rfl
    refine ⟨ex_feasible 1, fun y _ => ?_⟩
    fin_cases y
    · show W exU exD 0 ≤ W exU exD 1
      rw [ex_W0, ex_W1]; exact hlt.le
    · exact le_rfl

/-- After rescaling player `0` by `10`, option `1` is still the unique Nash maximizer. -/
theorem ex_nash_after (x : Fin 2) :
    IsNashMax (scaleU exC exU) (scaleD exC exD) x ↔ x = 1 := by
  rw [isNashMax_scale_iff exC exC_pos]
  exact ex_nash_before x

/-- Before rescaling, option `1` is the unique utilitarian maximizer (sums `3` vs `4`). -/
theorem ex_util_before (x : Fin 2) : IsUtilMax exU x ↔ x = 1 := by
  constructor
  · intro h
    by_contra hx
    have hx0 : x = 0 := by fin_cases x <;> simp_all
    subst hx0
    have := h 1
    simp [U, exU, Fin.sum_univ_two] at this
    norm_num at this
  · rintro rfl y
    fin_cases y <;> norm_num [U, exU, Fin.sum_univ_two]

/-- After rescaling, option `0` is the unique utilitarian maximizer (sums `21` vs `13`). -/
theorem ex_util_after (x : Fin 2) : IsUtilMax (scaleU exC exU) x ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    have hx1 : x = 1 := by fin_cases x <;> simp_all
    subst hx1
    have := h 0
    simp [U, scaleU, exU, exC, Fin.sum_univ_two] at this
    norm_num at this
  · rintro rfl y
    fin_cases y <;> norm_num [U, scaleU, exU, exC, Fin.sum_univ_two]

/-- Rescaling one player's utility changes the utilitarian maximizer but not the Nash
maximizer. -/
theorem utilitarian_not_scale_invariant :
    (∀ i, 0 < exC i) ∧ exC 1 = 1 ∧
    (∀ x, IsUtilMax exU x ↔ x = 1) ∧
    (∀ x, IsUtilMax (scaleU exC exU) x ↔ x = 0) ∧
    (∀ x, IsNashMax exU exD x ↔ x = 1) ∧
    (∀ x, IsNashMax (scaleU exC exU) (scaleD exC exD) x ↔ x = 1) :=
  ⟨exC_pos, by simp [exC], ex_util_before, ex_util_after, ex_nash_before, ex_nash_after⟩

end NashProductScaleInvariantB
