import Mathlib

/-!
# Scale and shift invariance of the Nash product

Setting: a type `X` of options, a finite type `ι` of players, utilities
`u : ι → X → ℝ` and disagreement points `d : ι → ℝ`. An option `x` is feasible when
every gain `u i x - d i` is strictly positive. The Nash welfare is
`W u d x = ∑ i, log (u i x - d i)`. A Nash maximizer on a set of options `S` is a
feasible `x ∈ S` with `W u d y ≤ W u d x` for every feasible `y ∈ S`.

PROVED
* `feasible_scale_iff`: for `c i > 0`, `x` is feasible for `(c • u, c • d)` iff it is
  feasible for `(u, d)`.
* `nashWelfare_scale`: on feasible options,
  `W (c • u) (c • d) x = W u d x + ∑ i, log (c i)`.
* `isNashMax_scale_iff`: the set of Nash maximizers is unchanged by any per-player
  rescaling `c i > 0` of utility and disagreement point.
* `feasible_shift_iff`, `nashWelfare_shift`, `isNashMax_shift_iff`: adding the same
  constant `k i` to `u i` and `d i` leaves feasibility, `W` (at every option) and the
  set of Nash maximizers unchanged.
* `utilitarian_not_scale_invariant`: an explicit two-player, two-option example with
  `d = 0` where rescaling player 1 by `c = 10` moves the unique utilitarian maximizer
  from option 0 to option 1, while option 0 is the unique Nash maximizer both before and
  after the rescaling.

INTERPRETED
* "Restricted to options where every gain is positive" is the predicate `Feasible`;
  maximizers are taken over feasible options in a set `S` (for the theorem, any
  `S : Set X`, finite or not; finiteness of `X` is not needed).
* "Set of maximizers is unchanged" is the pointwise equivalence of `IsNashMax`.
* Example: `u 0 = (3, 1)`, `u 1 = (1, 2)` over options `(0, 1)`, `d = (0, 0)`;
  rescaled `u 1 = (10, 20)`. Utilitarian sums: `(4, 3)` before, `(13, 21)` after.
  Nash welfares: `(log 3, log 2)` before, `(log 30, log 20)` after.
-/

namespace NashProductScaleInvariantA

open Real Finset

variable {ι X : Type*} [Fintype ι]

/-- Every player's gain over the disagreement point is strictly positive at `x`. -/
def Feasible (u : ι → X → ℝ) (d : ι → ℝ) (x : X) : Prop :=
  ∀ i, 0 < u i x - d i

/-- Nash welfare: the sum of log gains. -/
noncomputable def nashWelfare (u : ι → X → ℝ) (d : ι → ℝ) (x : X) : ℝ :=
  ∑ i, Real.log (u i x - d i)

/-- `x` maximizes Nash welfare among feasible options of `S`. -/
def IsNashMax (u : ι → X → ℝ) (d : ι → ℝ) (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ Feasible u d x ∧
    ∀ y ∈ S, Feasible u d y → nashWelfare u d y ≤ nashWelfare u d x

/-- Utilitarian welfare: the plain sum of utilities. -/
def utilitarian (u : ι → X → ℝ) (x : X) : ℝ := ∑ i, u i x

/-- `x` maximizes utilitarian welfare over `S`. -/
def IsUtilMax (u : ι → X → ℝ) (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, utilitarian u y ≤ utilitarian u x

/-- Rescaled utilities `u i ↦ c i * u i`. -/
def scaleU (c : ι → ℝ) (u : ι → X → ℝ) : ι → X → ℝ := fun i x => c i * u i x

/-- Rescaled disagreement points `d i ↦ c i * d i`. -/
def scaleD (c : ι → ℝ) (d : ι → ℝ) : ι → ℝ := fun i => c i * d i

/-- Shifted utilities `u i ↦ u i + k i`. -/
def shiftU (k : ι → ℝ) (u : ι → X → ℝ) : ι → X → ℝ := fun i x => u i x + k i

/-- Shifted disagreement points `d i ↦ d i + k i`. -/
def shiftD (k : ι → ℝ) (d : ι → ℝ) : ι → ℝ := fun i => d i + k i

omit [Fintype ι] in
lemma scale_gain (c : ι → ℝ) (u : ι → X → ℝ) (d : ι → ℝ) (i : ι) (x : X) :
    scaleU c u i x - scaleD c d i = c i * (u i x - d i) := by
  simp [scaleU, scaleD]; ring

omit [Fintype ι] in
theorem feasible_scale_iff {c : ι → ℝ} (hc : ∀ i, 0 < c i) (u : ι → X → ℝ) (d : ι → ℝ)
    (x : X) : Feasible (scaleU c u) (scaleD c d) x ↔ Feasible u d x := by
  unfold Feasible
  refine forall_congr' fun i => ?_
  rw [scale_gain]
  exact mul_pos_iff_of_pos_left (hc i)

theorem nashWelfare_scale {c : ι → ℝ} (hc : ∀ i, 0 < c i) (u : ι → X → ℝ) (d : ι → ℝ)
    {x : X} (hx : Feasible u d x) :
    nashWelfare (scaleU c u) (scaleD c d) x = nashWelfare u d x + ∑ i, Real.log (c i) := by
  unfold nashWelfare
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [scale_gain, Real.log_mul (hc i).ne' (hx i).ne', add_comm]

theorem isNashMax_scale_iff {c : ι → ℝ} (hc : ∀ i, 0 < c i) (u : ι → X → ℝ) (d : ι → ℝ)
    (S : Set X) (x : X) :
    IsNashMax (scaleU c u) (scaleD c d) S x ↔ IsNashMax u d S x := by
  unfold IsNashMax
  rw [feasible_scale_iff hc]
  constructor
  · rintro ⟨hS, hx, h⟩
    refine ⟨hS, hx, fun y hy hfy => ?_⟩
    have := h y hy ((feasible_scale_iff hc u d y).2 hfy)
    rw [nashWelfare_scale hc u d hfy, nashWelfare_scale hc u d hx] at this
    linarith
  · rintro ⟨hS, hx, h⟩
    refine ⟨hS, hx, fun y hy hfy => ?_⟩
    have hfy' := (feasible_scale_iff hc u d y).1 hfy
    rw [nashWelfare_scale hc u d hfy', nashWelfare_scale hc u d hx]
    linarith [h y hy hfy']

omit [Fintype ι] in
lemma shift_gain (k : ι → ℝ) (u : ι → X → ℝ) (d : ι → ℝ) (i : ι) (x : X) :
    shiftU k u i x - shiftD k d i = u i x - d i := by
  simp [shiftU, shiftD]

omit [Fintype ι] in
theorem feasible_shift_iff (k : ι → ℝ) (u : ι → X → ℝ) (d : ι → ℝ) (x : X) :
    Feasible (shiftU k u) (shiftD k d) x ↔ Feasible u d x := by
  simp only [Feasible, shift_gain]

theorem nashWelfare_shift (k : ι → ℝ) (u : ι → X → ℝ) (d : ι → ℝ) (x : X) :
    nashWelfare (shiftU k u) (shiftD k d) x = nashWelfare u d x := by
  simp only [nashWelfare, shift_gain]

theorem isNashMax_shift_iff (k : ι → ℝ) (u : ι → X → ℝ) (d : ι → ℝ) (S : Set X) (x : X) :
    IsNashMax (shiftU k u) (shiftD k d) S x ↔ IsNashMax u d S x := by
  simp only [IsNashMax, feasible_shift_iff, nashWelfare_shift]

/-! ## The utilitarian counterexample -/

/-- Example utilities: player 0 gets `(3, 1)`, player 1 gets `(1, 2)` on options `(0, 1)`. -/
def exU : Fin 2 → Fin 2 → ℝ := ![![3, 1], ![1, 2]]

/-- Zero disagreement points. -/
def exD : Fin 2 → ℝ := fun _ => 0

/-- Rescale player 1 by `10`, player 0 by `1`. -/
def exC : Fin 2 → ℝ := ![1, 10]

lemma exC_pos : ∀ i, 0 < exC i := by
  intro i; fin_cases i <;> simp [exC]

lemma ex_feasible (x : Fin 2) : Feasible exU exD x := by
  intro i; fin_cases i <;> fin_cases x <;> simp [exU, exD]

lemma ex_nash0 : nashWelfare exU exD 0 = Real.log 3 := by
  simp [nashWelfare, exU, exD, Fin.sum_univ_two]

lemma ex_nash1 : nashWelfare exU exD 1 = Real.log 2 := by
  simp [nashWelfare, exU, exD, Fin.sum_univ_two]

lemma ex_util_before (y : Fin 2) : utilitarian exU y ≤ utilitarian exU 0 := by
  fin_cases y <;> norm_num [utilitarian, exU, Fin.sum_univ_two]

lemma ex_util_after (y : Fin 2) :
    utilitarian (scaleU exC exU) y ≤ utilitarian (scaleU exC exU) 1 := by
  fin_cases y <;> norm_num [utilitarian, scaleU, exU, exC, Fin.sum_univ_two]

lemma ex_isNashMax0 : IsNashMax exU exD Set.univ 0 := by
  refine ⟨Set.mem_univ _, ex_feasible 0, fun y _ _ => ?_⟩
  fin_cases y
  · exact le_rfl
  · show nashWelfare exU exD 1 ≤ nashWelfare exU exD 0
    rw [ex_nash0, ex_nash1]
    exact Real.log_le_log (by norm_num) (by norm_num)

lemma ex_not_isNashMax1 : ¬ IsNashMax exU exD Set.univ 1 := by
  rintro ⟨_, _, h⟩
  have := h 0 (Set.mem_univ _) (ex_feasible 0)
  rw [ex_nash0, ex_nash1] at this
  have : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- In the example, utilitarian welfare is not scale invariant while Nash welfare is:
before rescaling, option 0 is the unique utilitarian maximizer; after rescaling player 1
by `10`, option 1 is the unique utilitarian maximizer; option 0 is the unique Nash
maximizer both before and after. -/
theorem utilitarian_not_scale_invariant :
    (∀ x : Fin 2, IsUtilMax exU Set.univ x ↔ x = 0) ∧
    (∀ x : Fin 2, IsUtilMax (scaleU exC exU) Set.univ x ↔ x = 1) ∧
    (∀ x : Fin 2, IsNashMax exU exD Set.univ x ↔ x = 0) ∧
    (∀ x : Fin 2, IsNashMax (scaleU exC exU) (scaleD exC exD) Set.univ x ↔ x = 0) := by
  have hnash : ∀ x : Fin 2, IsNashMax exU exD Set.univ x ↔ x = 0 := by
    intro x
    fin_cases x
    · simpa using ex_isNashMax0
    · simpa using ex_not_isNashMax1
  refine ⟨?_, ?_, hnash, ?_⟩
  · intro x
    fin_cases x
    · exact iff_of_true ⟨Set.mem_univ _, fun y _ => ex_util_before y⟩ rfl
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, iff_false]
      rintro ⟨_, h⟩
      have := h 0 (Set.mem_univ _)
      simp [utilitarian, exU, Fin.sum_univ_two] at this
      norm_num at this
  · intro x
    fin_cases x
    · simp only [Fin.zero_eta, Fin.isValue, zero_ne_one, iff_false]
      rintro ⟨_, h⟩
      have := h 1 (Set.mem_univ _)
      simp [utilitarian, scaleU, exU, exC, Fin.sum_univ_two] at this
      norm_num at this
    · exact iff_of_true ⟨Set.mem_univ _, fun y _ => ex_util_after y⟩ rfl
  · intro x
    rw [isNashMax_scale_iff exC_pos]
    exact hnash x

end NashProductScaleInvariantA
