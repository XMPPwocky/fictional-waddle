import Mathlib

/-!
# Contrarian diagonal and randomized rescue

PROVED
* `exists_eq_iff_isFixedPt`: for any `c : S → S`, `(∃ g, c g = g)` holds iff `c` has a fixed
  point in the sense of `Function.IsFixedPt` (definitional).
* `bool_not_no_fixedPt`: there is no `g : Bool` with `g = !g`.
* `bool_not_fixedPointFree`: `Bool.not` has no fixed point (`¬ ∃ g, Function.IsFixedPt not g`).
* `contrarian_defeats_bool`: for every announced prediction `g : Bool`, the contrarian outcome
  `y = !g` satisfies `g ≠ y`.
* `contrarian_defeats`: for any type `S` and fixed-point-free `c : S → S`, for every announced
  prediction `predict : S`, the outcome `c predict` differs from `predict`.
* `contrarian_defeats_all_predictors`: for fixed-point-free `c`, no predictor function
  `predict : α → S` is correct on any input, i.e. `∀ a, c (predict a) ≠ predict a`.
* `no_two_deterministic_predictors`: there are no `p q : Bool` with `p = q` (P correctly
  predicts Q) and `q = !p` (Q contrarian to P).
* `mixed_not_fixedPt_iff`: for real `p`, `1 - p = p ↔ p = 1/2`.
* `randomized_rescue`: there is a unique `p ∈ Set.Icc (0:ℝ) 1` with `1 - p = p`.
* `randomized_rescue_eq_half`: the set of `p ∈ [0,1]` with `1 - p = p` is exactly `{1/2}`.
* `mixed_not_maps_Icc`: `p ↦ 1 - p` maps `[0,1]` into itself, so it is a self-map of the
  mixed-strategy space; `mixedNot` is that self-map of `Set.Icc 0 1`.
* `mixed_not_unique_fixedPt`: `mixedNot` has exactly one fixed point.
* `mixed_not_isFixedPt_iff`: a point of `[0,1]` is fixed by `mixedNot` iff it equals `1/2`.

INTERPRETED (not formalized)
* Reading `Bool` outputs as deterministic predictions/actions and `p ∈ [0,1]` as the probability
  of outputting `true`, so that `p ↦ 1 - p` is the mixed extension of `Bool.not`.
-/

namespace ContrarianDiagonalAndRescue

/-- `∃ g, c g = g` is definitionally the existence of a fixed point. -/
theorem exists_eq_iff_isFixedPt {S : Type*} (c : S → S) :
    (∃ g, c g = g) ↔ ∃ g, Function.IsFixedPt c g :=
  Iff.rfl

/-- No Boolean equals its own negation. -/
theorem bool_not_no_fixedPt : ¬ ∃ g : Bool, g = !g := by
  rintro ⟨g, hg⟩
  cases g <;> simp at hg

/-- `Bool.not` has no fixed point. -/
theorem bool_not_fixedPointFree : ¬ ∃ g : Bool, Function.IsFixedPt (fun b : Bool => !b) g := by
  rintro ⟨g, hg⟩
  exact bool_not_no_fixedPt ⟨g, hg.symm⟩

/-- A contrarian replying `y = !g` to an announced prediction `g` makes the prediction wrong. -/
theorem contrarian_defeats_bool (g y : Bool) (hy : y = !g) : g ≠ y := by
  subst hy
  cases g <;> simp

/-- For a fixed-point-free contrarian `c`, every announced prediction is wrong. -/
theorem contrarian_defeats {S : Type*} (c : S → S) (hc : ∀ x, c x ≠ x) (predict : S) :
    c predict ≠ predict :=
  hc predict

/-- For a fixed-point-free contrarian `c`, no predictor is right on any input. -/
theorem contrarian_defeats_all_predictors {α S : Type*} (c : S → S) (hc : ¬ ∃ x, c x = x)
    (predict : α → S) : ∀ a, c (predict a) ≠ predict a := by
  intro a h
  exact hc ⟨predict a, h⟩

/-- There are no deterministic `p q : Bool` with `p = q` and `q = !p`. -/
theorem no_two_deterministic_predictors : ¬ ∃ p q : Bool, p = q ∧ q = !p := by
  rintro ⟨p, q, hpq, hq⟩
  subst hpq
  exact bool_not_no_fixedPt ⟨p, hq⟩

/-- The fixed-point equation of the mixed extension of negation. -/
theorem mixed_not_fixedPt_iff (p : ℝ) : 1 - p = p ↔ p = 1 / 2 := by
  constructor
  · intro h; linarith
  · intro h; subst h; norm_num

/-- There is a unique `p ∈ [0,1]` with `1 - p = p`. -/
theorem randomized_rescue : ∃! p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 ∧ 1 - p = p := by
  refine ⟨1 / 2, ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩, ?_⟩
  rintro p ⟨_, hp⟩
  exact (mixed_not_fixedPt_iff p).1 hp

/-- The solution set in `[0,1]` of `1 - p = p` is exactly `{1/2}`. -/
theorem randomized_rescue_eq_half :
    {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 1 - p = p} = {1 / 2} := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, hp⟩
    exact (mixed_not_fixedPt_iff p).1 hp
  · intro h
    subst h
    exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩

/-- `p ↦ 1 - p` maps `[0,1]` into itself. -/
theorem mixed_not_maps_Icc : Set.MapsTo (fun p : ℝ => 1 - p) (Set.Icc 0 1) (Set.Icc 0 1) := by
  intro p hp
  obtain ⟨h0, h1⟩ := hp
  exact ⟨by linarith, by linarith⟩

/-- The mixed extension of negation as a self-map of `[0,1]`. -/
def mixedNot : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 :=
  Set.MapsTo.restrict _ _ _ mixed_not_maps_Icc

/-- The self-map `mixedNot` of `[0,1]` has exactly one fixed point. -/
theorem mixed_not_unique_fixedPt : ∃! x : Set.Icc (0 : ℝ) 1, Function.IsFixedPt mixedNot x := by
  refine ⟨⟨1 / 2, by norm_num, by norm_num⟩, ?_, ?_⟩
  · apply Subtype.ext
    show (1 : ℝ) - 1 / 2 = 1 / 2
    norm_num
  · intro y hy
    apply Subtype.ext
    have h : (1 : ℝ) - y = y := congrArg Subtype.val hy
    exact (mixed_not_fixedPt_iff y).1 h

/-- A point of `[0,1]` is fixed by `mixedNot` iff its value is `1/2`. -/
theorem mixed_not_isFixedPt_iff (x : Set.Icc (0 : ℝ) 1) :
    Function.IsFixedPt mixedNot x ↔ (x : ℝ) = 1 / 2 := by
  constructor
  · intro hx
    exact (mixed_not_fixedPt_iff x).1 (congrArg Subtype.val hx)
  · intro hx
    apply Subtype.ext
    show (1 : ℝ) - x = x
    exact (mixed_not_fixedPt_iff x).2 hx

end ContrarianDiagonalAndRescue
