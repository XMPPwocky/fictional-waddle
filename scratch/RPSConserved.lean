import Mathlib

/-!
# Zero-sum rock-paper-scissors replicator dynamics conserves `∏ xᵢ`; no pair can coexist

Replicator field for a payoff matrix `A : Matrix (Fin n) (Fin n) ℝ` at a state `x : Fin n → ℝ`:
`replicator A x i = x i * ((A *ᵥ x) i - x ⬝ᵥ (A *ᵥ x))`.

## What is PROVED (no `sorry`, no extra axioms)

Algebraic core, general `n`:
* R0 `quadForm_eq_zero_of_antisymm`: `Aᵀ = -A → x ⬝ᵥ (A *ᵥ x) = 0`.
* R1 `sum_growth_rates_eq_zero`: `Aᵀ = -A`, every column sums to `0` ⟹
  `∑ i, ((A *ᵥ x) i - x ⬝ᵥ (A *ᵥ x)) = 0` for EVERY `x` (no positivity, no simplex constraint).
* R2 `sum_replicator_div_eq_zero`: same hypotheses plus `∀ i, x i ≠ 0` ⟹ `∑ i, replicator A x i / x i = 0`,
  i.e. `d/dt log ∏ xᵢ = 0` along the flow.

RPS instance:
* R3 `rps_antisymm`, `rps_colsum`: the matrix `!![0, 1, -1; -1, 0, 1; 1, -1, 0]` satisfies both hypotheses.
* R4 `rps_sum_replicator_div_eq_zero`: R2 for the RPS matrix.
* helper `rps_replicator_apply`: `v = (x0 (x1 - x2), x1 (x2 - x0), x2 (x0 - x1))` for every real `x`.

Calculus (trajectories `x : ℝ → Fin n → ℝ` with `HasDerivAt (fun t => x t i) (replicator A (x t) i) t` for all `i, t`):
* R5 `hasDerivAt_prod_replicator`: general `n`, `t ↦ ∏ i, x t i` has derivative `0` at every `t`.
  NO positivity hypothesis is needed: `d/dt ∏ xᵢ = (∏ xᵢ) · ∑ᵢ gᵢ` with `gᵢ` the growth rates, and `∑ gᵢ = 0`
  identically by R1.
* R6 `prod_const_replicator`: general `n`, `∏ i, x s i = ∏ i, x t i` for all `s t`.
* R7 `rps_prod_const`: the requested RPS statement (each coordinate positive, `Fin 3`); the positivity
  hypothesis is carried as asked but is not used.

Pair collapse on the faces of the RPS simplex (index `0, 1, 2`; with this matrix `0` beats `1`, `1` beats `2`,
`2` beats `0`, since `A 0 1 = A 1 2 = A 2 0 = 1`):
* R8 `rps_face_growth`: on the face `x 2 = 0` with `x 0, x 1 > 0`: `v 0 = x 0 * x 1 > 0` and `v 1 < 0`.
  Cyclically: on `x 0 = 0`, `v 1 > 0 > v 2`; on `x 1 = 0`, `v 2 > 0 > v 0`. In each pair the winner strictly grows.
* R9 `rps_face_rest_point`: for any `k`, a rest point (`v = 0`) of the RPS field with `x k = 0` has one more zero
  coordinate (stated for all real `x`, no simplex constraint).
* R10 `rps_face_rest_is_vertex`: on the simplex (`x ≥ 0`, `∑ x = 1`), a rest point with some coordinate `0` is a
  vertex `Pi.single i 1`. (The nonnegativity hypothesis is carried for the simplex reading but is not used:
  two zero coordinates plus `∑ x = 1` already force a vertex.)
* R11 `rps_interior_rest_iff`: on the open simplex (all `x i > 0`, `∑ x = 1`), `v = 0 ↔ x = (1/3, 1/3, 1/3)`.
  So the triple has a coexistence point while no pair does.

## What is INTERPRETATION only (not formalized)

The "Borromean" reading: three species can coexist (R11) but removing any one makes the remaining pair collapse
to a single survivor (R8-R10), like Borromean rings, which are linked as a triple yet pairwise unlinked. The
analogy with Milnor's triple linking number (a link invariant visible only at the level of triples, with all
pairwise linking numbers zero) is suggestive only; nothing about links, knots, or Milnor invariants is stated or
proved here. Likewise "conserved product = closed orbits around the barycenter" is the standard consequence of
R6 on the open simplex, not proved here.
-/

namespace RPSConserved

open Matrix Finset

/-- Replicator velocity field for payoff matrix `A`. -/
noncomputable def replicator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i * ((A *ᵥ x) i - x ⬝ᵥ (A *ᵥ x))

/-- The zero-sum rock-paper-scissors payoff matrix. -/
def rps : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, -1; -1, 0, 1; 1, -1, 0]

/-- **R0.** Antisymmetric payoffs: mean fitness is identically zero. -/
theorem quadForm_eq_zero_of_antisymm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = -A)
    (x : Fin n → ℝ) : x ⬝ᵥ (A *ᵥ x) = 0 := by
  have h1 : x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (Aᵀ *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.mulVec_transpose]
  rw [hA, Matrix.neg_mulVec, dotProduct_neg] at h1
  linarith

/-- **R1.** The growth rates sum to zero, for every `x`. -/
theorem sum_growth_rates_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = -A)
    (hcol : ∀ j, ∑ i, A i j = 0) (x : Fin n → ℝ) :
    ∑ i, ((A *ᵥ x) i - x ⬝ᵥ (A *ᵥ x)) = 0 := by
  rw [Finset.sum_sub_distrib, quadForm_eq_zero_of_antisymm A hA x]
  simp only [Finset.sum_const_zero, sub_zero, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul, hcol]

/-- **R2.** `d/dt log ∏ xᵢ = ∑ vᵢ / xᵢ = 0`. -/
theorem sum_replicator_div_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = -A)
    (hcol : ∀ j, ∑ i, A i j = 0) (x : Fin n → ℝ) (hx : ∀ i, x i ≠ 0) :
    ∑ i, replicator A x i / x i = 0 := by
  rw [← sum_growth_rates_eq_zero A hA hcol x]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold replicator
  rw [mul_div_cancel_left₀ _ (hx i)]

/-- **R3a.** -/
theorem rps_antisymm : rpsᵀ = -rps := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rps]

/-- **R3b.** -/
theorem rps_colsum : ∀ j, ∑ i, rps i j = 0 := by
  intro j
  fin_cases j <;> simp [rps, Fin.sum_univ_three]

/-- **R4.** -/
theorem rps_sum_replicator_div_eq_zero (x : Fin 3 → ℝ) (hx : ∀ i, x i ≠ 0) :
    ∑ i, replicator rps x i / x i = 0 := by
  exact sum_replicator_div_eq_zero rps rps_antisymm rps_colsum x hx


/-- Explicit RPS replicator components (mean fitness vanishes by antisymmetry). -/
theorem rps_replicator_apply (x : Fin 3 → ℝ) :
    replicator rps x 0 = x 0 * (x 1 - x 2) ∧ replicator rps x 1 = x 1 * (x 2 - x 0) ∧
      replicator rps x 2 = x 2 * (x 0 - x 1) := by
  have hv : rps *ᵥ x = ![x 1 - x 2, x 2 - x 0, x 0 - x 1] := by
    ext i
    fin_cases i <;> simp [rps, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  unfold replicator
  rw [quadForm_eq_zero_of_antisymm rps rps_antisymm, hv]
  simp

/-- **R5.** Along any replicator trajectory, `∏ xᵢ` has zero derivative (general `n`, no positivity). -/
theorem hasDerivAt_prod_replicator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = -A)
    (hcol : ∀ j, ∑ i, A i j = 0) (x : ℝ → Fin n → ℝ)
    (hx : ∀ i t, HasDerivAt (fun t => x t i) (replicator A (x t) i) t) (t : ℝ) :
    HasDerivAt (fun t => ∏ i, x t i) 0 t := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hx i t)
  convert h using 1
  have : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (∏ j ∈ Finset.univ.erase i, x t j) • replicator A (x t) i
        = (∏ j, x t j) * ((A *ᵥ x t) i - x t ⬝ᵥ (A *ᵥ x t)) := by
    intro i hi
    rw [smul_eq_mul, ← Finset.prod_erase_mul _ _ hi]
    unfold replicator
    ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_growth_rates_eq_zero A hA hcol, mul_zero]

/-- **R6.** Along any replicator trajectory, `∏ xᵢ` is constant (general `n`, no positivity). -/
theorem prod_const_replicator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = -A)
    (hcol : ∀ j, ∑ i, A i j = 0) (x : ℝ → Fin n → ℝ)
    (hx : ∀ i t, HasDerivAt (fun t => x t i) (replicator A (x t) i) t) (s t : ℝ) :
    ∏ i, x s i = ∏ i, x t i := by
  have hd := hasDerivAt_prod_replicator A hA hcol x hx
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) s t

/-- **R7.** The requested RPS statement: positive trajectory of the RPS replicator field ⟹ `∏ xᵢ` constant.
(`hpos` is not needed; see R6.) -/
theorem rps_prod_const (x : ℝ → Fin 3 → ℝ) (hpos : ∀ t i, 0 < x t i)
    (hx : ∀ i t, HasDerivAt (fun t => x t i) (replicator rps (x t) i) t) (s t : ℝ) :
    ∏ i, x s i = ∏ i, x t i := by
  exact prod_const_replicator rps rps_antisymm rps_colsum x hx s t

/-- **R8.** On each edge of the simplex, the winner of the pair strictly grows and the loser strictly shrinks. -/
theorem rps_face_growth (x : Fin 3 → ℝ) :
    (x 2 = 0 → 0 < x 0 → 0 < x 1 → 0 < replicator rps x 0 ∧ replicator rps x 1 < 0) ∧
    (x 0 = 0 → 0 < x 1 → 0 < x 2 → 0 < replicator rps x 1 ∧ replicator rps x 2 < 0) ∧
    (x 1 = 0 → 0 < x 2 → 0 < x 0 → 0 < replicator rps x 2 ∧ replicator rps x 0 < 0) := by
  obtain ⟨e0, e1, e2⟩ := rps_replicator_apply x
  rw [e0, e1, e2]
  refine ⟨fun h2 h0 h1 => ?_, fun h0 h1 h2 => ?_, fun h1 h2 h0 => ?_⟩
  · rw [h2]; constructor <;> nlinarith [mul_pos h0 h1]
  · rw [h0]; constructor <;> nlinarith [mul_pos h1 h2]
  · rw [h1]; constructor <;> nlinarith [mul_pos h2 h0]

/-- **R9.** A rest point with one coordinate zero has a second zero coordinate. -/
theorem rps_face_rest_point (x : Fin 3 → ℝ) (k : Fin 3) (hk : x k = 0) (hrest : replicator rps x = 0) :
    ∃ j, j ≠ k ∧ x j = 0 := by
  have e0 := congrFun hrest 0
  have e1 := congrFun hrest 1
  have e2 := congrFun hrest 2
  obtain ⟨r0, r1, r2⟩ := rps_replicator_apply x
  simp only [r0, r1, r2, Pi.zero_apply] at e0 e1 e2
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hk
  · rw [hk, sub_zero] at e1
    rcases mul_eq_zero.1 e1 with h | h
    · exact ⟨1, by decide, h⟩
    · exact ⟨2, by decide, h⟩
  · rw [hk, sub_zero] at e2
    rcases mul_eq_zero.1 e2 with h | h
    · exact ⟨2, by decide, h⟩
    · exact ⟨0, by decide, h⟩
  · rw [hk, sub_zero] at e0
    rcases mul_eq_zero.1 e0 with h | h
    · exact ⟨0, by decide, h⟩
    · exact ⟨1, by decide, h⟩

/-- **R10.** On the simplex, a rest point on the boundary is a vertex. -/
theorem rps_face_rest_is_vertex (x : Fin 3 → ℝ) (hnn : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (k : Fin 3) (hk : x k = 0) (hrest : replicator rps x = 0) :
    ∃ i, x = Pi.single i 1 := by
  obtain ⟨j, hjk, hj⟩ := rps_face_rest_point x k hk hrest
  rw [Fin.sum_univ_three] at hsum
  fin_cases k <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hk hj hjk <;>
    first
    | exact absurd rfl hjk
    | (refine ⟨0, funext fun i => ?_⟩; fin_cases i <;> simp <;> linarith)
    | (refine ⟨1, funext fun i => ?_⟩; fin_cases i <;> simp <;> linarith)
    | (refine ⟨2, funext fun i => ?_⟩; fin_cases i <;> simp <;> linarith)

/-- **R11.** On the open simplex, the unique rest point is the barycenter. -/
theorem rps_interior_rest_iff (x : Fin 3 → ℝ) (hpos : ∀ i, 0 < x i) (hsum : ∑ i, x i = 1) :
    replicator rps x = 0 ↔ x = fun _ => 1 / 3 := by
  rw [Fin.sum_univ_three] at hsum
  constructor
  · intro hrest
    have e0 := congrFun hrest 0
    have e1 := congrFun hrest 1
    obtain ⟨r0, r1, r2⟩ := rps_replicator_apply x
    simp only [r0, r1, Pi.zero_apply] at e0 e1
    have a : x 1 = x 2 := by
      have := (mul_eq_zero.1 e0).resolve_left (hpos 0).ne'
      linarith
    have b : x 2 = x 0 := by
      have := (mul_eq_zero.1 e1).resolve_left (hpos 1).ne'
      linarith
    funext i
    fin_cases i <;> simp <;> linarith
  · rintro rfl
    funext i
    obtain ⟨r0, r1, r2⟩ := rps_replicator_apply (fun _ => (1 : ℝ) / 3)
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Pi.zero_apply] <;>
      (first | rw [r0] | rw [r1] | rw [r2]) <;> norm_num

end RPSConserved
