import Mathlib

/-!
# Stationary law of a positive-rate generator

Convention (same as `BoundaryTheorem/CycleClock.lean`): `M i j` is the rate from `i` to `j`,
rows sum to zero, and a stationary law is a row vector `π` with `π M = 0`, that is
`∑ i, π i * M i j = 0` for every `j`.

PROVED
* `abs_stationary` : if `v M = 0` then `|v| M = 0` (coordinatewise absolute value).
* `nonneg_stationary_zero_or_pos` : a nonnegative solution of `w M = 0` is either identically
  zero or strictly positive in every coordinate.
* `stationary_strict_sign` : every nonzero solution of `v M = 0` is strictly positive in every
  coordinate or strictly negative in every coordinate.
* `exists_stationary_ne_zero` : `v M = 0` has a nonzero solution (since `M 1 = 0`, `det M = 0`).
* `stationary_unique` : two solutions of `π M = 0` with total mass one are equal.
* `stationary_pos` : every solution of `π M = 0` with total mass one is strictly positive.
* `stationary_exists_unique_pos` : under `Fintype.card ι ≥ 2`, positive off-diagonal rates and
  zero row sums, there is exactly one `π` with `∑ i, π i = 1` and `π M = 0`, and every such `π`
  (hence the unique one) satisfies `0 < π i` for all `i`. This is the target statement.

The hypothesis `Fintype.card ι ≥ 2` is used only to obtain `Nonempty ι`; the lemmas above are
stated under `[Nonempty ι]` (or no cardinality assumption at all), which is more general.
-/

namespace StationaryPositiveGenerator

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive off-diagonal rates. -/
def PosRates (M : Matrix ι ι ℝ) : Prop := ∀ i j, i ≠ j → 0 < M i j

/-- Zero row sums. -/
def ZeroRowSums (M : Matrix ι ι ℝ) : Prop := ∀ i, ∑ j, M i j = 0

/-- `v M = 0` as a row-vector equation. -/
def Stationary (M : Matrix ι ι ℝ) (v : ι → ℝ) : Prop := ∀ j, ∑ i, v i * M i j = 0

theorem abs_stationary (M : Matrix ι ι ℝ) (hM : PosRates M) (hrow : ZeroRowSums M)
    (v : ι → ℝ) (hv : Stationary M v) : Stationary M (fun i => |v i|) := by
  have hge : ∀ j, 0 ≤ ∑ i, |v i| * M i j := by
    intro j
    rcases le_or_gt 0 (v j) with hj | hj
    · calc (0 : ℝ) = ∑ i, v i * M i j := (hv j).symm
        _ ≤ ∑ i, |v i| * M i j := by
          refine Finset.sum_le_sum fun i _ => ?_
          by_cases hij : i = j
          · subst hij; rw [abs_of_nonneg hj]
          · exact mul_le_mul_of_nonneg_right (le_abs_self _) (hM i j hij).le
    · calc (0 : ℝ) = -∑ i, v i * M i j := by rw [hv j, neg_zero]
        _ = ∑ i, (-v i) * M i j := by rw [← Finset.sum_neg_distrib]; simp [neg_mul]
        _ ≤ ∑ i, |v i| * M i j := by
          refine Finset.sum_le_sum fun i _ => ?_
          by_cases hij : i = j
          · subst hij; rw [abs_of_neg hj]
          · exact mul_le_mul_of_nonneg_right (neg_le_abs _) (hM i j hij).le
  have htot : ∑ j, ∑ i, |v i| * M i j = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.mul_sum, hrow i, mul_zero]
  intro j
  exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hge j).mp htot j (Finset.mem_univ _)

theorem nonneg_stationary_zero_or_pos (M : Matrix ι ι ℝ) (hM : PosRates M)
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : Stationary M w) :
    (∀ i, w i = 0) ∨ (∀ i, 0 < w i) := by
  by_cases h : ∃ j, w j = 0
  · left
    obtain ⟨j, hj⟩ := h
    have hterm : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i * M i j := by
      intro i _
      by_cases hij : i = j
      · subst hij; rw [hj, zero_mul]
      · exact mul_nonneg (hw0 i) (hM i j hij).le
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp (hw j)
    intro i
    by_cases hij : i = j
    · subst hij; exact hj
    · have := hz i (Finset.mem_univ _)
      rcases mul_eq_zero.mp this with h1 | h1
      · exact h1
      · exact absurd h1 (hM i j hij).ne'
  · right
    push Not at h
    exact fun i => lt_of_le_of_ne (hw0 i) (h i).symm

theorem stationary_strict_sign (M : Matrix ι ι ℝ) (hM : PosRates M) (hrow : ZeroRowSums M)
    (v : ι → ℝ) (hv : Stationary M v) (hne : v ≠ 0) :
    (∀ i, 0 < v i) ∨ (∀ i, v i < 0) := by
  have ha := abs_stationary M hM hrow v hv
  have hp : Stationary M (fun i => |v i| + v i) := by
    intro j
    simp only [add_mul, Finset.sum_add_distrib]
    rw [ha j, hv j, add_zero]
  have hq : Stationary M (fun i => |v i| - v i) := by
    intro j
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [ha j, hv j, sub_zero]
  have hp0 : ∀ i, 0 ≤ |v i| + v i := fun i => by
    have := neg_abs_le (v i); linarith
  have hq0 : ∀ i, 0 ≤ |v i| - v i := fun i => by
    have := le_abs_self (v i); linarith
  rcases nonneg_stationary_zero_or_pos M hM _ hp0 hp with hpz | hpp
  · rcases nonneg_stationary_zero_or_pos M hM _ hq0 hq with hqz | hqp
    · exact absurd (funext fun i => by have := hpz i; have := hqz i; simp only [Pi.zero_apply]; linarith) hne
    · right
      intro i
      have h1 := hpz i
      have h2 := hqp i
      linarith
  · left
    intro i
    have h1 := hpp i
    rcases le_or_gt (v i) 0 with h | h
    · rw [abs_of_nonpos h] at h1; linarith
    · exact h

theorem exists_stationary_ne_zero [Nonempty ι] (M : Matrix ι ι ℝ) (hrow : ZeroRowSums M) :
    ∃ v : ι → ℝ, v ≠ 0 ∧ Stationary M v := by
  have hdet : M.det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun _ => 1, ?_, ?_⟩
    · intro h
      have := congrFun h (Classical.arbitrary ι)
      simp at this
    · funext i
      simp only [mulVec, dotProduct, mul_one, Pi.zero_apply]
      exact hrow i
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  refine ⟨v, hv0, fun j => ?_⟩
  have := congrFun hv j
  simpa [vecMul, dotProduct] using this

theorem stationary_unique [Nonempty ι] (M : Matrix ι ι ℝ) (hM : PosRates M)
    (hrow : ZeroRowSums M) (π π' : ι → ℝ) (h1 : ∑ i, π i = 1) (h1' : ∑ i, π' i = 1)
    (hs : Stationary M π) (hs' : Stationary M π') : π = π' := by
  by_contra hne
  have hd : Stationary M (fun i => π i - π' i) := by
    intro j
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hs j, hs' j, sub_zero]
  have hdne : (fun i => π i - π' i) ≠ 0 := by
    intro h
    exact hne (funext fun i => sub_eq_zero.mp (congrFun h i))
  have hsum : ∑ i, (π i - π' i) = 0 := by
    rw [Finset.sum_sub_distrib, h1, h1', sub_self]
  rcases stationary_strict_sign M hM hrow _ hd hdne with hpos | hneg
  · have := Finset.sum_pos (fun i _ => hpos i) (Finset.univ_nonempty (α := ι))
    linarith
  · have := Finset.sum_neg (fun i _ => hneg i) (Finset.univ_nonempty (α := ι))
    linarith

theorem stationary_pos (M : Matrix ι ι ℝ) (hM : PosRates M) (hrow : ZeroRowSums M)
    (π : ι → ℝ) (h1 : ∑ i, π i = 1) (hs : Stationary M π) : ∀ i, 0 < π i := by
  have hne : π ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  rcases stationary_strict_sign M hM hrow π hs hne with hpos | hneg
  · exact hpos
  · exfalso
    have : ∑ i, π i ≤ 0 := Finset.sum_nonpos fun i _ => (hneg i).le
    linarith

theorem stationary_exists_unique_pos (hcard : 2 ≤ Fintype.card ι) (M : Matrix ι ι ℝ)
    (hM : ∀ i j, i ≠ j → 0 < M i j) (hrow : ∀ i, ∑ j, M i j = 0) :
    (∃! π : ι → ℝ, ∑ i, π i = 1 ∧ ∀ j, ∑ i, π i * M i j = 0) ∧
      ∀ π : ι → ℝ, ∑ i, π i = 1 → (∀ j, ∑ i, π i * M i j = 0) → ∀ i, 0 < π i := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  refine ⟨?_, fun π h1 hs => stationary_pos M hM hrow π h1 hs⟩
  obtain ⟨v, hv0, hv⟩ := exists_stationary_ne_zero M hrow
  have hsne : ∑ i, v i ≠ 0 := by
    rcases stationary_strict_sign M hM hrow v hv hv0 with hpos | hneg
    · exact (Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty).ne'
    · exact (Finset.sum_neg (fun i _ => hneg i) Finset.univ_nonempty).ne
  refine ⟨fun i => v i / ∑ k, v k, ⟨?_, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, div_self hsne]
  · intro j
    have : ∑ i, (v i / ∑ k, v k) * M i j = (∑ i, v i * M i j) / ∑ k, v k := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hv j, zero_div]
  · rintro π ⟨h1, hs⟩
    refine stationary_unique M hM hrow π _ h1 ?_ hs ?_
    · rw [← Finset.sum_div, div_self hsne]
    · intro j
      have : ∑ i, (v i / ∑ k, v k) * M i j = (∑ i, v i * M i j) / ∑ k, v k := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, hv j, zero_div]

end StationaryPositiveGenerator
