import Mathlib

/-!
# Birthday bound for independent discoverers

Model: `k` discoverers each pick one of `n` planets independently and uniformly, i.e. the
outcome is a uniformly random function `Fin k → Fin n` (all `n ^ k` functions equally likely).
The no-collision event is the set of injective functions.

PROVED
* `card_injective` : the number of injective functions `Fin k → Fin n` is `n.descFactorial k`.
* `descFactorial_cast_eq_prod` : `(n.descFactorial k : ℝ) = ∏_{i<k} (n - i)`.
* `noCollisionProb_eq_div` : the no-collision probability equals `n.descFactorial k / n ^ k`.
* `noCollisionProb_eq_prod` : for `n > 0` it equals `∏_{i<k} (1 - i/n)`.
* `one_sub_sum_le_prod_one_sub` : Weierstrass product inequality, `1 - ∑ aᵢ ≤ ∏ (1 - aᵢ)` for
  `aᵢ ∈ [0,1]`.
* `sum_range_cast` : `∑_{i<k} i = k(k-1)/2` in `ℝ`.
* `noCollisionProb_ge` : for `n > 0`, the no-collision probability is at least
  `1 - k(k-1)/(2n)` (valid for all `k`, including `k > n`).
* `collisionProb_two` : for `n > 0` and two discoverers, the conflict probability is exactly `1/n`.
* `collisionProb_two_eq_card` : the same conflict probability computed directly as
  `#{f | f 0 = f 1} / n^2`.
* `collisionProb_two_tendsto_zero` : the two-discoverer conflict probability tends to `0`
  as `n → ∞`.
-/

namespace AbundanceBirthdayA

open Finset Filter Topology

/-- Probability, under the uniform distribution on `Fin k → Fin n`, that the choice is injective. -/
noncomputable def noCollisionProb (k n : ℕ) : ℝ :=
  ((univ.filter (fun f : Fin k → Fin n => Function.Injective f)).card : ℝ) /
    (Fintype.card (Fin k → Fin n) : ℝ)

/-- Probability that at least two discoverers pick the same planet. -/
noncomputable def collisionProb (k n : ℕ) : ℝ := 1 - noCollisionProb k n

theorem card_injective (k n : ℕ) :
    (univ.filter (fun f : Fin k → Fin n => Function.Injective f)).card = n.descFactorial k := by
  classical
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fin n))]
  rw [Fintype.card_embedding_eq]
  simp

theorem descFactorial_cast_eq_prod (n k : ℕ) :
    (n.descFactorial k : ℝ) = ∏ i ∈ range k, ((n : ℝ) - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, prod_range_succ, ← ih, Nat.cast_mul]
    by_cases h : n.descFactorial k = 0
    · simp [h]
    · have hk : k ≤ n := by
        by_contra hk
        exact h (Nat.descFactorial_eq_zero_iff_lt.mpr (by omega))
      rw [Nat.cast_sub hk]
      ring

theorem noCollisionProb_eq_div (k n : ℕ) :
    noCollisionProb k n = (n.descFactorial k : ℝ) / (n : ℝ) ^ k := by
  unfold noCollisionProb
  rw [card_injective]
  simp

theorem noCollisionProb_eq_prod (k n : ℕ) (hn : 0 < n) :
    noCollisionProb k n = ∏ i ∈ range k, (1 - (i : ℝ) / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : (n : ℝ) ^ k = ∏ _i ∈ range k, (n : ℝ) := by rw [prod_const, card_range]
  rw [noCollisionProb_eq_div, descFactorial_cast_eq_prod, hc, ← prod_div_distrib]
  refine prod_congr rfl fun i _ => ?_
  field_simp

theorem one_sub_sum_le_prod_one_sub (s : Finset ℕ) (a : ℕ → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi))
      (fun i hi => h1 i (mem_insert_of_mem hi))
    have hP : 0 ≤ ∏ i ∈ s, (1 - a i) :=
      prod_nonneg fun i hi => by linarith [h1 i (mem_insert_of_mem hi)]
    have hS : 0 ≤ ∑ i ∈ s, a i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    have ha0 := h0 j (mem_insert_self j s)
    have ha1 := h1 j (mem_insert_self j s)
    nlinarith [mul_le_mul_of_nonneg_left ih' (by linarith : (0 : ℝ) ≤ 1 - a j),
      mul_nonneg ha0 hS]

theorem sum_range_cast (k : ℕ) : ∑ i ∈ range k, (i : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem noCollisionProb_ge (k n : ℕ) (hn : 0 < n) :
    1 - (k : ℝ) * ((k : ℝ) - 1) / (2 * n) ≤ noCollisionProb k n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hk : k ≤ n
  · rw [noCollisionProb_eq_prod k n hn]
    have hsum : ∑ i ∈ range k, (i : ℝ) / n = (k : ℝ) * ((k : ℝ) - 1) / (2 * n) := by
      rw [← sum_div, sum_range_cast]
      field_simp
    rw [← hsum]
    apply one_sub_sum_le_prod_one_sub
    · intro i _
      positivity
    · intro i hi
      rw [div_le_one hnr]
      have : i < k := mem_range.mp hi
      exact_mod_cast (by omega : i ≤ n)
  · have hz : noCollisionProb k n = 0 := by
      rw [noCollisionProb_eq_div, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
      simp
    rw [hz]
    have hk' : (n : ℝ) + 1 ≤ k := by exact_mod_cast (by omega : n + 1 ≤ k)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [sub_nonpos, le_div_iff₀ (by positivity)]
    nlinarith

theorem collisionProb_two (n : ℕ) (hn : 0 < n) : collisionProb 2 n = 1 / n := by
  unfold collisionProb
  rw [noCollisionProb_eq_prod 2 n hn]
  simp [prod_range_succ]

theorem collisionProb_two_eq_card (n : ℕ) (hn : 0 < n) :
    collisionProb 2 n =
      ((univ.filter (fun f : Fin 2 → Fin n => f 0 = f 1)).card : ℝ) / (n : ℝ) ^ 2 := by
  have hcard : (univ.filter (fun f : Fin 2 → Fin n => f 0 = f 1)).card = n := by
    rw [← Fintype.card_subtype]
    let e : { f : Fin 2 → Fin n // f 0 = f 1 } ≃ Fin n :=
      { toFun := fun f => f.1 0
        invFun := fun x => ⟨fun _ => x, rfl⟩
        left_inv := by
          rintro ⟨f, hf⟩
          apply Subtype.ext
          funext i
          fin_cases i
          · rfl
          · exact hf
        right_inv := fun x => rfl }
    rw [Fintype.card_congr e, Fintype.card_fin]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hcard, collisionProb_two n hn]
  field_simp

theorem collisionProb_two_tendsto_zero :
    Tendsto (fun n : ℕ => collisionProb 2 n) atTop (𝓝 0) := by
  refine (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [collisionProb_two n hn]

end AbundanceBirthdayA
