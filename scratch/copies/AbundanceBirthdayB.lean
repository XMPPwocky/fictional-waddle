import Mathlib

/-!
# Birthday bound for independent discoverers

`k` discoverers each independently pick one of `n` planets uniformly at random, so every
assignment `Fin k → Fin n` is equally likely and there are `n ^ k` of them. The event
"no two discoverers pick the same planet" is the set of injective assignments.

PROVED
* `card_assignments` : there are exactly `n ^ k` assignments `Fin k → Fin n`.
* `card_injective` : exactly `n.descFactorial k` assignments are injective.
* `noCollisionProb_eq_div` : the no-collision probability equals
  `n.descFactorial k / n ^ k`.
* `noCollisionProb_eq_card_div_card` : it equals (injective assignments) / (all assignments).
* `descFactorial_cast_eq_prod` : `(n.descFactorial k : ℝ) = ∏ i < k, (n - i)`.
* `noCollisionProb_eq_prod` : for `n > 0`, the no-collision probability is
  `∏ i < k, (1 - i / n)`.
* `noCollisionProb_nonneg`, `noCollisionProb_le_one` : it is a probability.
* `noCollisionProb_ge` : for `n > 0`, it is at least `1 - k (k - 1) / (2 n)`
  (valid for every `k`, including `k > n`).
* `collisionProb_le` : equivalently, the collision probability is at most `k (k - 1) / (2 n)`.
* `card_two_conflict` : exactly `n` assignments of two discoverers have them on the same planet.
* `collisionProb_two` : for `n > 0`, the conflict probability of two discoverers is `1 / n`.
* `collisionProb_two_eq_conflict_count` : that conflict probability is also
  (number of conflicting assignments) / `n ^ 2`.
* `tendsto_collisionProb_two` : the two-discoverer conflict probability tends to `0`
  as `n → ∞`.

INTERPRETED
* "Uniform, independent picks" is modelled as the uniform distribution on the `n ^ k`
  functions `Fin k → Fin n`; probabilities are counts divided by `n ^ k`.
* The equality with the product and the lower bound require `n > 0`: for `n = 0` and
  `k ≥ 1` there are no assignments at all, and the product `∏ (1 - i / 0)` evaluates to `1`
  under Lean's convention `x / 0 = 0`.
-/

namespace AbundanceBirthdayB

open Finset Filter Topology

/-- Probability that `k` uniform independent picks among `n` planets are pairwise distinct. -/
noncomputable def noCollisionProb (n k : ℕ) : ℝ :=
  (Fintype.card {f : Fin k → Fin n // Function.Injective f} : ℝ) / (n : ℝ) ^ k

/-- Probability that some two of the `k` picks coincide. -/
noncomputable def collisionProb (n k : ℕ) : ℝ := 1 - noCollisionProb n k

theorem card_assignments (n k : ℕ) : Fintype.card (Fin k → Fin n) = n ^ k := by
  simp

theorem card_injective (n k : ℕ) :
    Fintype.card {f : Fin k → Fin n // Function.Injective f} = n.descFactorial k := by
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fin n)),
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

theorem noCollisionProb_eq_div (n k : ℕ) :
    noCollisionProb n k = (n.descFactorial k : ℝ) / (n : ℝ) ^ k := by
  rw [noCollisionProb, card_injective]

theorem noCollisionProb_eq_card_div_card (n k : ℕ) :
    noCollisionProb n k =
      (Fintype.card {f : Fin k → Fin n // Function.Injective f} : ℝ) /
        (Fintype.card (Fin k → Fin n) : ℝ) := by
  rw [noCollisionProb, card_assignments]
  push_cast
  rfl

theorem descFactorial_cast_eq_prod (n k : ℕ) :
    (n.descFactorial k : ℝ) = ∏ i ∈ range k, ((n : ℝ) - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, prod_range_succ, Nat.cast_mul, ih, mul_comm]
    by_cases hk : k ≤ n
    · rw [Nat.cast_sub hk]
    · have h0 : n.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      have : ∏ i ∈ range k, ((n : ℝ) - i) = 0 := by rw [← ih, h0, Nat.cast_zero]
      rw [this]; simp

theorem noCollisionProb_eq_prod {n : ℕ} (hn : 0 < n) (k : ℕ) :
    noCollisionProb n k = ∏ i ∈ range k, (1 - (i : ℝ) / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [noCollisionProb_eq_div, descFactorial_cast_eq_prod]
  have : ∀ i ∈ range k, (1 - (i : ℝ) / n) = ((n : ℝ) - i) / n := by
    intro i _; field_simp
  rw [prod_congr rfl this, prod_div_distrib, prod_const, card_range]

theorem noCollisionProb_nonneg (n k : ℕ) : 0 ≤ noCollisionProb n k := by
  rw [noCollisionProb]; positivity

theorem noCollisionProb_le_one (n k : ℕ) : noCollisionProb n k ≤ 1 := by
  rw [noCollisionProb_eq_div]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Nat.cast_zero, zero_pow hk.ne']; simp
  · have hpos : (0 : ℝ) < (n : ℝ) ^ k := by positivity
    rw [div_le_one hpos]
    exact_mod_cast Nat.descFactorial_le_pow n k

theorem noCollisionProb_ge {n : ℕ} (hn : 0 < n) (k : ℕ) :
    1 - (k : ℝ) * ((k : ℝ) - 1) / (2 * n) ≤ noCollisionProb n k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [noCollisionProb_eq_prod hn]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ]
    by_cases hk : k < n
    · have hf : 0 ≤ 1 - (k : ℝ) / n := by
        rw [sub_nonneg, div_le_one hnR]; exact_mod_cast hk.le
      have hL : 1 - (k : ℝ) * ((k : ℝ) - 1) / (2 * n) ≤ 1 := by
        have : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) / (2 * n) := by
          rcases Nat.eq_zero_or_pos k with h | h
          · subst h; simp
          · have : (1 : ℝ) ≤ k := by exact_mod_cast h
            apply div_nonneg
            · nlinarith
            · positivity
        linarith
      have h1 := mul_le_mul_of_nonneg_right ih hf
      have hkn : 0 ≤ (k : ℝ) / n := by positivity
      have h2 : (1 - (k : ℝ) * ((k : ℝ) - 1) / (2 * n)) * (1 - (k : ℝ) / n) ≥
          1 - (k : ℝ) * ((k : ℝ) - 1) / (2 * n) - (k : ℝ) / n := by
        nlinarith
      have h3 : 1 - (k : ℝ) * ((k : ℝ) - 1) / (2 * n) - (k : ℝ) / n =
          1 - ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) - 1) / (2 * n) := by
        push_cast; field_simp; ring
      linarith
    · have hz : (1 - ((n : ℕ) : ℝ) / n) = 0 := by field_simp; ring
      have hprod : ∏ i ∈ range (k + 1), (1 - (i : ℝ) / n) = 0 :=
        prod_eq_zero (i := n) (mem_range.mpr (by omega)) hz
      rw [prod_range_succ] at hprod
      rw [hprod]
      have hkR : (n : ℝ) ≤ k := by exact_mod_cast (not_lt.mp hk)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [sub_nonpos, le_div_iff₀ (by positivity)]
      push_cast
      nlinarith

theorem collisionProb_le {n : ℕ} (hn : 0 < n) (k : ℕ) :
    collisionProb n k ≤ (k : ℝ) * ((k : ℝ) - 1) / (2 * n) := by
  have := noCollisionProb_ge hn k
  rw [collisionProb]; linarith

theorem card_two_conflict (n : ℕ) :
    Fintype.card {f : Fin 2 → Fin n // f 0 = f 1} = n := by
  let e : {f : Fin 2 → Fin n // f 0 = f 1} ≃ Fin n :=
    { toFun := fun f => f.1 0
      invFun := fun a => ⟨fun _ => a, rfl⟩
      left_inv := by
        rintro ⟨f, hf⟩
        apply Subtype.ext
        funext i
        fin_cases i
        · rfl
        · exact hf
      right_inv := fun a => rfl }
  rw [Fintype.card_congr e, Fintype.card_fin]

theorem collisionProb_two {n : ℕ} (hn : 0 < n) : collisionProb n 2 = 1 / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [collisionProb, noCollisionProb_eq_prod hn]
  simp [prod_range_succ]

theorem collisionProb_two_eq_conflict_count {n : ℕ} (hn : 0 < n) :
    collisionProb n 2 =
      (Fintype.card {f : Fin 2 → Fin n // f 0 = f 1} : ℝ) / (Fintype.card (Fin 2 → Fin n)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [collisionProb_two hn, card_two_conflict, card_assignments]
  push_cast
  field_simp

theorem tendsto_collisionProb_two :
    Tendsto (fun n : ℕ => collisionProb n 2) atTop (𝓝 0) := by
  have h : (fun n : ℕ => (1 : ℝ) / n) =ᶠ[atTop] fun n : ℕ => collisionProb n 2 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [collisionProb_two (by omega)]
  exact (tendsto_one_div_atTop_nhds_zero_nat).congr' h

end AbundanceBirthdayB
