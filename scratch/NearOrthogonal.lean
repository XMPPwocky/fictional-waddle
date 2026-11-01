import Mathlib

/-!
# Exponentially many nearly orthogonal directions (superposition capacity), by counting

Sign vectors in dimension `n` are encoded as `S : Finset (Fin n)` (the coordinates set to −1). Two of them have inner
product `corr n S T = n − 2 · |S ∆ T|`.

* O1 `binomial_tail`: for `0 < x ≤ 1`, `∑_{k ≤ m} C(n, k) ≤ x^(−m) (1 + x)^n`. A Chernoff bound by the
  generating-function trick.
* O2 `greedy_packing`: in a finite set where every element conflicts with at most `B` elements (itself included),
  there is a conflict-free subset of size at least `N / B`.
* O3 `near_orthogonal_family`: for `2q ≤ n` there is a family of sign vectors with pairwise `|corr| ≤ n − 2q`, of
  size at least `2^n / (2 ∑_{k<q} C(n, k) + 1)`.
* O4 `superposition_beats_dimension`: in dimension `n = 1024`, more than `10^50` sign vectors have pairwise
  `|cos| ≤ 1/2`. That is exponentially more nearly orthogonal directions than dimensions.
-/

namespace NearOrthogonal

open Finset

/-- **O1.** -/
theorem binomial_tail (n m : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (∑ k ∈ range (m + 1), (n.choose k : ℝ)) ≤ (1 / x) ^ m * (1 + x) ^ n := by
  have hxk : ∀ k ∈ range (m + 1), (n.choose k : ℝ) ≤ (1 / x) ^ m * ((n.choose k : ℝ) * x ^ k) := by
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have h1 : x ^ m ≤ x ^ k := pow_le_pow_of_le_one hx0.le hx1 hkm
    have h2 : (1 / x) ^ m * x ^ m = 1 := by rw [← mul_pow, one_div, inv_mul_cancel₀ hx0.ne', one_pow]
    have h3 : 1 ≤ (1 / x) ^ m * x ^ k := by
      calc (1 : ℝ) = (1 / x) ^ m * x ^ m := h2.symm
        _ ≤ (1 / x) ^ m * x ^ k := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hc : (0 : ℝ) ≤ n.choose k := by positivity
    nlinarith
  calc (∑ k ∈ range (m + 1), (n.choose k : ℝ)) ≤ ∑ k ∈ range (m + 1), (1 / x) ^ m * ((n.choose k : ℝ) * x ^ k) :=
        sum_le_sum hxk
    _ = (1 / x) ^ m * ∑ k ∈ range (m + 1), (n.choose k : ℝ) * x ^ k := by rw [mul_sum]
    _ ≤ (1 / x) ^ m * ∑ k ∈ range (n + 1), (n.choose k : ℝ) * x ^ k := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hz : ∀ k ∈ range (m + 1), k ∉ range (n + 1) → (n.choose k : ℝ) * x ^ k = 0 := by
          intro k _ hk
          have : n < k := by simpa using hk
          simp [Nat.choose_eq_zero_of_lt this]
        calc ∑ k ∈ range (m + 1), (n.choose k : ℝ) * x ^ k
            = ∑ k ∈ (range (m + 1)).filter (fun k => k ∈ range (n + 1)), (n.choose k : ℝ) * x ^ k := by
              rw [sum_filter_of_ne]; intro k hk hne; by_contra hc; exact hne (hz k hk hc)
          _ ≤ ∑ k ∈ range (n + 1), (n.choose k : ℝ) * x ^ k := by
              apply sum_le_sum_of_subset_of_nonneg
              · intro k hk; exact (mem_filter.mp hk).2
              · intro k _ _; positivity
    _ = (1 / x) ^ m * (1 + x) ^ n := by
        congr 1; rw [show (1 : ℝ) + x = x + 1 by ring, add_pow]; apply sum_congr rfl; intro k _; simp only [one_pow, mul_one]; ring

/-- **O2.** -/
theorem greedy_packing {α : Type*} [Fintype α] [DecidableEq α] (R : α → α → Prop) [DecidableRel R] (B : ℕ)
    (hdeg : ∀ a, (univ.filter (fun b => R a b ∨ R b a ∨ b = a)).card ≤ B) :
    ∃ S : Finset α, (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ R a b) ∧ Fintype.card α ≤ S.card * B := by
  classical
  have aux : ∀ U : Finset α, ∃ S ⊆ U, (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ R a b) ∧ U.card ≤ S.card * B := by
    intro U
    induction U using Finset.strongInduction with
    | H U ih =>
      rcases U.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
      · exact ⟨∅, by simp, by simp, by simp⟩
      · set N := univ.filter (fun b => R a b ∨ R b a ∨ b = a) with hN
        have haN : a ∈ N := by simp [hN]
        have hsub : U \ N ⊂ U := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, fun h => ?_⟩
          have : a ∈ U \ N := by rw [h]; exact ha
          exact (mem_sdiff.mp this).2 haN
        obtain ⟨S', hS'sub, hS'pw, hS'card⟩ := ih (U \ N) hsub
        have haS' : a ∉ S' := fun h => (mem_sdiff.mp (hS'sub h)).2 haN
        have notN : ∀ y ∈ S', y ∉ N := fun y hy => (mem_sdiff.mp (hS'sub hy)).2
        refine ⟨insert a S', ?_, ?_, ?_⟩
        · intro y hy; rcases mem_insert.mp hy with rfl | hy
          · exact ha
          · exact (mem_sdiff.mp (hS'sub hy)).1
        · intro x hx y hy hxy
          rcases mem_insert.mp hx with hxa | hx' <;> rcases mem_insert.mp hy with hya | hy'
          · exact absurd (hxa.trans hya.symm) hxy
          · rw [hxa]; have := notN y hy'; simp only [hN, mem_filter, mem_univ, true_and, not_or] at this; exact this.1
          · rw [hya]; have := notN x hx'; simp only [hN, mem_filter, mem_univ, true_and, not_or] at this; exact this.2.1
          · exact hS'pw x hx' y hy' hxy
        · rw [card_insert_of_notMem haS']
          calc U.card ≤ (U \ N).card + N.card := card_le_card_sdiff_add_card
            _ ≤ S'.card * B + B := add_le_add hS'card (hdeg a)
            _ = (S'.card + 1) * B := by ring
  obtain ⟨S, _, hpw, hc⟩ := aux univ
  exact ⟨S, hpw, by simpa using hc⟩

/-- Inner product of the sign vectors encoded by `S` and `T`. -/
def corr (n : ℕ) (S T : Finset (Fin n)) : ℤ := n - 2 * (symmDiff S T).card

lemma card_small (n q : ℕ) :
    (univ.filter (fun D : Finset (Fin n) => D.card < q)).card = ∑ k ∈ range q, n.choose k := by
  have h : (univ.filter (fun D : Finset (Fin n) => D.card < q)) = (range q).biUnion (fun k => powersetCard k univ) := by
    ext D; simp [mem_powersetCard]
  rw [h, card_biUnion]
  · apply sum_congr rfl; intro k _; rw [card_powersetCard, card_univ, Fintype.card_fin]
  · intro i _ j _ hij; exact disjoint_left.mpr (fun D hi hj => hij ((mem_powersetCard.mp hi).2.symm.trans (mem_powersetCard.mp hj).2))

lemma count_near (n q : ℕ) (S : Finset (Fin n)) :
    (univ.filter (fun T : Finset (Fin n) => (symmDiff S T).card < q)).card = ∑ k ∈ range q, n.choose k := by
  rw [← card_small n q]
  apply Finset.card_nbij' (fun T => symmDiff S T) (fun D => symmDiff S D)
  · intro T hT; simpa using hT
  · intro D hD; simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hD ⊢; rwa [symmDiff_symmDiff_cancel_left]
  · intro T _; simp [symmDiff_symmDiff_cancel_left]
  · intro D _; simp [symmDiff_symmDiff_cancel_left]

lemma count_far (n q : ℕ) (hq : q ≤ n) (S : Finset (Fin n)) :
    (univ.filter (fun T : Finset (Fin n) => n - q < (symmDiff S T).card)).card = ∑ k ∈ range q, n.choose k := by
  rw [← card_small n q]
  apply Finset.card_nbij' (fun T => (symmDiff S T)ᶜ) (fun E => symmDiff S Eᶜ)
  · intro T hT
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hT ⊢
    rw [card_compl, Fintype.card_fin]
    have := card_le_univ (symmDiff S T); rw [Fintype.card_fin] at this; omega
  · intro E hE
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hE ⊢
    rw [symmDiff_symmDiff_cancel_left, card_compl, Fintype.card_fin]
    have := card_le_univ E; rw [Fintype.card_fin] at this; omega
  · intro T _; simp [symmDiff_symmDiff_cancel_left]
  · intro E _; simp [symmDiff_symmDiff_cancel_left]

/-- **O3.** -/
theorem near_orthogonal_family (n q : ℕ) (hq : 2 * q ≤ n) :
    ∃ F : Finset (Finset (Fin n)), (∀ S ∈ F, ∀ T ∈ F, S ≠ T → |corr n S T| ≤ n - 2 * q) ∧
      2 ^ n ≤ F.card * (2 * ∑ k ∈ range q, n.choose k + 1) := by
  classical
  let R : Finset (Fin n) → Finset (Fin n) → Prop := fun S T => (n : ℤ) - 2 * q < |corr n S T|
  have hsymm : ∀ S T, corr n S T = corr n T S := fun S T => by simp [corr, symmDiff_comm]
  have hRiff : ∀ S T, R S T → (symmDiff S T).card < q ∨ n - q < (symmDiff S T).card := by
    intro S T h
    have hle : (symmDiff S T).card ≤ n := by have := card_le_univ (symmDiff S T); rwa [Fintype.card_fin] at this
    simp only [R, corr] at h
    rcases lt_abs.mp h with h1 | h1 <;> omega
  have hdeg : ∀ S, (univ.filter (fun T => R S T ∨ R T S ∨ T = S)).card ≤ 2 * ∑ k ∈ range q, n.choose k + 1 := by
    intro S
    have hsub : univ.filter (fun T => R S T ∨ R T S ∨ T = S) ⊆
        (univ.filter (fun T : Finset (Fin n) => (symmDiff S T).card < q) ∪
          univ.filter (fun T : Finset (Fin n) => n - q < (symmDiff S T).card)) ∪ {S} := by
      intro T hT
      simp only [mem_filter, mem_univ, true_and] at hT
      simp only [mem_union, mem_filter, mem_univ, true_and, mem_singleton]
      rcases hT with h | h | h
      · left; exact hRiff S T h
      · left; have h' : R S T := by simpa only [R, hsymm T S] using h
        exact hRiff S T h'
      · right; exact h
    calc (univ.filter (fun T => R S T ∨ R T S ∨ T = S)).card
        ≤ ((univ.filter (fun T : Finset (Fin n) => (symmDiff S T).card < q) ∪
          univ.filter (fun T : Finset (Fin n) => n - q < (symmDiff S T).card)) ∪ {S}).card := card_le_card hsub
      _ ≤ (univ.filter (fun T : Finset (Fin n) => (symmDiff S T).card < q) ∪
          univ.filter (fun T : Finset (Fin n) => n - q < (symmDiff S T).card)).card + 1 := by
          rw [← card_singleton S]; exact card_union_le _ _
      _ ≤ (univ.filter (fun T : Finset (Fin n) => (symmDiff S T).card < q)).card +
          (univ.filter (fun T : Finset (Fin n) => n - q < (symmDiff S T).card)).card + 1 := by
          have := card_union_le (univ.filter (fun T : Finset (Fin n) => (symmDiff S T).card < q))
            (univ.filter (fun T : Finset (Fin n) => n - q < (symmDiff S T).card)); omega
      _ = 2 * ∑ k ∈ range q, n.choose k + 1 := by rw [count_near, count_far n q (by omega)]; ring
  obtain ⟨F, hpw, hc⟩ := greedy_packing R (2 * ∑ k ∈ range q, n.choose k + 1) hdeg
  refine ⟨F, fun S hS T hT hne => not_lt.mp (hpw S hS T hT hne), ?_⟩
  simpa [Fintype.card_finset, Fintype.card_fin] using hc

/-- **O4.** -/
theorem superposition_beats_dimension :
    ∃ F : Finset (Finset (Fin 1024)), (∀ S ∈ F, ∀ T ∈ F, S ≠ T → |corr 1024 S T| ≤ 512) ∧ 10 ^ 50 < F.card := by
  obtain ⟨F, hF, hc⟩ := near_orthogonal_family 1024 256 (by norm_num)
  refine ⟨F, fun S hS T hT hne => by have := hF S hS T hT hne; norm_num at this; exact this, ?_⟩
  have htail := binomial_tail 1024 255 (1 / 3) (by norm_num) (by norm_num)
  have hc' : (2 : ℝ) ^ 1024 ≤ (F.card : ℝ) * (2 * ∑ k ∈ range 256, ((1024 : ℕ).choose k : ℝ) + 1) := by
    exact_mod_cast hc
  by_contra hcon
  push_neg at hcon
  have hF0 : (F.card : ℝ) ≤ 10 ^ 50 := by exact_mod_cast hcon
  have hs0 : (0 : ℝ) ≤ 2 * ∑ k ∈ range 256, ((1024 : ℕ).choose k : ℝ) + 1 := by positivity
  have key : (2 : ℝ) ^ 1024 ≤ 10 ^ 50 * (2 * ((1 / (1 / 3)) ^ 255 * (1 + 1 / 3) ^ 1024) + 1) := by
    calc (2 : ℝ) ^ 1024 ≤ (F.card : ℝ) * (2 * ∑ k ∈ range 256, ((1024 : ℕ).choose k : ℝ) + 1) := hc'
      _ ≤ 10 ^ 50 * (2 * ∑ k ∈ range 256, ((1024 : ℕ).choose k : ℝ) + 1) := mul_le_mul_of_nonneg_right hF0 hs0
      _ ≤ 10 ^ 50 * (2 * ((1 / (1 / 3)) ^ 255 * (1 + 1 / 3) ^ 1024) + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith [htail]
  set_option exponentiation.threshold 2048 in norm_num at key

end NearOrthogonal
