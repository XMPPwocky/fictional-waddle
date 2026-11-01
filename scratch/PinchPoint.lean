import Mathlib

/-!
# Two closed lobes pinched at one point: every connected passage goes through the pinch

* T1 `pinch_point` (the general form): in any topological space, if a preconnected set `S` is covered by two closed
  sets `A, B` with `A ∩ B = {p}`, and `S` meets both `A` and `B`, then `p ∈ S`.
* T2 `causal_path_through_apex` (the light cone, in every dimension): in `ℝ × E` (time × space, `E` any real normed
  space), let a path stay causal, `‖x‖ ≤ |t|`, and run from the future cone (`‖x‖ ≤ t`) to the past cone
  (`‖x‖ ≤ −t`). Then it passes through the zero vector.
* T3 `apex_disconnects_causal_vectors`: the causal vectors with the zero vector removed are NOT preconnected. Future
  and past fall apart, so time orientation is a topological invariant of causal vectors.
* T4 `orthant_path_through_origin` (the n-dimensional same-sign orthants): a path in `Fin n → ℝ` that keeps all
  pairwise products `xᵢxⱼ ≥ 0`, starting in the nonnegative orthant and ending in the nonpositive one, passes
  through `0`.
* T5 `lawful_good_to_chaotic_evil` (the labelled reading): with coordinates (Law, Good), a path from the Lawful-Good
  quadrant to the Chaotic-Evil quadrant that never enters the mixed quadrants passes through True Neutral `(0, 0)`.
-/

namespace PinchPoint

open Set

/-- **T1.** -/
theorem pinch_point {X : Type*} [TopologicalSpace X] {S A B : Set X} {p : X} (hS : IsPreconnected S)
    (hA : IsClosed A) (hB : IsClosed B) (hcov : S ⊆ A ∪ B) (hAB : A ∩ B = {p}) (hSA : (S ∩ A).Nonempty)
    (hSB : (S ∩ B).Nonempty) : p ∈ S := by
  obtain ⟨x, hxS, hxAB⟩ := isPreconnected_closed_iff.mp hS A B hA hB hcov hSA hSB
  rw [hAB, mem_singleton_iff] at hxAB
  exact hxAB ▸ hxS

/-- **T2.** -/
theorem causal_path_through_apex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (γ : ℝ → ℝ × E)
    (hγ : ContinuousOn γ (Icc 0 1)) (hcausal : ∀ s ∈ Icc (0 : ℝ) 1, ‖(γ s).2‖ ≤ |(γ s).1|)
    (h0 : ‖(γ 0).2‖ ≤ (γ 0).1) (h1 : ‖(γ 1).2‖ ≤ -(γ 1).1) : ∃ s ∈ Icc (0 : ℝ) 1, γ s = 0 := by
  set A : Set (ℝ × E) := {v | ‖v.2‖ ≤ v.1}
  set B : Set (ℝ × E) := {v | ‖v.2‖ ≤ -v.1}
  have hA : IsClosed A := isClosed_le (continuous_norm.comp continuous_snd) continuous_fst
  have hB : IsClosed B := isClosed_le (continuous_norm.comp continuous_snd) continuous_fst.neg
  have hAB : A ∩ B = {0} := by
    ext v
    simp only [A, B, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hn := norm_nonneg v.2
      have ht : v.1 = 0 := by linarith
      have hx : v.2 = 0 := norm_le_zero_iff.mp (by linarith)
      exact Prod.ext ht hx
    · rintro rfl; simp
  have hS : IsPreconnected (γ '' Icc 0 1) := isPreconnected_Icc.image γ hγ
  have hcov : γ '' Icc 0 1 ⊆ A ∪ B := by
    rintro v ⟨s, hs, rfl⟩
    have hc := hcausal s hs
    rcases le_or_gt 0 (γ s).1 with h | h
    · left; show ‖(γ s).2‖ ≤ (γ s).1; rwa [abs_of_nonneg h] at hc
    · right; show ‖(γ s).2‖ ≤ -(γ s).1; rwa [abs_of_neg h] at hc
  have h0m : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have h1m : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have hp := pinch_point hS hA hB hcov hAB ⟨γ 0, ⟨0, h0m, rfl⟩, h0⟩ ⟨γ 1, ⟨1, h1m, rfl⟩, h1⟩
  obtain ⟨s, hs, hγs⟩ := hp
  exact ⟨s, hs, hγs⟩

/-- **T3.** -/
theorem apex_disconnects_causal_vectors {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] :
    ¬ IsPreconnected ({v : ℝ × E | ‖v.2‖ ≤ |v.1|} \ {0}) := by
  intro hpc
  set A : Set (ℝ × E) := {v | ‖v.2‖ ≤ v.1}
  set B : Set (ℝ × E) := {v | ‖v.2‖ ≤ -v.1}
  have hA : IsClosed A := isClosed_le (continuous_norm.comp continuous_snd) continuous_fst
  have hB : IsClosed B := isClosed_le (continuous_norm.comp continuous_snd) continuous_fst.neg
  have hAB : A ∩ B = {0} := by
    ext v
    simp only [A, B, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hn := norm_nonneg v.2
      have ht : v.1 = 0 := by linarith
      have hx : v.2 = 0 := norm_le_zero_iff.mp (by linarith)
      exact Prod.ext ht hx
    · rintro rfl; simp
  have hcov : ({v : ℝ × E | ‖v.2‖ ≤ |v.1|} \ {0}) ⊆ A ∪ B := by
    rintro v ⟨hc, _⟩
    simp only [mem_ofPred_eq] at hc
    rcases le_or_gt 0 v.1 with h | h
    · left; show ‖v.2‖ ≤ v.1; rwa [abs_of_nonneg h] at hc
    · right; show ‖v.2‖ ≤ -v.1; rwa [abs_of_neg h] at hc
  have hfut : ((1 : ℝ), (0 : E)) ∈ ({v : ℝ × E | ‖v.2‖ ≤ |v.1|} \ {0}) ∩ A := by
    refine ⟨⟨by simp, ?_⟩, by simp [A]⟩
    simp only [mem_singleton_iff, Prod.ext_iff]; norm_num
  have hpast : ((-1 : ℝ), (0 : E)) ∈ ({v : ℝ × E | ‖v.2‖ ≤ |v.1|} \ {0}) ∩ B := by
    refine ⟨⟨by simp, ?_⟩, by simp [B]⟩
    simp only [mem_singleton_iff, Prod.ext_iff]; norm_num
  have h0 := pinch_point hpc hA hB hcov hAB ⟨_, hfut⟩ ⟨_, hpast⟩
  exact h0.2 rfl

/-- **T4.** -/
theorem orthant_path_through_origin {n : ℕ} (γ : ℝ → (Fin n → ℝ)) (hγ : ContinuousOn γ (Icc 0 1))
    (hsame : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i j, 0 ≤ γ s i * γ s j) (h0 : ∀ i, 0 ≤ γ 0 i) (h1 : ∀ i, γ 1 i ≤ 0) :
    ∃ s ∈ Icc (0 : ℝ) 1, γ s = 0 := by
  set A : Set (Fin n → ℝ) := {x | ∀ i, 0 ≤ x i}
  set B : Set (Fin n → ℝ) := {x | ∀ i, x i ≤ 0}
  have hA : IsClosed A := by
    simp only [A, ofPred_forall]; exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hB : IsClosed B := by
    simp only [B, ofPred_forall]; exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const
  have hAB : A ∩ B = {0} := by
    ext x
    simp only [A, B, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩; funext i; exact le_antisymm (h2 i) (h1 i)
    · rintro rfl; simp
  have hS : IsPreconnected (γ '' Icc 0 1) := isPreconnected_Icc.image γ hγ
  have hcov : γ '' Icc 0 1 ⊆ A ∪ B := by
    rintro x ⟨s, hs, rfl⟩
    by_cases h : ∃ i, 0 < γ s i
    · obtain ⟨i, hi⟩ := h
      left; intro j; exact (mul_nonneg_iff_of_pos_left hi).mp (hsame s hs i j)
    · push_neg at h; right; exact h
  have h0m : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have h1m : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  obtain ⟨s, hs, hγs⟩ := pinch_point hS hA hB hcov hAB ⟨γ 0, ⟨0, h0m, rfl⟩, h0⟩ ⟨γ 1, ⟨1, h1m, rfl⟩, h1⟩
  exact ⟨s, hs, hγs⟩

/-- **T5.** Coordinates `(law, good)`. -/
theorem lawful_good_to_chaotic_evil (γ : ℝ → ℝ × ℝ) (hγ : ContinuousOn γ (Icc 0 1))
    (hnomixed : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (γ s).1 * (γ s).2) (hLG : 0 ≤ (γ 0).1 ∧ 0 ≤ (γ 0).2)
    (hCE : (γ 1).1 ≤ 0 ∧ (γ 1).2 ≤ 0) : ∃ s ∈ Icc (0 : ℝ) 1, γ s = (0, 0) := by
  set A : Set (ℝ × ℝ) := {v | 0 ≤ v.1 ∧ 0 ≤ v.2}
  set B : Set (ℝ × ℝ) := {v | v.1 ≤ 0 ∧ v.2 ≤ 0}
  have hA : IsClosed A := (isClosed_le continuous_const continuous_fst).inter (isClosed_le continuous_const continuous_snd)
  have hB : IsClosed B := (isClosed_le continuous_fst continuous_const).inter (isClosed_le continuous_snd continuous_const)
  have hAB : A ∩ B = {(0, 0)} := by
    ext v
    simp only [A, B, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact Prod.ext (le_antisymm h3 h1) (le_antisymm h4 h2)
    · rintro rfl; simp
  have hS : IsPreconnected (γ '' Icc 0 1) := isPreconnected_Icc.image γ hγ
  have hcov : γ '' Icc 0 1 ⊆ A ∪ B := by
    rintro v ⟨s, hs, rfl⟩
    exact mul_nonneg_iff.mp (hnomixed s hs)
  have h0m : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have h1m : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  obtain ⟨s, hs, hγs⟩ := pinch_point hS hA hB hcov hAB ⟨γ 0, ⟨0, h0m, rfl⟩, hLG⟩ ⟨γ 1, ⟨1, h1m, rfl⟩, hCE⟩
  exact ⟨s, hs, hγs⟩

end PinchPoint
