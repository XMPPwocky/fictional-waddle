/-
# Averaging is canonical; picking is never symmetric

Two ways to send each class of a symmetry back to one thing.

PROVED
1. `averaging_unique`: on a real vector space with a linear involution τ, the averaging map
   P v = (v + τ v)/2 is the only linear map that (a) fixes every τ-fixed vector and (b) ignores the
   symmetry, P ∘ τ = P. Symmetry forces uniqueness.
2. `averaging_ignores_swap`, `averaging_fixes_fixed`: the averaging map has both properties.
3. `no_symmetric_pick`: on a two-element set where the swap identifies the two elements (one class),
   no choice of representative is invariant under the swap. Symmetry rules out existence.
4. `pick_exists`: a representative of every class of any equivalence relation does exist, using
   `Quotient.out`, which is built on the axiom of choice.

INTERPRETED (not formalized)
- A deterministic perfect obfuscator outputs a program, a member of its class, so it is a pick (item 4
  shows picks exist; item 3 shows a symmetric one need not). Real obfuscators are randomized and can
  output a random member instead. CoCo outputs an average, which is canonical (item 1).
- Item 3 is a single two-element instance, not a general statement about group actions.
- "Every partition has a set of representatives" is equivalent to the axiom of choice over ZF (cited).
-/

import Mathlib

namespace AverageOrPick

section Average

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

noncomputable def avg (τ : W →ₗ[ℝ] W) : W →ₗ[ℝ] W := (1 / 2 : ℝ) • (LinearMap.id + τ)

theorem avg_apply (τ : W →ₗ[ℝ] W) (v : W) : avg τ v = (1 / 2 : ℝ) • (v + τ v) := by
  simp [avg]

theorem averaging_fixes_fixed (τ : W →ₗ[ℝ] W) (v : W) (hv : τ v = v) : avg τ v = v := by
  rw [avg_apply, hv, ← two_smul ℝ v, smul_smul]
  norm_num

theorem averaging_ignores_swap (τ : W →ₗ[ℝ] W) (hτ : ∀ v, τ (τ v) = v) (v : W) :
    avg τ (τ v) = avg τ v := by
  rw [avg_apply, avg_apply, hτ, add_comm]

theorem averaging_unique (τ : W →ₗ[ℝ] W) (hτ : ∀ v, τ (τ v) = v) (P : W →ₗ[ℝ] W)
    (hfix : ∀ v, τ v = v → P v = v) (hinv : ∀ v, P (τ v) = P v) : P = avg τ := by
  ext v
  set a := (1 / 2 : ℝ) • (v + τ v)
  set b := (1 / 2 : ℝ) • (v - τ v)
  have hv : v = a + b := by
    simp only [a, b, ← smul_add]
    rw [show v + τ v + (v - τ v) = (2 : ℝ) • v by rw [two_smul]; abel, smul_smul]
    norm_num
  have ha : τ a = a := by
    simp only [a, map_smul, map_add, hτ]
    rw [add_comm]
  have hb : τ b = -b := by
    simp only [b, map_smul, map_sub, hτ, ← smul_neg, neg_sub]
  have hPb : P b = 0 := by
    have h1 : P (τ b) = P b := hinv b
    rw [hb, map_neg] at h1
    have h2 : (2 : ℝ) • P b = 0 := by rw [two_smul]; nth_rewrite 1 [← h1]; abel
    have := smul_eq_zero.mp h2
    rcases this with h | h
    · norm_num at h
    · exact h
  rw [avg_apply, hv, map_add, hfix a ha, hPb, add_zero, map_add, ha, hb]
  rw [show a + b + (a + -b) = (2 : ℝ) • a by rw [two_smul]; abel, smul_smul]
  norm_num

end Average

section Pick

/-- One class containing both booleans; the swap is `not`. A pick sends the class to a member. -/
theorem no_symmetric_pick : ¬ ∃ r : Bool, (!r) = r := by
  rintro ⟨r, hr⟩
  cases r <;> simp at hr

theorem pick_exists {α : Type*} (s : Setoid α) :
    ∃ pick : Quotient s → α, ∀ q, Quotient.mk s (pick q) = q :=
  ⟨Quotient.out, Quotient.out_eq⟩

end Pick

end AverageOrPick

#print axioms AverageOrPick.averaging_fixes_fixed
#print axioms AverageOrPick.averaging_ignores_swap
#print axioms AverageOrPick.averaging_unique
#print axioms AverageOrPick.no_symmetric_pick
#print axioms AverageOrPick.pick_exists
