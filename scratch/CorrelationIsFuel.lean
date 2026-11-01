import Mathlib

/-!
# Correlation is fuel, and only joint access can burn it

* M1 `copy_erases_for_free`: the reversible map `(s, e) ↦ (s xor e, e)` (CNOT) is injective, and when the environment
  holds a COPY of the system (`e = s`) it sends the system to `false` while leaving the environment unchanged. Shared
  information erases without consuming blank tape (compare LandauerCounting L2). This is Bennett's uncomputation.
* M2 `additive_energy_sees_only_marginals`: for any additive energy `E(a, b) = Eₐ a + E_b b`, the mean energy under a
  joint distribution equals the mean under the product of its marginals. So the whole free-energy difference between
  a correlated state and its uncorrelated twin is entropic: `kT · I(A; B)`.
* M3 `local_test_blind_to_correlation`: any quantity of `A` alone has the same mean under the joint and under the
  product. Each side, acting alone, cannot see the correlation, let alone burn it.
-/

namespace CorrelationIsFuel

open Finset

/-- **M1.** -/
theorem copy_erases_for_free :
    Function.Injective (fun p : Bool × Bool => (xor p.1 p.2, p.2)) ∧
      ∀ s : Bool, (fun p : Bool × Bool => (xor p.1 p.2, p.2)) (s, s) = (false, s) := by
  refine ⟨?_, fun s => by cases s <;> rfl⟩
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  cases a <;> cases c <;> cases b <;> simp_all

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Marginals of a joint distribution. -/
def margA (p : α → β → ℝ) (a : α) : ℝ := ∑ b, p a b
def margB (p : α → β → ℝ) (b : β) : ℝ := ∑ a, p a b

/-- **M3.** -/
theorem local_test_blind_to_correlation (p : α → β → ℝ) (hp : ∑ a, ∑ b, p a b = 1) (g : α → ℝ) :
    ∑ a, ∑ b, p a b * g a = ∑ a, ∑ b, (margA p a * margB p b) * g a := by
  have hB : ∑ b, margB p b = 1 := by unfold margB; rw [Finset.sum_comm]; exact hp
  have L : ∑ a, ∑ b, p a b * g a = ∑ a, margA p a * g a := by
    unfold margA; apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul]
  have R : ∑ a, ∑ b, (margA p a * margB p b) * g a = ∑ a, margA p a * g a * ∑ b, margB p b := by
    apply Finset.sum_congr rfl; intro a _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
  rw [L, R, hB]; simp

/-- **M2.** -/
theorem additive_energy_sees_only_marginals (p : α → β → ℝ) (hp : ∑ a, ∑ b, p a b = 1) (Ea : α → ℝ)
    (Eb : β → ℝ) : ∑ a, ∑ b, p a b * (Ea a + Eb b) = ∑ a, ∑ b, (margA p a * margB p b) * (Ea a + Eb b) := by
  have hA : ∑ a, margA p a = 1 := by unfold margA; exact hp
  have hB : ∑ b, margB p b = 1 := by unfold margB; rw [Finset.sum_comm]; exact hp
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · exact local_test_blind_to_correlation p hp Ea
  · have L : ∑ a, ∑ b, p a b * Eb b = ∑ b, margB p b * Eb b := by
      rw [Finset.sum_comm]; unfold margB; apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_mul]
    have R : ∑ a, ∑ b, (margA p a * margB p b) * Eb b = (∑ a, margA p a) * ∑ b, margB p b * Eb b := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b _; ring
    rw [L, R, hA, one_mul]

end CorrelationIsFuel
