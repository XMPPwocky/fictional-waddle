/-
# Differentiating a run produces the run reversed; nothing predicts itself

PROVED
1. `backward_is_reversed`: the transpose of a product of matrices A₁ A₂ ⋯ Aₙ (a run of n linear
   steps) is the product of the transposes in reverse order, Aₙᵀ ⋯ A₁ᵀ. Reverse-mode
   differentiation of a run applies the adjoint steps last-to-first.
2. `backward_cost_eq_forward`: if each step's cost depends only on that step, the backward pass,
   which visits the same steps in reverse order, has exactly the same total cost.
3. `no_self_predictor`: if a system can run a program that asks a predictor about itself and does the
   opposite, then no predictor is right about every program.
4. `diagonal_exists_of_fixed_point`: such a contrary program exists whenever every
   transformation of programs has a fixed point (Kleene's recursion theorem, as a hypothesis).

CITED
- Baur–Strassen (1983), the cheap gradient principle: a gradient costs a small constant times the
  function, which item 2 is the bookkeeping core of.
- Hartmanis–Stearns (1965), the time hierarchy theorem: the diagonal argument of item 3 with the cost
  of simulation counted.
-/

import Mathlib

namespace AdjointReversal

open Matrix

theorem backward_is_reversed {n : Type*} [Fintype n] [DecidableEq n] (L : List (Matrix n n ℝ)) :
    L.prodᵀ = (L.map transpose).reverse.prod :=
  Matrix.transpose_list_prod L

theorem backward_cost_eq_forward {Step : Type*} (cost : Step → ℕ) (run : List Step) :
    (run.reverse.map cost).sum = (run.map cost).sum := by
  rw [List.map_reverse, List.sum_reverse]

theorem no_self_predictor {Prog : Type*} (result pred : Prog → Bool)
    (hdiag : ∃ d, result d = !pred d) : ¬ ∀ p, pred p = result p := by
  intro hall
  obtain ⟨d, hd⟩ := hdiag
  have := hall d
  rw [hd] at this
  cases h : pred d <;> simp [h] at this

theorem diagonal_exists_of_fixed_point {Prog : Type*} (result pred : Prog → Bool)
    (contrary : Prog → Prog) (hcontrary : ∀ p, result (contrary p) = !pred p)
    (hfix : ∀ t : Prog → Prog, ∃ q, result (t q) = result q) :
    ∃ d, result d = !pred d := by
  obtain ⟨q, hq⟩ := hfix contrary
  exact ⟨q, by rw [← hq, hcontrary]⟩

end AdjointReversal

#print axioms AdjointReversal.backward_is_reversed
#print axioms AdjointReversal.backward_cost_eq_forward
#print axioms AdjointReversal.no_self_predictor
#print axioms AdjointReversal.diagonal_exists_of_fixed_point
