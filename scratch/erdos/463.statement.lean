import Mathlib

/-!
# Erdős problem 463 (statement only)

Erdős problem 463 is open. Its statement is recorded as the proposition `Erdos463Conjecture`;
no proof is claimed. Partial results are in `463.lean`.
-/

abbrev Nat.Composite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime

open Filter

namespace Erdos463

/-- CONJECTURE (Erdős problem 463, open): there is `f → ∞` such that for all large `n` some
composite `m` satisfies `n + f n < m < n + minFac m`. -/
def Erdos463Conjecture : Prop := ∃ (f : ℕ → ℕ) (_ : Tendsto f atTop atTop),
    ∀ᶠ n in atTop,
      ∃ m, m.Composite ∧
        n + f n < m ∧ m < n + m.minFac

end Erdos463
