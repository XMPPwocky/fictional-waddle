import Mathlib

open Nat

namespace Erdos849

/-- CONJECTURE (Erdős problem 849, open), stated as a `Prop` with no proof claimed:
for every `t ≥ 1` there is `a` such that `choose n k = a` with `1 ≤ k ≤ n/2` has exactly `t`
solutions `n`. -/
def Erdos849Conjecture : Prop :=
    ∀ t ≥ 1, ∃ a : ℕ,
      {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = t

end Erdos849
