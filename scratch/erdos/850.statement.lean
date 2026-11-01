import Mathlib

namespace Erdos850

/-- CONJECTURE (Erdős problem 850, open), stated as a `Prop` with no proof claimed:
there exist distinct `x y` such that each of the pairs `x, y`, `x+1, y+1` and `x+2, y+2`
has the same set of prime factors. -/
def Erdos850Conjecture : Prop :=
    ∃ x y : ℕ, x ≠ y ∧ x.primeFactors = y.primeFactors
      ∧ (x + 1).primeFactors = (y + 1).primeFactors
      ∧ (x + 2).primeFactors = (y + 2).primeFactors

end Erdos850
