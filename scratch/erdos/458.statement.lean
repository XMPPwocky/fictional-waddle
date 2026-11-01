import Mathlib

/-!
# Erdős problem 458 (statement only)

Erdős problem 458 is open. Its statement is recorded as the proposition `Erdos458Conjecture`;
no proof is claimed. `458.lean` proves partial results (conditional forms and a finite
verification), not this statement.
-/

namespace Erdos458

/-- The least common multiple of `1, ..., n`. -/
def lcm_upto (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

/-- CONJECTURE (Erdős problem 458, open): with `p_k` the `k`-th prime (0-indexed via `Nat.nth`),
`lcm(1..p_{k+1}-1) < p_k * lcm(1..p_k)`. -/
def Erdos458Conjecture : Prop :=
    ∀ k : ℕ, lcm_upto ((k + 1).nth Nat.Prime - 1)
     < k.nth Nat.Prime * lcm_upto (k.nth Nat.Prime)

end Erdos458
