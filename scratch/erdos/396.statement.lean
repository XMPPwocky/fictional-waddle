import Mathlib

/-!
# Erdős problem 396 (statement only)

Erdős problem 396 is open. Its statement is recorded as the proposition `Erdos396Conjecture`;
no proof is claimed. Partial results are in `396.lean`.
-/

open Nat

namespace Erdos396

/-- CONJECTURE (Erdős problem 396, open): for every `k` there is `n` with
`∏_{0 ≤ i ≤ k} (n - i)` dividing `binom(2n, n)`. -/
def Erdos396Conjecture : Prop := ∀ k : ℕ, ∃ n : ℕ, descFactorial n (k + 1) ∣ centralBinom n

end Erdos396
