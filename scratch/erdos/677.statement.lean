import Mathlib

/-- The least common multiple of `{n+1, ..., n+k}`. -/
def Finset.lcmInterval {α : Type*} [CommSemiring α] [NormalizedGCDMonoid α]
    [Preorder α] [LocallyFiniteOrder α] (n k : α) : α := (Finset.Ioc n (n + k)).lcm id

namespace Erdos677

open Finset

/-- CONJECTURE (Erdős problem 677, open), stated as a `Prop` with no proof claimed:
`M(m,k) ≠ M(n,k)` whenever `m ≥ n + k`. -/
def Erdos677Conjecture : Prop :=
    ∀ (m n k : ℕ), k > 0 → m ≥ n + k → lcmInterval m k ≠ lcmInterval n k

end Erdos677
