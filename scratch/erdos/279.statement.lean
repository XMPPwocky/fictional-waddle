import Mathlib

/-!
# Erdős problem 279 (statement only)

Erdős problem 279 is open. Its statement is recorded as the proposition `Erdos279Conjecture`;
no proof is claimed. Partial results are in `279.lean`.
-/

namespace Erdos279

/-- CONJECTURE (Erdős problem 279, open): for `k ≥ 3` there is a choice of residues `a_p mod p`
for every prime `p` so that all sufficiently large `n` equal `a_p + t * p` for some prime `p`
and `t ≥ k`. -/
def Erdos279Conjecture : Prop := ∀ k : Nat, k ≥ 3 →
    ∃ a : Nat → Nat, ∃ N : Nat, (∀ p : Nat, p.Prime → a p < p) ∧
    ∀ n ≥ N, ∃ p : Nat, ∃ t ≥ k, p.Prime ∧ n = a p + t * p

end Erdos279
