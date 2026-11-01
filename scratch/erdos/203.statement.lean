import Mathlib

/-!
# Erdős problem 203 (statement only)

Erdős problem 203 is open. Its statement is recorded as the proposition `Erdos203Conjecture`;
no proof is claimed. Partial results are in `203.lean`.
-/

namespace Erdos203

/-- CONJECTURE (Erdős problem 203, open): there is `m` coprime to 6 such that
`2^k * 3^l * m + 1` is never prime. -/
def Erdos203Conjecture : Prop := ∃ m, m.Coprime 6 ∧ ∀ k l, ¬ (2^k * 3^l * m + 1).Prime

end Erdos203
