import Mathlib

abbrev Nat.Composite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime

namespace Erdos681

/-- `IsLPF p m` says that `p` is the least prime factor of `m`. -/
def IsLPF (p m : ℕ) : Prop := p.Prime ∧ p ∣ m ∧ ∀ q, q.Prime ∧ q ∣ m → p ≤ q

/-- CONJECTURE (Erdős problem 681, open), stated as a `Prop` with no proof claimed:
for all large `n` there is `k > 0` with `n + k` composite and least prime factor of `n + k`
greater than `k ^ 2`. -/
def Erdos681Conjecture : Prop :=
    ∀ᶠ n in .atTop, ∃ k > 0, (n + k).Composite ∧ ∀ p, IsLPF p (n + k) → p > k ^ 2

end Erdos681
