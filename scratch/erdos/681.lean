import Mathlib

abbrev Nat.Composite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime

namespace Erdos681

/-- `IsLPF p m` says that `p` is the least prime factor of `m`. -/
def IsLPF (p m : ℕ) : Prop := p.Prime ∧ p ∣ m ∧ ∀ q, q.Prime ∧ q ∣ m → p ≤ q

/-! ### Erdős problem 681 (open): conjecture and a partial result

* CONJECTURE, stated as a `Prop` with no proof claimed: `Erdos681Conjecture`.
* Unconditional: `erdos_681_partial_k1` (the conclusion for `n` whenever `n + 1` is
  composite, with `k = 1`). -/

/-- Partial result: if `n + 1` is composite then `k = 1` witnesses the conclusion for `n`. -/
theorem erdos_681_partial_k1 (n : ℕ) (h : (n + 1).Composite) :
    ∃ k > 0, (n + k).Composite ∧ ∀ p, IsLPF p (n + k) → p > k ^ 2 := by
  refine ⟨1, by norm_num, h, ?_⟩
  intro p hp
  simpa using hp.1.one_lt

/-- CONJECTURE (Erdős problem 681, open), stated as a `Prop` with no proof claimed:
for all large `n` there is `k > 0` with `n + k` composite and least prime factor of `n + k`
greater than `k ^ 2`. -/
def Erdos681Conjecture : Prop :=
    ∀ᶠ n in .atTop, ∃ k > 0, (n + k).Composite ∧ ∀ p, IsLPF p (n + k) → p > k ^ 2

end Erdos681
