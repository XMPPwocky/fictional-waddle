import Mathlib

/-!
# Erdős problem 279

* CONJECTURE (open, no proof claimed): `Erdos279Conjecture`.
* Unconditional: `erdos_279_iff` (the conjecture is `∀ k ≥ 3, Covers k`), `covers_mono`,
  `erdos_279_of_unbounded` (it suffices to have `Covers k` for arbitrarily large `k`), and
  `covers_one` (the case `k = 1`, outside the range of the problem).
-/

namespace Erdos279

/-- CONJECTURE (Erdős problem 279, open): for `k ≥ 3` there is a choice of residues `a_p mod p`
for every prime `p` so that all sufficiently large `n` equal `a_p + t * p` for some prime `p`
and `t ≥ k`. -/
def Erdos279Conjecture : Prop := ∀ k : Nat, k ≥ 3 →
    ∃ a : Nat → Nat, ∃ N : Nat, (∀ p : Nat, p.Prime → a p < p) ∧
    ∀ n ≥ N, ∃ p : Nat, ∃ t ≥ k, p.Prime ∧ n = a p + t * p

/-! ## Partial results -/

/-- The inner predicate of `Erdos279Conjecture` for a given `k`: there are residues `a_p < p` for all
primes `p` such that every sufficiently large `n` is `a_p + t * p` with `p` prime and `t ≥ k`. -/
def Covers (k : Nat) : Prop :=
  ∃ a : Nat → Nat, ∃ N : Nat, (∀ p : Nat, p.Prime → a p < p) ∧
    ∀ n ≥ N, ∃ p : Nat, ∃ t ≥ k, p.Prime ∧ n = a p + t * p

/-- `Erdos279Conjecture` is exactly `∀ k ≥ 3, Covers k`. -/
theorem erdos_279_iff : Erdos279Conjecture ↔ ∀ k : Nat, k ≥ 3 → Covers k :=
  Iff.rfl

/-- Monotonicity: a choice of residues that works with multipliers `t ≥ k` also works with
multipliers `t ≥ k'` whenever `k' ≤ k`. -/
theorem covers_mono {k k' : Nat} (hk : k' ≤ k) (h : Covers k) : Covers k' := by
  obtain ⟨a, N, ha, hN⟩ := h
  refine ⟨a, N, ha, fun n hn => ?_⟩
  obtain ⟨p, t, ht, hp, hnt⟩ := hN n hn
  exact ⟨p, t, le_trans hk ht, hp, hnt⟩

/-- Consequently, `Covers k` holds for all `k ≥ 3` as soon as it holds for arbitrarily
large `k`. -/
theorem erdos_279_of_unbounded (h : ∀ K : Nat, ∃ k ≥ K, Covers k) :
    ∀ k : Nat, k ≥ 3 → Covers k := by
  intro k _
  obtain ⟨k', hk', hc⟩ := h k
  exact covers_mono hk' hc

/-- The analogue with `k = 1` (outside the range `k ≥ 3` of the problem) is trivially true:
take `a_p = 0` for every `p`; then every `n ≥ 2` is `t * p` with `p` its least prime factor and
`t = n / p ≥ 1`. -/
theorem covers_one : Covers 1 := by
  refine ⟨fun _ => 0, 2, fun p hp => hp.pos, fun n hn => ?_⟩
  have hn1 : n ≠ 1 := by omega
  have hp : (Nat.minFac n).Prime := Nat.minFac_prime hn1
  have hdvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
  refine ⟨Nat.minFac n, n / Nat.minFac n, ?_, hp, ?_⟩
  · exact Nat.div_pos (Nat.minFac_le (by omega)) hp.pos
  · simp [Nat.div_mul_cancel hdvd]

end Erdos279
