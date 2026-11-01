import Mathlib

/-!
# Erdős problem 463

* CONJECTURE (open, no proof claimed): `Erdos463Conjecture`.
* Unconditional: `minFac_sq_of_prime`, `tendsto_sqrt_div_two`, and `erdos_463_frequently`,
  the weaker statement with "for all large `n`" replaced by "for infinitely many `n`".
-/

abbrev Nat.Composite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime

open Filter

namespace Erdos463

/-- CONJECTURE (Erdős problem 463, open): there is `f → ∞` such that for all large `n` some
composite `m` satisfies `n + f n < m < n + minFac m`. -/
def Erdos463Conjecture : Prop := ∃ (f : ℕ → ℕ) (_ : Tendsto f atTop atTop),
    ∀ᶠ n in atTop,
      ∃ m, m.Composite ∧
        n + f n < m ∧ m < n + m.minFac

/-! ## Partial result

The weaker statement in which "for all large `n`"
is replaced by "for infinitely many `n`", with `f n = Nat.sqrt n / 2`. The witnesses are
`n = p ^ 2 - p + 1` and `m = p ^ 2` for primes `p`. -/

/-- The least prime factor of `p ^ 2` is `p` for a prime `p`. -/
lemma minFac_sq_of_prime {p : ℕ} (hp : p.Prime) : (p ^ 2).minFac = p := by
  have h1 : p ^ 2 ≠ 1 := by
    have := hp.two_le
    nlinarith
  exact (Nat.prime_dvd_prime_iff_eq (Nat.minFac_prime h1) hp).1
    ((Nat.minFac_prime h1).dvd_of_dvd_pow (Nat.minFac_dvd _))

lemma tendsto_sqrt_div_two : Tendsto (fun n : ℕ => Nat.sqrt n / 2) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun b => ⟨(2 * b) * (2 * b), fun n hn => ?_⟩
  have h : 2 * b ≤ Nat.sqrt n := Nat.le_sqrt.2 hn
  omega

/-- For infinitely many `n` (namely `n = p ^ 2 - p + 1`, `p` prime) there is a composite `m`
with `n + Nat.sqrt n / 2 < m < n + m.minFac`. -/
theorem erdos_463_frequently :
    ∃ (f : ℕ → ℕ) (_ : Tendsto f atTop atTop),
      ∃ᶠ n in atTop,
        ∃ m, m.Composite ∧
          n + f n < m ∧ m < n + m.minFac := by
  refine ⟨fun n => Nat.sqrt n / 2, tendsto_sqrt_div_two, ?_⟩
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes (a + 2)
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨s, hs⟩ : ∃ s, s = p ^ 2 := ⟨_, rfl⟩
  have hsp : p * 2 ≤ s := by rw [hs]; nlinarith
  refine ⟨s - p + 1, ?_, p ^ 2, ⟨?_, ?_⟩, ?_, ?_⟩
  · omega
  · rw [← hs]; omega
  · exact Nat.Prime.not_prime_pow' (by norm_num)
  · have hsq : Nat.sqrt (s - p + 1) < p := by
      rw [Nat.sqrt_lt', ← hs]
      omega
    show s - p + 1 + Nat.sqrt (s - p + 1) / 2 < p ^ 2
    rw [← hs]
    omega
  · rw [minFac_sq_of_prime hp, ← hs]
    omega

end Erdos463
