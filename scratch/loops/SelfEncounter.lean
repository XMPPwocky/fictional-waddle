/-
# A looping machine mostly meets other configurations

Let f be the step function of any deterministic machine, and let x be a configuration that returns
to itself with minimal period p. Sample a time uniformly from p·N steps and look at the
configuration then.

PROVED
1. `visit_iff`: the orbit is at its k-th configuration (k < p) exactly at the times t ≡ k mod p.
2. `self_encounters`: in p·N steps, each of the p configurations is visited exactly N times.
3. `self_encounter_rate`: so a uniformly sampled time shows any given configuration, including
   "yourself", with probability exactly 1/p, and some other configuration with probability 1 − 1/p.
4. `hamilton_threshold`: if meeting yourself is the relatedness r = 1/p, cooperation that costs c and
   gives b to whoever you meet pays off on average (r·b − c > 0) exactly when b > p·c.

INTERPRETED (not formalized)
- For a recurrent Markov chain, Kac's lemma says the mean return time to a state is 1 / π(state),
  so a state with small stationary mass mostly meets others. That stochastic version is cited, not
  proved here; item 3 is its deterministic case.
- Reading "meeting yourself" as relatedness r in Hamilton's rule is the kin-selection reading.
-/

import Mathlib

namespace SelfEncounter

open Function Finset

variable {α : Type*}

theorem visit_iff (f : α → α) (x : α) (hp : 0 < minimalPeriod f x) (k : ℕ)
    (hk : k < minimalPeriod f x) (t : ℕ) :
    f^[t] x = f^[k] x ↔ t % minimalPeriod f x = k := by
  rw [← iterate_mod_minimalPeriod_eq (n := t)]
  constructor
  · intro h
    exact iterate_injOn_Iio_minimalPeriod (Set.mem_Iio.mpr (Nat.mod_lt _ hp)) (Set.mem_Iio.mpr hk) h
  · intro h
    rw [h]

theorem count_mod (p N k : ℕ) (hk : k < p) :
    ((range (p * N)).filter fun t => t % p = k).card = N := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le k) hk
  have hinj : Injective fun j : ℕ => p * j + k := by
    intro a b h
    have : p * a = p * b := by simpa using h
    exact Nat.eq_of_mul_eq_mul_left hp this
  have hset : ((range (p * N)).filter fun t => t % p = k) = (range N).map ⟨_, hinj⟩ := by
    ext t
    simp only [mem_filter, mem_range, mem_map, Embedding.coeFn_mk]
    constructor
    · rintro ⟨ht, hm⟩
      refine ⟨t / p, ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hp]; linarith [mul_comm p N]
      · have := Nat.div_add_mod t p
        rw [hm] at this
        exact this
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, ?_⟩
      · have : j + 1 ≤ N := hj
        nlinarith
      · simp [Nat.add_mod, Nat.mod_eq_of_lt hk]
  rw [hset, card_map, card_range]

theorem self_encounters [DecidableEq α] (f : α → α) (x : α) (hp : 0 < minimalPeriod f x) (k : ℕ)
    (hk : k < minimalPeriod f x) (N : ℕ) :
    ((range (minimalPeriod f x * N)).filter fun t => f^[t] x = f^[k] x).card = N := by
  rw [Finset.filter_congr (fun t _ => visit_iff f x hp k hk t)]
  exact count_mod _ N k hk

theorem self_encounter_rate [DecidableEq α] (f : α → α) (x : α) (hp : 0 < minimalPeriod f x) (k : ℕ)
    (hk : k < minimalPeriod f x) (N : ℕ) (hN : 0 < N) :
    (((range (minimalPeriod f x * N)).filter fun t => f^[t] x = f^[k] x).card : ℚ) /
      (minimalPeriod f x * N : ℕ) = 1 / minimalPeriod f x := by
  rw [self_encounters f x hp k hk N]
  have h1 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : (minimalPeriod f x : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp

theorem hamilton_threshold (p : ℕ) (hp : 0 < p) (b c : ℚ) :
    (1 / (p : ℚ)) * b - c > 0 ↔ b > p * c := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  constructor
  · intro h
    have := mul_lt_mul_of_pos_left h hp'
    field_simp at this
    linarith
  · intro h
    have : (1 / (p : ℚ)) * b - c = (b - p * c) / p := by field_simp
    rw [this]
    exact div_pos (by linarith) hp'

end SelfEncounter

#print axioms SelfEncounter.visit_iff
#print axioms SelfEncounter.self_encounters
#print axioms SelfEncounter.self_encounter_rate
#print axioms SelfEncounter.hamilton_threshold
