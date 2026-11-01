/-
# Tortoise and hare: running too fast can make them miss

On a cycle of length λ, the tortoise starts at position 0 and moves 1 step per tick; the hare starts
g steps ahead. Positions are taken mod λ.

PROVED
1. `slow_hare_meets`: a hare moving 2 steps per tick (speed difference 1) meets the tortoise at some
   tick, for every cycle length λ > 0 and every head start g.
2. `fast_hare_misses`: a hare moving 3 steps per tick (speed difference 2) never meets the tortoise
   when the cycle length is even and the head start is odd: the gap changes by 2 each tick, so its
   parity never changes.

CITED
- Floyd's cycle-finding algorithm. In general, with speed difference d they meet iff gcd(d, λ) divides
  the head start; Floyd uses d = 1.
-/

import Mathlib

namespace HareParity

theorem slow_hare_meets (L g : ℕ) (hL : 0 < L) : ∃ t, t % L = (g + 2 * t) % L := by
  refine ⟨L - g % L, ?_⟩
  have hr := Nat.mod_lt g hL
  have hq := Nat.div_add_mod g L
  have hdvd : L ∣ g + 2 * (L - g % L) - (L - g % L) := by
    refine ⟨g / L + 1, ?_⟩
    rw [mul_add, mul_one]
    generalize L * (g / L) = Q at hq ⊢
    omega
  exact (Nat.modEq_iff_dvd' (by omega)).mpr hdvd

theorem fast_hare_misses (m g t : ℕ) (hg : g % 2 = 1) : t % (2 * m) ≠ (g + 3 * t) % (2 * m) := by
  intro h
  have hmod : t ≡ g + 3 * t [MOD 2 * m] := h
  have hdvd := (Nat.modEq_iff_dvd' (by omega)).mp hmod
  have h2 : 2 ∣ g + 3 * t - t := dvd_trans (Dvd.intro m rfl) hdvd
  omega

end HareParity

#print axioms HareParity.slow_hare_meets
#print axioms HareParity.fast_hare_misses
