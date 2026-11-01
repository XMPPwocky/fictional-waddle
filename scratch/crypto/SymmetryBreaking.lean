/-
# Identical agents cannot pick a leader without something that breaks the symmetry

Two agents run the same deterministic update: each new state depends on its own state and the other's,
via the same rule `step`.

PROVED
1. `stay_equal`: if they start in the same state, they are in the same state after every number of rounds.
2. `no_deterministic_leader`: so for any rule `isLeader` on states, at no round is exactly one of them
   the leader.
3. `coins_break_ties`: with one fair coin each per round, of the 4^k equally likely coin sequences over
   k rounds, exactly 2^k have the two coins agreeing in every round; every other sequence has a round
   where they differ. Whether differing coins actually separate the agents' states depends on the
   update rule using the coins; that is not modelled here.
4. `tie_fraction`: so the chance the tie survives k rounds is (1/2)^k.

CITED
- Angluin, "Local and global properties in networks of processors" (1980): no deterministic protocol
  elects a leader in an anonymous ring of identical processors; randomization or identifiers are needed.
-/

import Mathlib

namespace SymmetryBreaking

variable {S : Type*}

/-- Both agents' states after n rounds. -/
def run (step : S → S → S) : ℕ → S × S → S × S
  | 0, st => st
  | n + 1, st => run step n (step st.1 st.2, step st.2 st.1)

theorem stay_equal (step : S → S → S) (s : S) (n : ℕ) : (run step n (s, s)).1 = (run step n (s, s)).2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih (step s s)

theorem no_deterministic_leader (step : S → S → S) (isLeader : S → Prop) (s : S) (n : ℕ) :
    ¬ (isLeader (run step n (s, s)).1 ∧ ¬ isLeader (run step n (s, s)).2) := by
  rw [stay_equal]
  exact fun h => h.2 h.1

/-- Coin sequences over k rounds for two agents, one bit each per round. -/
abbrev Coins (k : ℕ) := Fin k → Bool × Bool

theorem coins_break_ties (k : ℕ) :
    (Finset.univ.filter fun c : Coins k => ∀ r, (c r).1 = (c r).2).card = 2 ^ k ∧
      Fintype.card (Coins k) = 4 ^ k := by
  constructor
  · have hbij : (Finset.univ.filter fun c : Coins k => ∀ r, (c r).1 = (c r).2) =
        Finset.univ.map ⟨fun b : Fin k → Bool => fun r => (b r, b r), by
          intro b b' h; funext r; exact congrArg Prod.fst (congrFun h r)⟩ := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro h
        exact ⟨fun r => (c r).1, funext fun r => Prod.ext rfl (h r)⟩
      · rintro ⟨b, rfl⟩ r
        rfl
    rw [hbij, Finset.card_map, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  · simp [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool]

theorem tie_fraction (k : ℕ) :
    ((Finset.univ.filter fun c : Coins k => ∀ r, (c r).1 = (c r).2).card : ℚ) /
      Fintype.card (Coins k) = (1 / 2) ^ k := by
  rw [(coins_break_ties k).1, (coins_break_ties k).2]
  push_cast
  rw [show (4 : ℚ) ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]
  have : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
  rw [← mul_pow]; norm_num

end SymmetryBreaking

#print axioms SymmetryBreaking.stay_equal
#print axioms SymmetryBreaking.no_deterministic_leader
#print axioms SymmetryBreaking.coins_break_ties
#print axioms SymmetryBreaking.tie_fraction
