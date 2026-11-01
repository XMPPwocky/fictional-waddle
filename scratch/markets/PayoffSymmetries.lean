/-
# Four symmetries of a two-party payoff, and the flip that trades cooperation for conflict

A payoff pair (x, y): what I get and what you get. Write it as a shared part c = (x + y)/2 and a
conflict part d = (x − y)/2, so x = c + d and y = c − d (the CoCo split, pointwise).

PROVED
1. `split_recovers`: x = c + d and y = c − d.
2. `swap_action`: swapping who gets what keeps the shared part and negates the conflict part.
3. `negate_action`: negating both payoffs negates both parts.
4. `swap_negate_action`: doing both keeps the conflict part and negates the shared part.
5. `klein_four`: each of these is its own inverse and they compose like ℤ/2 × ℤ/2.
6. `one_sided_flip_exchanges`: negating only your payoff, (x, y) ↦ (x, −y), exchanges the parts:
   the new shared part is the old conflict part and the new conflict part is the old shared part.
7. `externality_examples`: "I gain a, you lose a" is pure conflict; swapping gives "you gain, I
   lose"; negating both gives the same; swap-and-negate returns it unchanged; only the one-sided
   flip turns it into "we both gain a".

INTERPRETED (not formalized)
- Calling swap "P", negation "C" and their composite "CP" is an analogy, not physics. Under that
  analogy, CP fixes a pure externality rather than turning it into a shared loss. The map that turns
  a pure externality into a common interest is outside this group: it changes one party's sign alone,
  which is what fully pricing the other party's loss into your own payoff would do.
-/

import Mathlib

namespace PayoffSymmetries

noncomputable def shared (p : ℝ × ℝ) : ℝ := (p.1 + p.2) / 2
noncomputable def conflict (p : ℝ × ℝ) : ℝ := (p.1 - p.2) / 2

def swap (p : ℝ × ℝ) : ℝ × ℝ := (p.2, p.1)
def negate (p : ℝ × ℝ) : ℝ × ℝ := (-p.1, -p.2)
def flipYou (p : ℝ × ℝ) : ℝ × ℝ := (p.1, -p.2)

theorem split_recovers (p : ℝ × ℝ) : p.1 = shared p + conflict p ∧ p.2 = shared p - conflict p := by
  constructor <;> simp [shared, conflict] <;> ring

theorem swap_action (p : ℝ × ℝ) : shared (swap p) = shared p ∧ conflict (swap p) = -conflict p := by
  constructor <;> simp [shared, conflict, swap] <;> ring

theorem negate_action (p : ℝ × ℝ) :
    shared (negate p) = -shared p ∧ conflict (negate p) = -conflict p := by
  constructor <;> simp [shared, conflict, negate] <;> ring

theorem swap_negate_action (p : ℝ × ℝ) :
    shared (swap (negate p)) = -shared p ∧ conflict (swap (negate p)) = conflict p := by
  constructor <;> simp [shared, conflict, swap, negate] <;> ring

theorem klein_four (p : ℝ × ℝ) :
    swap (swap p) = p ∧ negate (negate p) = p ∧ swap (negate p) = negate (swap p) ∧
      swap (negate (swap (negate p))) = p := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp [swap, negate]

theorem one_sided_flip_exchanges (p : ℝ × ℝ) :
    shared (flipYou p) = conflict p ∧ conflict (flipYou p) = shared p := by
  constructor <;> simp [shared, conflict, flipYou] <;> ring

theorem externality_examples (a : ℝ) :
    swap (a, -a) = (-a, a) ∧ negate (a, -a) = (-a, a) ∧ swap (negate (a, -a)) = (a, -a) ∧
      flipYou (a, -a) = (a, a) := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [swap, negate, flipYou]

end PayoffSymmetries

#print axioms PayoffSymmetries.split_recovers
#print axioms PayoffSymmetries.swap_action
#print axioms PayoffSymmetries.negate_action
#print axioms PayoffSymmetries.swap_negate_action
#print axioms PayoffSymmetries.klein_four
#print axioms PayoffSymmetries.one_sided_flip_exchanges
#print axioms PayoffSymmetries.externality_examples
