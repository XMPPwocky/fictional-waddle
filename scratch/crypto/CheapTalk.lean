/-
# Cheap talk: Grice works when interests align, Bitfrost when they don't, and the price of robustness

Two equally likely states θ ∈ Bool. The sender sees θ and sends a message m θ ∈ Bool; the receiver
picks an action r(message) ∈ Bool. The receiver scores 1 when the action matches the state. An aligned
sender wants the same; an opposed sender scores 1 when the action does NOT match. Payoffs are counts
over the two states (so 2 = always right, 1 = what the prior alone gives, 0 = always wrong).
An equilibrium: neither side can do better by switching strategy.

PROVED
1. `aligned_truthful_equilibrium`: with an aligned sender, truthful messages read literally form an
   equilibrium in which the receiver is always right (the Gricean case: words carry their meaning).
2. `opposed_only_babbling`: with an opposed sender, every equilibrium leaves the receiver at exactly the
   prior value 1: no equilibrium transmits any information (Crawford–Sobel, in its smallest form).
3. `opposed_babbling_exists`: such an equilibrium exists (constant message, constant action).
4. `powerless_policy`: a receiver policy that ignores messages scores exactly 1 against every sender
   strategy (the Bitfrost move: requests carry no authority).
5. `every_listening_policy_exploitable`: every receiver policy can be held to at most 1 by some sender
   strategy. So the best guaranteed value, over all policies, is 1, the value of having no channel.
6. `robustness_costs_alignment`: the powerless policy scores 1 against a truthful aligned sender, who
   could have given 2.

INTERPRETED
- Item 4 with item 5 shows the sense in which "make cheap talk powerless" is vacuous: a channel nobody
  can influence carries no information, and its guarantee equals having no channel at all.
- Bitfrost gets real information only from a different channel whose sender is aligned with the user
  (the user's own action in the Security Center), not from the program's messages. Grice's maxims are
  the equilibrium behaviour of item 1; implicature lives there and disappears in item 2.

CITED
- Crawford and Sobel, "Strategic Information Transmission" (1982).
-/

import Mathlib

namespace CheapTalk

abbrev Strat := Bool → Bool

/-- Receiver's payoff: number of states where the action matches the state. -/
def uR (m r : Strat) : ℕ := (Finset.univ.filter fun θ : Bool => r (m θ) = θ).card

/-- Opposed sender's payoff: number of states where the action does not match. -/
def uOpp (m r : Strat) : ℕ := (Finset.univ.filter fun θ : Bool => r (m θ) ≠ θ).card

def EqAligned (m r : Strat) : Prop := (∀ m', uR m' r ≤ uR m r) ∧ ∀ r', uR m r' ≤ uR m r
def EqOpposed (m r : Strat) : Prop := (∀ m', uOpp m' r ≤ uOpp m r) ∧ ∀ r', uR m r' ≤ uR m r

instance (m r : Strat) : Decidable (EqAligned m r) := by unfold EqAligned; infer_instance
instance (m r : Strat) : Decidable (EqOpposed m r) := by unfold EqOpposed; infer_instance

theorem aligned_truthful_equilibrium : EqAligned id id ∧ uR id id = 2 := by decide

theorem opposed_only_babbling : ∀ m r : Strat, EqOpposed m r → uR m r = 1 := by decide

theorem opposed_babbling_exists : EqOpposed (fun _ => false) (fun _ => false) := by decide

theorem powerless_policy : ∀ (b : Bool) (m : Strat), uR m (fun _ => b) = 1 := by decide

theorem every_listening_policy_exploitable : ∀ r : Strat, ∃ m : Strat, uR m r ≤ 1 := by decide

theorem robustness_costs_alignment : uR id (fun _ => false) = 1 ∧ uR id id = 2 := by decide

end CheapTalk

#print axioms CheapTalk.aligned_truthful_equilibrium
#print axioms CheapTalk.opposed_only_babbling
#print axioms CheapTalk.opposed_babbling_exists
#print axioms CheapTalk.powerless_policy
#print axioms CheapTalk.every_listening_policy_exploitable
#print axioms CheapTalk.robustness_costs_alignment
