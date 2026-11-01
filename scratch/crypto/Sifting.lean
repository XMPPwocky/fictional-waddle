/-
# Sifting: when two parties can agree on a basis, and what they share when they cannot

Alice picks a basis (Z or X) and a bit uniformly at random and prepares that state; Bob picks a basis
uniformly at random and measures. Bases and bits are `Bool`; states and the Born rule are as in BB84.lean
(copied here so the file is self-contained).

PROVED
1. `joint_total`: the joint probabilities of (Alice's basis, Bob's basis, Alice's bit, Bob's bit) sum to 1.
2. `agree_prob`: the bases agree with probability 1/2.
3. `sifted_bits_match`: when the bases agree, every outcome with Bob's bit different from Alice's has
   joint probability 0.
4. `mismatched_independent`: when the bases differ, every pair (Alice's bit, Bob's bit) has joint
   probability 1/16.
5. `key_rate`: the probability of a round with matching bases and matching bits is 1/2.
Conditioning (not stated in Lean): given matching bases Bob's bit equals Alice's with probability 1;
given mismatched bases the four bit pairs each have probability 1/4, so the bits are independent.

INTERPRETED (not formalized)
- A measurement basis is a partition of outcomes. The parties can agree on a partition only by
  announcing bases and keeping the rounds where they coincide (cut-and-choose between bases); across
  mutually unbiased bases the outcomes are independent, so there is nothing to agree on.
-/

import Mathlib

namespace Sifting

noncomputable def s : ℝ := Real.sqrt 2 / 2

theorem s_sq : s ^ 2 = 1 / 2 := by
  unfold s
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem s_four : s ^ 4 = 1 / 4 := by
  rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, s_sq]
  norm_num

noncomputable def vec : Bool → Bool → ℝ × ℝ
  | false, false => (1, 0)
  | false, true => (0, 1)
  | true, false => (s, s)
  | true, true => (s, -s)

noncomputable def prob (u v : ℝ × ℝ) : ℝ := (u.1 * v.1 + u.2 * v.2) ^ 2

/-- Joint probability of Alice's basis a, Bob's basis b, Alice's bit i, Bob's bit j. -/
noncomputable def joint (a b i j : Bool) : ℝ := (1 / 2) * (1 / 2) * (1 / 2) * prob (vec a i) (vec b j)

theorem prob_values (a b i j : Bool) :
    prob (vec a i) (vec b j) = if a = b then (if i = j then 1 else 0) else 1 / 2 := by
  cases a <;> cases b <;> cases i <;> cases j <;> simp [vec, prob]
  all_goals (try ring_nf)
  all_goals (try simp [s_sq, s_four])
  all_goals (try norm_num)

theorem joint_total : ∑ a : Bool, ∑ b : Bool, ∑ i : Bool, ∑ j : Bool, joint a b i j = 1 := by
  simp only [joint, prob_values, Fintype.sum_bool]
  norm_num

theorem agree_prob :
    ∑ a : Bool, ∑ i : Bool, ∑ j : Bool, joint a a i j = 1 / 2 := by
  simp only [joint, prob_values, Fintype.sum_bool]
  norm_num

theorem sifted_bits_match (a i j : Bool) (hij : i ≠ j) : joint a a i j = 0 := by
  simp [joint, prob_values, hij]

theorem mismatched_independent (a b i j : Bool) (hab : a ≠ b) : joint a b i j = 1 / 16 := by
  simp only [joint, prob_values, hab, if_false]
  norm_num

theorem key_rate : ∑ a : Bool, ∑ i : Bool, joint a a i i = 1 / 2 := by
  simp only [joint, prob_values, Fintype.sum_bool]
  norm_num

end Sifting

#print axioms Sifting.prob_values
#print axioms Sifting.joint_total
#print axioms Sifting.agree_prob
#print axioms Sifting.sifted_bits_match
#print axioms Sifting.mismatched_independent
#print axioms Sifting.key_rate
