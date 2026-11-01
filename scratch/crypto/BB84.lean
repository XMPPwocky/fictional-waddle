/-
# BB84: cut-and-choose between bases

A qubit is prepared in one of two bases: Z = {(1,0), (0,1)} or X = {(s,s), (s,−s)} with s = √2/2. The
probability of outcome v when measuring state u is (u·v)². Bases are indexed by `Bool`
(false = Z, true = X) and bits by `Bool`.

PROVED
1. `same_basis`: measuring in the preparation basis returns the prepared bit with probability 1 and
   the other bit with probability 0.
2. `unbiased`: measuring in the other basis returns each bit with probability 1/2 (the bases are
   mutually unbiased).
3. `normalized`: the two outcome probabilities sum to 1 in every case.
4. `intercept_resend_error`: if an eavesdropper measures in a uniformly random basis and resends what
   she saw, then on rounds where the two honest parties' bases agree, the receiver's bit differs from
   the sender's with probability exactly 1/4, for every basis and bit the sender used.

INTERPRETED (not formalized)
- Sifting is a cut-and-choose on bases: the parties keep only rounds where their bases agree, where
  they share a bit perfectly (item 1), and discard the rest, where the outcome is a fair coin (item 2).
- Item 4 is why eavesdropping shows up: comparing a sample of sifted bits reveals a 25% error rate.
-/

import Mathlib

namespace BB84

noncomputable def s : ℝ := Real.sqrt 2 / 2

theorem s_sq : s ^ 2 = 1 / 2 := by
  unfold s
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- Basis vector for basis `b` and bit `i`. -/
noncomputable def vec : Bool → Bool → ℝ × ℝ
  | false, false => (1, 0)
  | false, true => (0, 1)
  | true, false => (s, s)
  | true, true => (s, -s)

/-- Probability of outcome v when measuring state u. -/
noncomputable def prob (u v : ℝ × ℝ) : ℝ := (u.1 * v.1 + u.2 * v.2) ^ 2

theorem s_four : s ^ 4 = 1 / 4 := by
  rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, s_sq]
  norm_num

theorem same_basis (b i j : Bool) : prob (vec b i) (vec b j) = if i = j then 1 else 0 := by
  cases b <;> cases i <;> cases j <;> simp [vec, prob]
  all_goals (try ring_nf)
  all_goals (try simp [s_sq, s_four])
  all_goals (try norm_num)

theorem unbiased (i j : Bool) :
    prob (vec false i) (vec true j) = 1 / 2 ∧ prob (vec true i) (vec false j) = 1 / 2 := by
  cases i <;> cases j <;> simp [vec, prob]
  all_goals (try ring_nf)
  all_goals (try simp [s_sq, s_four])
  all_goals (try norm_num)

theorem normalized (b b' i : Bool) :
    prob (vec b i) (vec b' false) + prob (vec b i) (vec b' true) = 1 := by
  cases b <;> cases b' <;> cases i <;> simp [vec, prob]
  all_goals (try ring_nf)
  all_goals (try simp [s_sq, s_four])
  all_goals (try norm_num)

/-- Error probability on a sifted round under intercept-resend with a uniformly random basis. -/
noncomputable def interceptError (b i : Bool) : ℝ :=
  ∑ e : Bool, (1 / 2) * ∑ o : Bool, prob (vec b i) (vec e o) * prob (vec e o) (vec b (!i))

theorem intercept_resend_error (b i : Bool) : interceptError b i = 1 / 4 := by
  cases b <;> cases i <;> simp [interceptError, vec, prob, Fintype.sum_bool]
  all_goals (try ring_nf)
  all_goals (try simp [s_sq, s_four])
  all_goals (try norm_num)

end BB84

#print axioms BB84.same_basis
#print axioms BB84.unbiased
#print axioms BB84.normalized
#print axioms BB84.intercept_resend_error
