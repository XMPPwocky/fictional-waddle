/-
# Borromean structure: bound as a triple, free in every pair

PROVED
1. `comm_nontrivial`: in the free group on two generators a, b, the commutator a b a⁻¹ b⁻¹ is not
   the identity (it maps to a non-identity permutation of three points).
2. `comm_dies_without_a`, `comm_dies_without_b`: deleting either generator (sending it to 1) sends
   the commutator to the identity.
3. `pair_shares_uniform_12`, `pair_shares_uniform_13`, `pair_shares_uniform_23`: split a secret bit
   s into three shares (r₁, r₂, s ⊕ r₁ ⊕ r₂) with r₁, r₂ uniform. Every pair of shares takes each of
   its four values for exactly one of the four (r₁, r₂), whatever s is: any two shares say nothing.
4. `three_shares_open`: all three shares together give s back.

INTERPRETED (not formalized)
- Borromean rings: the complement of two unlinked circles has fundamental group free on a, b, and
  the third Borromean ring represents the commutator. Item 1 says the three are linked; item 2 says
  removing either other ring frees the third. The topology is classical and cited, not proved here.
- Linking of a p-sphere with a q-sphere in ℝⁿ needs p + q = n − 1, so two circles can link only
  in n = 3. Cited, not proved here.
- Item 3–4 is the information-theoretic analogue: a three-party bond that no pair carries.
-/

import Mathlib

namespace Borromean

/-- Group commutator. -/
def comm {G : Type*} [Group G] (x y : G) : G := x * y * x⁻¹ * y⁻¹

abbrev F2 := FreeGroup (Fin 2)

def a : F2 := FreeGroup.of 0
def b : F2 := FreeGroup.of 1

/-- Send a and b to two different transpositions of three points. -/
def toPerm : F2 →* Equiv.Perm (Fin 3) :=
  FreeGroup.lift ![Equiv.swap 0 1, Equiv.swap 1 2]

theorem comm_nontrivial : comm a b ≠ 1 := by
  intro h
  have h2 := congrArg toPerm h
  simp only [comm, a, b, toPerm, map_mul, map_inv, map_one, FreeGroup.lift_apply_of] at h2
  revert h2
  decide

/-- Delete generator `i`: send it to 1 and keep the other. -/
def delete (i : Fin 2) : F2 →* F2 :=
  FreeGroup.lift fun j => if j = i then 1 else FreeGroup.of j

theorem comm_dies_without_a : delete 0 (comm a b) = 1 := by
  simp [delete, comm, a, b, FreeGroup.lift_apply_of]

theorem comm_dies_without_b : delete 1 (comm a b) = 1 := by
  simp [delete, comm, a, b, FreeGroup.lift_apply_of]

/-! ## Three-party secret sharing -/

/-- Shares of the secret `s` from random bits `r = (r₁, r₂)`. -/
def shares (s : Bool) (r : Bool × Bool) : Bool × Bool × Bool :=
  (r.1, r.2, xor s (xor r.1 r.2))

theorem pair_shares_uniform_12 (s x y : Bool) :
    (Finset.univ.filter fun r : Bool × Bool =>
      ((shares s r).1, (shares s r).2.1) = (x, y)).card = 1 := by
  revert s x y; decide

theorem pair_shares_uniform_13 (s x y : Bool) :
    (Finset.univ.filter fun r : Bool × Bool =>
      ((shares s r).1, (shares s r).2.2) = (x, y)).card = 1 := by
  revert s x y; decide

theorem pair_shares_uniform_23 (s x y : Bool) :
    (Finset.univ.filter fun r : Bool × Bool =>
      ((shares s r).2.1, (shares s r).2.2) = (x, y)).card = 1 := by
  revert s x y; decide

theorem three_shares_open (s : Bool) (r : Bool × Bool) :
    xor (shares s r).1 (xor (shares s r).2.1 (shares s r).2.2) = s := by
  revert s r; decide

end Borromean

#print axioms Borromean.comm_nontrivial
#print axioms Borromean.comm_dies_without_a
#print axioms Borromean.comm_dies_without_b
#print axioms Borromean.pair_shares_uniform_12
#print axioms Borromean.pair_shares_uniform_13
#print axioms Borromean.pair_shares_uniform_23
#print axioms Borromean.three_shares_open
