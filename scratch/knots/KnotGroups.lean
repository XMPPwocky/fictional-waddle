import Mathlib

/-!
# The trefoil's group is the 3 : 2 gear, and its colourings are mirror symmetries

The trefoil's knot group (the fundamental group of its complement) is presented as the 3-strand braid group:
generators `a`, `b` with the braid relation `a b a = b a b`.

PROVED:
* `braid_gives_torus_relation`: in any group, `a b a = b a b` implies `(a b a)² = (a b)³`. With `x = a b a`,
  `y = a b`, this is the presentation `⟨x, y | x² = y³⟩` of the (2, 3) torus knot: one loop around twice equals the
  other around three times, the two clocks of the nine-cell gear.
* `s3_braid`, `s3_not_comm`: the two transpositions of three objects (reflections of a triangle, the symmetry group
  of two mirrors at 60°) satisfy the braid relation and do not commute. So the trefoil's group maps onto this
  non-abelian mirror group; such maps are Fox's three-colourings.
* `abelian_braid_collapses`: in a commutative group the braid relation forces `a = b`. A knot whose group is
  abelian (the unknot's group is ℤ) can only be coloured with one colour, so it has no nontrivial three-colouring.
INTERPRETED (not formalized): that these presentations are the knot groups (Wirtinger, Artin), and that
three-colourability distinguishes the trefoil from the unknot.
-/

namespace KnotGroups

theorem braid_gives_torus_relation {G : Type*} [Group G] (a b : G) (h : a * b * a = b * a * b) :
    (a * b * a) ^ 2 = (a * b) ^ 3 := by
  calc (a * b * a) ^ 2 = (a * b * a) * (b * a * b) := by rw [sq, ← h]
    _ = (a * b) ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]

def s1 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def s2 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

theorem s3_braid : s1 * s2 * s1 = s2 * s1 * s2 := by decide

theorem s3_not_comm : s1 * s2 ≠ s2 * s1 := by decide

theorem abelian_braid_collapses {G : Type*} [CommGroup G] (a b : G) (h : a * b * a = b * a * b) : a = b := by
  have h2 : a * (a * b) = b * (a * b) := by
    calc a * (a * b) = a * b * a := by rw [mul_assoc, mul_comm b a]
      _ = b * a * b := h
      _ = b * (a * b) := by rw [mul_assoc]
  exact mul_right_cancel h2

end KnotGroups
