import Mathlib

/-!
# Integral octonions by Cayley–Dickson; the 16 signed basis units form a Moufang loop

Construction. `Oct` is the type of pairs `(a, b)` of integer quaternions `ℍ[ℤ]`
(Mathlib's `Quaternion ℤ`, so `i² = j² = k² = -1`, `i j = k`), with the
Cayley–Dickson product

  `(a, b) * (c, d) = (a * c - star d * b, d * a + b * star c)`

where `star` is quaternion conjugation. No octonion multiplication table is typed:
every product is computed from Mathlib's quaternion product. The basis units are
`e 0, e 1, e 2, e 3 = (1,0), (i,0), (j,0), (k,0)` and
`e 4, e 5, e 6, e 7 = (0,1), (0,i), (0,j), (0,k)`; the signed basis units are
`unit (n, s) = ±e n` (minus when `s = true`), indexed by `Fin 8 × Bool`.

PROVED
* `not_associative`: `(e 1 * e 2) * e 4 ≠ e 1 * (e 2 * e 4)`.
* `left_alternative`, `right_alternative`: `x * (x * y) = (x * x) * y` and
  `(y * x) * x = y * (x * x)` for ALL octonions `x y` (by `ring` on components),
  not only for basis units.
* `moufang`: `z * (x * (z * y)) = ((z * x) * z) * y` for ALL octonions `x y z`
  (by `ring` on components); `moufang_units` is its specialisation to the 16 signed
  basis units. Since (2) and (3) are proved for all octonions, no separate
  case check on units is included.
* `unit_injective`: the 16 signed basis units are pairwise distinct.
* `units_closed`: the product of two signed basis units is a signed basis unit.
* `one_eq_unit`, `unit_inv`: `1 = e 0` is a signed basis unit, and every signed basis
  unit `u` has a signed basis unit `v` with `u * v = 1` and `v * u = 1`.
* `left_inverse_property`, `right_inverse_property`: `u⁻¹ (u x) = x = u (u⁻¹ x)` and
  `(y u) u⁻¹ = y = (y u⁻¹) u` for signed basis units, where `u⁻¹ = unit (uinv p)`.
* `one_mul_unit`: `1` is a two-sided identity on the signed basis units.
* `units_left_div`, `units_right_div`: for signed basis units `a b`, the equations
  `a * x = b` and `y * a = b` each have exactly one solution among the signed basis
  units (unique left and right division, i.e. the quasigroup axiom).
* `units_not_assoc`: the multiplication on the 16 signed basis units is not
  associative, so this loop is not a group.

INTERPRETED
* "Loop" is rendered as: a set closed under the product, containing the identity
  `1`, with unique left and right division inside the set (`units_closed`,
  `one_eq_unit`, `one_mul_unit`, `units_left_div`, `units_right_div`). No loop typeclass is used,
  since Mathlib has none.
* "Not a group" is rendered as the failure of associativity on the set
  (`units_not_assoc`); any group operation is associative.
* Finite statements about the 16 units are checked by `decide` or
  `decide +kernel` (kernel evaluation of the Cayley–Dickson product over `ℤ`).
-/

namespace OctonionMoufangLoopA

open Quaternion

instance : DecidableEq ℍ[ℤ] := fun a b =>
  decidable_of_iff (a.re = b.re ∧ a.imI = b.imI ∧ a.imJ = b.imJ ∧ a.imK = b.imK)
    (by
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact QuaternionAlgebra.ext h1 h2 h3 h4
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl⟩)

/-- Integral octonions: pairs of integer quaternions. -/
@[ext]
structure Oct where
  fst : ℍ[ℤ]
  snd : ℍ[ℤ]
  deriving DecidableEq

/-- The Cayley–Dickson product `(a, b) * (c, d) = (a c - d̄ b, d a + b c̄)`. -/
instance : Mul Oct where
  mul x y := ⟨x.fst * y.fst - star y.snd * x.snd, y.snd * x.fst + x.snd * star y.fst⟩

instance : One Oct := ⟨⟨1, 0⟩⟩

instance : Neg Oct := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩

@[simp] theorem mul_fst (x y : Oct) : (x * y).fst = x.fst * y.fst - star y.snd * x.snd := rfl
@[simp] theorem mul_snd (x y : Oct) : (x * y).snd = y.snd * x.fst + x.snd * star y.fst := rfl

/-- The quaternion units `1, i, j, k`. -/
def qbasis : Fin 4 → ℍ[ℤ] :=
  ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/-- The octonion basis units `e 0, …, e 7`. -/
def e (n : Fin 8) : Oct :=
  if h : n.val < 4 then ⟨qbasis ⟨n.val, h⟩, 0⟩ else ⟨0, qbasis ⟨n.val - 4, by omega⟩⟩

/-- The signed basis unit `±e n`, with sign `-` when `s = true`. -/
def unit (p : Fin 8 × Bool) : Oct :=
  if p.2 then -e p.1 else e p.1

/-- (1) The Cayley–Dickson product is not associative on basis units. -/
theorem not_associative : (e 1 * e 2) * e 4 ≠ e 1 * (e 2 * e 4) := by
  decide

/-- (2a) Left alternative law, for all octonions. -/
theorem left_alternative (x y : Oct) : x * (x * y) = (x * x) * y := by
  apply Oct.ext <;> apply Quaternion.ext <;>
    simp only [mul_fst, mul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
    Quaternion.imK_add, Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub,
    Quaternion.imK_sub, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star] <;> ring

/-- (2b) Right alternative law, for all octonions. -/
theorem right_alternative (x y : Oct) : (y * x) * x = y * (x * x) := by
  apply Oct.ext <;> apply Quaternion.ext <;>
    simp only [mul_fst, mul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
    Quaternion.imK_add, Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub,
    Quaternion.imK_sub, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star] <;> ring

set_option maxHeartbeats 20000000 in
/-- (3) Moufang identity `z (x (z y)) = ((z x) z) y`, for all octonions. -/
theorem moufang (x y z : Oct) : z * (x * (z * y)) = ((z * x) * z) * y := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨a4, a5, a6, a7⟩⟩ := x
  obtain ⟨⟨b0, b1, b2, b3⟩, ⟨b4, b5, b6, b7⟩⟩ := y
  obtain ⟨⟨c0, c1, c2, c3⟩, ⟨c4, c5, c6, c7⟩⟩ := z
  apply Oct.ext <;> apply Quaternion.ext <;>
    simp only [mul_fst, mul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
    Quaternion.imK_add, Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub,
    Quaternion.imK_sub, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star] <;> ring

/-- (3) on the 16 signed basis units: the specialisation of `moufang`. -/
theorem moufang_units (p q r : Fin 8 × Bool) :
    unit r * (unit p * (unit r * unit q)) = ((unit r * unit p) * unit r) * unit q :=
  moufang _ _ _

/-- The 16 signed basis units are pairwise distinct. -/
theorem unit_injective : Function.Injective unit := by
  intro p q h
  revert p q
  decide

/-- (4a) Closure: the product of two signed basis units is a signed basis unit. -/
theorem units_closed : ∀ p q : Fin 8 × Bool, ∃ r, unit p * unit q = unit r := by
  decide

/-- The identity is the signed basis unit `e 0`. -/
theorem one_eq_unit : (1 : Oct) = unit (0, false) := by
  decide

theorem one_mul_unit : ∀ p : Fin 8 × Bool, 1 * unit p = unit p ∧ unit p * 1 = unit p := by
  decide

/-- Candidate inverse index: `e 0` and `-e 0` are self-inverse, `±e n` for `n ≠ 0` has
inverse `∓e n`. Correctness is checked in `unit_mul_uinv`. -/
def uinv (p : Fin 8 × Bool) : Fin 8 × Bool :=
  if p.1 = 0 then p else (p.1, !p.2)

theorem unit_mul_uinv :
    ∀ p : Fin 8 × Bool, unit p * unit (uinv p) = 1 ∧ unit (uinv p) * unit p = 1 := by
  decide

/-- (4b) Two-sided inverses inside the signed basis units. -/
theorem unit_inv (p : Fin 8 × Bool) : ∃ q, unit p * unit q = 1 ∧ unit q * unit p = 1 :=
  ⟨uinv p, unit_mul_uinv p⟩

theorem left_inverse_property :
    ∀ a x : Fin 8 × Bool,
      unit (uinv a) * (unit a * unit x) = unit x ∧ unit a * (unit (uinv a) * unit x) = unit x := by
  decide +kernel

theorem right_inverse_property :
    ∀ a y : Fin 8 × Bool,
      (unit y * unit a) * unit (uinv a) = unit y ∧ (unit y * unit (uinv a)) * unit a = unit y := by
  decide +kernel

/-- Unique left division in the signed basis units. -/
theorem units_left_div (a b : Fin 8 × Bool) :
    (∃ x, unit a * unit x = unit b) ∧
      ∀ x x', unit a * unit x = unit b → unit a * unit x' = unit b → x = x' := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := units_closed (uinv a) b
    exact ⟨r, by rw [← hr]; exact (left_inverse_property a b).2⟩
  · intro x x' h h'
    apply unit_injective
    rw [← (left_inverse_property a x).1, ← (left_inverse_property a x').1, h, h']

/-- Unique right division in the signed basis units. -/
theorem units_right_div (a b : Fin 8 × Bool) :
    (∃ y, unit y * unit a = unit b) ∧
      ∀ y y', unit y * unit a = unit b → unit y' * unit a = unit b → y = y' := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := units_closed b (uinv a)
    exact ⟨r, by rw [← hr]; exact (right_inverse_property a b).2⟩
  · intro y y' h h'
    apply unit_injective
    rw [← (right_inverse_property a y).1, ← (right_inverse_property a y').1, h, h']

/-- (4c) The signed basis units do not form a group: their product is not associative. -/
theorem units_not_assoc :
    ∃ p q r : Fin 8 × Bool, (unit p * unit q) * unit r ≠ unit p * (unit q * unit r) :=
  ⟨(1, false), (2, false), (4, false), by simpa [unit] using not_associative⟩

end OctonionMoufangLoopA
