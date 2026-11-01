import Mathlib

/-!
# Octonions by Cayley–Dickson doubling of the integer quaternions; Moufang loop of signed units

Octonions are pairs `(a, b)` of Mathlib integer quaternions `ℍ[ℤ]` (whose multiplication table
is Mathlib's, not typed here), with the Cayley–Dickson product

  `(a, b) * (c, d) = (a * c - star d * b, d * a + b * star c)`.

The basis units are `e 0, e 1, e 2, e 3 = (1,0), (i,0), (j,0), (k,0)` and
`e 4, e 5, e 6, e 7 = (0,1), (0,i), (0,j), (0,k)`. `units16` is the list `±e 0, ..., ±e 7`.

PROVED
* `not_assoc`: `(e 1 * e 2) * e 4 ≠ e 1 * (e 2 * e 4)`.
* `left_alternative`, `right_alternative`: `x * (x * y) = (x * x) * y` and
  `(y * x) * x = y * (x * x)` for all octonions `x y` (by full coordinate expansion).
* `moufang`: `z * (x * (z * y)) = ((z * x) * z) * y` for all octonions;
  `moufang_units16` its restriction to the 16 signed basis units.
* `units16_mul_mem`: the 16 signed basis units are closed under multiplication.
* `one_mul_units16`, `units16_inv`: `1 = e 0` is a two-sided identity and `conj x` is a
  two-sided inverse in `units16` of every `x ∈ units16`.
* `units16_left_div`, `units16_right_div`: for `a b ∈ units16` there is a unique `x ∈ units16`
  with `a * x = b`, and a unique `y ∈ units16` with `y * a = b` (the loop axioms).
* `units16_not_assoc`, `not_group`: multiplication on the subtype `U` of the 16 units is not
  associative, hence there is no `Group U` structure whose multiplication is the octonion product.

INTERPRETED
* `U` with the induced product, identity `1` and unique two-sided division is a loop
  (Mathlib has no `Loop` class; the loop axioms are stated directly as `units16_left_div`,
  `units16_right_div`, `one_mul_units16`). It is a Moufang loop by `moufang_units16`.
-/

open Quaternion

namespace OctonionMoufangLoopB

/-- Integer quaternions (Mathlib's `ℍ[ℤ]`). -/
abbrev Q := ℍ[ℤ]

instance : DecidableEq Q := fun x y =>
  decidable_of_iff (x.re = y.re ∧ x.imI = y.imI ∧ x.imJ = y.imJ ∧ x.imK = y.imK)
    (by
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact QuaternionAlgebra.ext h1 h2 h3 h4
      · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩)

/-- Octonions over `ℤ`: Cayley–Dickson pairs of quaternions. -/
@[ext]
structure Oct where
  a : Q
  b : Q
deriving DecidableEq

/-- Cayley–Dickson product `(a, b) * (c, d) = (a c - star d * b, d a + b star c)`. -/
instance : Mul Oct := ⟨fun x y => ⟨x.a * y.a - star y.b * x.b, y.b * x.a + x.b * star y.a⟩⟩
instance : Neg Oct := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : One Oct := ⟨⟨1, 0⟩⟩

/-- Octonion conjugate `(a, b) ↦ (star a, -b)`. -/
def conj (x : Oct) : Oct := ⟨star x.a, -x.b⟩

@[simp] lemma mul_a (x y : Oct) : (x * y).a = x.a * y.a - star y.b * x.b := rfl
@[simp] lemma mul_b (x y : Oct) : (x * y).b = y.b * x.a + x.b * star y.a := rfl

/-- An octonion from its eight integer coordinates. -/
def mk8 (x0 x1 x2 x3 x4 x5 x6 x7 : ℤ) : Oct := ⟨⟨x0, x1, x2, x3⟩, ⟨x4, x5, x6, x7⟩⟩
/-- Coordinates of an octonion. -/
lemma eta (x : Oct) : x = mk8 x.a.re x.a.imI x.a.imJ x.a.imK x.b.re x.b.imI x.b.imJ x.b.imK := rfl
set_option maxHeartbeats 0 in
/-- The Cayley–Dickson product in coordinates (derived from the definition). -/
lemma mk8_mul (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : ℤ) :
    mk8 x0 x1 x2 x3 x4 x5 x6 x7 * mk8 y0 y1 y2 y3 y4 y5 y6 y7 =
    mk8 (x0*y0 - x1*y1 - x2*y2 - x3*y3 - y4*x4 - y5*x5 - y6*x6 - y7*x7)
        (x0*y1 + x1*y0 + x2*y3 - x3*y2 - y4*x5 + y5*x4 + y6*x7 - y7*x6)
        (x0*y2 - x1*y3 + x2*y0 + x3*y1 - y4*x6 - y5*x7 + y6*x4 + y7*x5)
        (x0*y3 + x1*y2 - x2*y1 + x3*y0 - y4*x7 + y5*x6 - y6*x5 + y7*x4)
        (y4*x0 - y5*x1 - y6*x2 - y7*x3 + x4*y0 + x5*y1 + x6*y2 + x7*y3)
        (y4*x1 + y5*x0 + y6*x3 - y7*x2 - x4*y1 + x5*y0 - x6*y3 + x7*y2)
        (y4*x2 - y5*x3 + y6*x0 + y7*x1 - x4*y2 + x5*y3 + x6*y0 - x7*y1)
        (y4*x3 + y5*x2 - y6*x1 + y7*x0 - x4*y3 - x5*y2 + x6*y1 + x7*y0) := by
  simp only [mk8, HMul.hMul, Mul.mul]
  ext <;> simp <;> ring
/-- Quaternion basis `1, i, j, k` for `n = 0, 1, 2, 3`. -/
def qb (n : ℕ) : Q :=
  ⟨if n = 0 then 1 else 0, if n = 1 then 1 else 0, if n = 2 then 1 else 0,
    if n = 3 then 1 else 0⟩

/-- Octonion basis units `e 0, ..., e 7`. -/
def e (i : Fin 8) : Oct := if i.val < 4 then ⟨qb i.val, 0⟩ else ⟨0, qb (i.val - 4)⟩

/-- The 16 signed basis units `±e 0, ..., ±e 7`. -/
def units16 : List Oct := (List.finRange 8).map e ++ (List.finRange 8).map (fun i => -e i)

theorem units16_length : units16.length = 16 := by decide

theorem units16_nodup : units16.Nodup := by decide

theorem one_eq_e0 : (1 : Oct) = e 0 := by decide

/-! ### (1) Non-associativity -/

theorem not_assoc : (e 1 * e 2) * e 4 ≠ e 1 * (e 2 * e 4) := by decide

/-! ### (2) Alternative laws for all octonions -/

theorem left_alternative (x y : Oct) : x * (x * y) = (x * x) * y := by
  ext <;> simp <;> ring

theorem right_alternative (x y : Oct) : (y * x) * x = y * (x * x) := by
  ext <;> simp <;> ring

/-! ### (3) Moufang identity -/

set_option maxHeartbeats 0 in
theorem moufang (x y z : Oct) : z * (x * (z * y)) = ((z * x) * z) * y := by
  rw [eta x, eta y, eta z]
  simp only [mk8_mul]
  congr 1 <;> ring

theorem moufang_units16 :
    ∀ x ∈ units16, ∀ y ∈ units16, ∀ z ∈ units16, z * (x * (z * y)) = ((z * x) * z) * y :=
  fun x _ y _ z _ => moufang x y z

/-! ### (4) The signed basis units form a loop that is not a group -/

theorem units16_mul_mem : ∀ x ∈ units16, ∀ y ∈ units16, x * y ∈ units16 := by
  decide +kernel

theorem one_mem_units16 : (1 : Oct) ∈ units16 := by decide

theorem one_mul_units16 : ∀ x ∈ units16, 1 * x = x ∧ x * 1 = x := by decide +kernel

theorem units16_inv :
    ∀ x ∈ units16, conj x ∈ units16 ∧ x * conj x = 1 ∧ conj x * x = 1 := by
  decide +kernel

theorem units16_conj_mul_mul : ∀ a ∈ units16, ∀ x ∈ units16, conj a * (a * x) = x := by
  decide +kernel

theorem units16_mul_mul_conj : ∀ a ∈ units16, ∀ x ∈ units16, (x * a) * conj a = x := by
  decide +kernel

theorem units16_left_div (a b : Oct) (ha : a ∈ units16) (hb : b ∈ units16) :
    ∃ x ∈ units16, a * x = b ∧ ∀ x' ∈ units16, a * x' = b → x' = x := by
  refine ⟨conj a * b, units16_mul_mem _ (units16_inv a ha).1 _ hb, ?_, ?_⟩
  · have h := units16_conj_mul_mul (conj a) (units16_inv a ha).1 b hb
    have hc : conj (conj a) = a := by cases a; simp [conj]
    rwa [hc] at h
  · intro x' hx' h
    rw [← h, units16_conj_mul_mul a ha x' hx']

theorem units16_right_div (a b : Oct) (ha : a ∈ units16) (hb : b ∈ units16) :
    ∃ y ∈ units16, y * a = b ∧ ∀ y' ∈ units16, y' * a = b → y' = y := by
  refine ⟨b * conj a, units16_mul_mem _ hb _ (units16_inv a ha).1, ?_, ?_⟩
  · have h := units16_mul_mul_conj (conj a) (units16_inv a ha).1 b hb
    have hc : conj (conj a) = a := by cases a; simp [conj]
    rwa [hc] at h
  · intro y' hy' h
    rw [← h, units16_mul_mul_conj a ha y' hy']

/-- The 16 signed basis units as a type. -/
abbrev U := {x : Oct // x ∈ units16}

instance : Mul U := ⟨fun x y => ⟨x.1 * y.1, units16_mul_mem _ x.2 _ y.2⟩⟩

lemma e_mem (i : Fin 8) : e i ∈ units16 := by revert i; decide

theorem units16_not_assoc :
    ∃ x y z : U, (x * y) * z ≠ x * (y * z) :=
  ⟨⟨e 1, e_mem 1⟩, ⟨e 2, e_mem 2⟩, ⟨e 4, e_mem 4⟩, fun h => not_assoc (congrArg Subtype.val h)⟩

theorem not_group : ¬ ∃ g : Group U, ∀ x y : U, g.mul x y = x * y := by
  rintro ⟨g, hg⟩
  obtain ⟨x, y, z, h⟩ := units16_not_assoc
  apply h
  have := @mul_assoc U g.toSemigroup x y z
  change g.mul (g.mul x y) z = g.mul x (g.mul y z) at this
  rwa [hg, hg, hg, hg] at this

end OctonionMoufangLoopB
