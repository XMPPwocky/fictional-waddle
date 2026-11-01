import Mathlib

/-!
# Periodic monodromy of the trefoil singularity `x² + y³`

Let `f (x, y) = x² + y³` on `ℂ × ℂ`, `ω = exp (2πi/3)`, and `h (x, y) = (-x, ω y)`.

PROVED
* `omega_isPrimitiveRoot`, `omega_pow_three`, `omega_ne_one`:
  `ω` is a primitive cube root of unity; `ω ^ 3 = 1` and `ω ≠ 1`.
* `f_comp_h`: `f ∘ h = f`; `h_mapsTo_fibre`: `h` maps every fibre `{f = t}` into itself.
* `h_iterate`: `h^[k] (x, y) = ((-1)^k x, ω^k y)`.
* `h_iterate_six`: `h^[6] = id`.
* `h_moves_one_one`: for `1 ≤ k ≤ 5`, `h^[k] (1, 1) ≠ (1, 1)`; hence `h_iterate_ne_id`.
  Explicit values `h_iterate_one_one_1` … `h_iterate_one_one_5`.
* `h_iterate_eq_id_iff`: `h^[k] = id ↔ 6 ∣ k`.
* `orderOf_h`: as an element of the monoid `Function.End (ℂ × ℂ)`, `orderOf h = 6 = Nat.lcm 2 3`.
* General case, for any `p q : ℕ` with `Nat.Coprime p q`, `IsPrimitiveRoot ζp p`,
  `IsPrimitiveRoot ζq q`, and `g (x, y) = (ζp x, ζq y)`:
  - `diag_preserves`: `x^p + y^q` is invariant under `g`;
  - `diag_iterate_eq_id_iff`: `g^[k] = id ↔ p * q ∣ k`;
  - `diag_order_exact` (with `0 < p`, `0 < q`): `g^[p*q] = id` and `g^[k] ≠ id` for `0 < k < p*q`;
  - `orderOf_diag`: `orderOf g = p * q` in `Function.End (ℂ × ℂ)`.
  The `(2,3)` statements are also obtained from this with `ζp = -1`, `ζq = ω`.

INTERPRETED (cited, not formalized)
* The link of `{x² + y³ = 0}` with a small sphere is the trefoil, the torus knot `T(2,3)`, and the
  Milnor fibration of `f` has geometric monodromy given by the weighted-homogeneous action `h`
  (Milnor, *Singular Points of Complex Hypersurfaces*, 1968). Under that citation, the results
  above say the trefoil's fibration has periodic monodromy of order exactly `6 = lcm(2,3)`,
  and more generally that of `x^p + y^q` (coprime `p, q`) has order `p q`.
-/

namespace TrefoilMonodromyB

open Complex

/-- `ω = exp (2πi/3)`. -/
noncomputable def ω : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)

/-- `f (x, y) = x² + y³`. -/
def f (z : ℂ × ℂ) : ℂ := z.1 ^ 2 + z.2 ^ 3

/-- `h (x, y) = (-x, ω y)`. -/
noncomputable def h (z : ℂ × ℂ) : ℂ × ℂ := (-z.1, ω * z.2)

/-- Diagonal map `(x, y) ↦ (a x, b y)`. -/
def diag (a b : ℂ) (z : ℂ × ℂ) : ℂ × ℂ := (a * z.1, b * z.2)

/-- `x^p + y^q`. -/
def fpq (p q : ℕ) (z : ℂ × ℂ) : ℂ := z.1 ^ p + z.2 ^ q

theorem omega_isPrimitiveRoot : IsPrimitiveRoot ω 3 := by
  have := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  simpa [ω] using this

theorem omega_pow_three : ω ^ 3 = 1 := omega_isPrimitiveRoot.pow_eq_one

theorem omega_ne_one : ω ≠ 1 := omega_isPrimitiveRoot.ne_one (by norm_num)

theorem neg_one_isPrimitiveRoot : IsPrimitiveRoot (-1 : ℂ) 2 :=
  IsPrimitiveRoot.neg_one 0 (by norm_num)

theorem f_comp_h : f ∘ h = f := by
  funext z
  simp only [Function.comp, f, h]
  rw [mul_pow, omega_pow_three]
  ring

theorem h_mapsTo_fibre (t : ℂ) : Set.MapsTo h {z | f z = t} {z | f z = t} := by
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz ⊢
  rw [← hz, ← Function.comp_apply (f := f) (g := h), f_comp_h]

theorem h_eq_diag : h = diag (-1) ω := by
  funext z
  simp [h, diag]

theorem diag_iterate (a b : ℂ) (k : ℕ) (z : ℂ × ℂ) :
    (diag a b)^[k] z = (a ^ k * z.1, b ^ k * z.2) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [diag, pow_succ]
    ext <;> ring

theorem h_iterate (k : ℕ) (z : ℂ × ℂ) : h^[k] z = ((-1) ^ k * z.1, ω ^ k * z.2) := by
  rw [h_eq_diag, diag_iterate]

theorem diag_iterate_eq_id_iff' (a b : ℂ) (k : ℕ) :
    (diag a b)^[k] = id ↔ a ^ k = 1 ∧ b ^ k = 1 := by
  constructor
  · intro hk
    have := congrFun hk (1, 1)
    rw [diag_iterate] at this
    simp only [mul_one, id, Prod.mk.injEq] at this
    exact this
  · rintro ⟨ha, hb⟩
    funext z
    rw [diag_iterate, ha, hb]
    simp

theorem diag_preserves {p q : ℕ} {ζp ζq : ℂ} (hp : IsPrimitiveRoot ζp p)
    (hq : IsPrimitiveRoot ζq q) : fpq p q ∘ diag ζp ζq = fpq p q := by
  funext z
  simp only [Function.comp, fpq, diag, mul_pow, hp.pow_eq_one, hq.pow_eq_one, one_mul]

theorem diag_iterate_eq_id_iff {p q : ℕ} {ζp ζq : ℂ} (hpq : Nat.Coprime p q)
    (hp : IsPrimitiveRoot ζp p) (hq : IsPrimitiveRoot ζq q) (k : ℕ) :
    (diag ζp ζq)^[k] = id ↔ p * q ∣ k := by
  rw [diag_iterate_eq_id_iff', hp.pow_eq_one_iff_dvd, hq.pow_eq_one_iff_dvd]
  constructor
  · rintro ⟨h1, h2⟩
    exact hpq.mul_dvd_of_dvd_of_dvd h1 h2
  · intro hk
    exact ⟨dvd_trans (dvd_mul_right p q) hk, dvd_trans (dvd_mul_left q p) hk⟩

theorem diag_order_exact {p q : ℕ} {ζp ζq : ℂ} (hpq : Nat.Coprime p q)
    (hp : IsPrimitiveRoot ζp p) (hq : IsPrimitiveRoot ζq q) (_hp0 : 0 < p) (_hq0 : 0 < q) :
    (diag ζp ζq)^[p * q] = id ∧
      ∀ k, 0 < k → k < p * q → (diag ζp ζq)^[k] ≠ id := by
  refine ⟨(diag_iterate_eq_id_iff hpq hp hq _).2 dvd_rfl, ?_⟩
  intro k hk0 hklt hk
  have := Nat.le_of_dvd hk0 ((diag_iterate_eq_id_iff hpq hp hq k).1 hk)
  omega

theorem End_pow_eq_iterate (g : Function.End (ℂ × ℂ)) (n : ℕ) :
    (g ^ n : Function.End (ℂ × ℂ)) = (g : ℂ × ℂ → ℂ × ℂ)^[n] := by
  rfl

theorem orderOf_diag {p q : ℕ} {ζp ζq : ℂ} (hpq : Nat.Coprime p q)
    (hp : IsPrimitiveRoot ζp p) (hq : IsPrimitiveRoot ζq q) (hp0 : 0 < p) (hq0 : 0 < q) :
    orderOf (G := Function.End (ℂ × ℂ)) (diag ζp ζq) = p * q := by
  have hpos : 0 < p * q := Nat.mul_pos hp0 hq0
  obtain ⟨h1, h2⟩ := diag_order_exact hpq hp hq hp0 hq0
  refine (orderOf_eq_iff (G := Function.End (ℂ × ℂ)) (x := diag ζp ζq) hpos).2 ⟨?_, ?_⟩
  · exact (End_pow_eq_iterate _ _).trans h1
  · intro m hm hm0 hc
    exact h2 m hm0 hm ((End_pow_eq_iterate _ _).symm.trans hc)

theorem h_iterate_eq_id_iff (k : ℕ) : h^[k] = id ↔ 6 ∣ k := by
  rw [h_eq_diag, diag_iterate_eq_id_iff (by norm_num) neg_one_isPrimitiveRoot
    omega_isPrimitiveRoot]

theorem h_iterate_six : h^[6] = id := (h_iterate_eq_id_iff 6).2 dvd_rfl

theorem h_iterate_one_one_1 : h^[1] (1, 1) = (-1, ω) := by
  rw [h_iterate]; simp

theorem h_iterate_one_one_2 : h^[2] (1, 1) = (1, ω ^ 2) := by
  rw [h_iterate]; norm_num

theorem h_iterate_one_one_3 : h^[3] (1, 1) = (-1, 1) := by
  rw [h_iterate, omega_pow_three]; norm_num

theorem h_iterate_one_one_4 : h^[4] (1, 1) = (1, ω) := by
  rw [h_iterate, show ω ^ 4 = ω ^ 3 * ω by ring, omega_pow_three]; norm_num

theorem h_iterate_one_one_5 : h^[5] (1, 1) = (-1, ω ^ 2) := by
  rw [h_iterate, show ω ^ 5 = ω ^ 3 * ω ^ 2 by ring, omega_pow_three]; norm_num

theorem h_moves_one_one (k : ℕ) (hk1 : 1 ≤ k) (hk5 : k ≤ 5) : h^[k] (1, 1) ≠ (1, 1) := by
  have hw2 : ω ^ 2 ≠ 1 := omega_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  interval_cases k
  · rw [h_iterate_one_one_1]; simp [Prod.ext_iff]; norm_num
  · rw [h_iterate_one_one_2]; simp [Prod.ext_iff, hw2]
  · rw [h_iterate_one_one_3]; simp [Prod.ext_iff]; norm_num
  · rw [h_iterate_one_one_4]; simp [Prod.ext_iff, omega_ne_one]
  · rw [h_iterate_one_one_5]; simp [Prod.ext_iff]; norm_num

theorem h_iterate_ne_id (k : ℕ) (hk1 : 1 ≤ k) (hk5 : k ≤ 5) : h^[k] ≠ id := by
  intro hk
  exact h_moves_one_one k hk1 hk5 (by rw [hk]; rfl)

theorem orderOf_h : orderOf (G := Function.End (ℂ × ℂ)) h = 6 := by
  rw [h_eq_diag]
  exact orderOf_diag (p := 2) (q := 3) (by norm_num) neg_one_isPrimitiveRoot
    omega_isPrimitiveRoot (by norm_num) (by norm_num)

theorem orderOf_h_eq_lcm : orderOf (G := Function.End (ℂ × ℂ)) h = Nat.lcm 2 3 := by
  rw [orderOf_h]; rfl

end TrefoilMonodromyB
