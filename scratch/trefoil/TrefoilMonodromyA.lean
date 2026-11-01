import Mathlib

/-!
# Periodic monodromy of the trefoil singularity x² + y³

PROVED
* `omega_pow_three`, `omega_ne_one`, `omega_isPrimitiveRoot`: ω = exp(2πi/3) satisfies ω³ = 1,
  ω ≠ 1, and is a primitive cube root of unity.
* `f_comp_h`: f ∘ h = f for f(x, y) = x² + y³ and h(x, y) = (−x, ω y).
* `h_mapsTo_fibre`: h maps every fibre {f = t} into itself; `h_bijOn_fibre`: bijectively onto it.
* `h_iterate_six`: h^[6] = id.
* `h_iterate_moves`: for 1 ≤ k ≤ 5, h^[k] (1, 1) ≠ (1, 1); hence `h_iterate_ne_id`.
* `h_iterate_eq_id_iff`: h^[k] = id ↔ 6 ∣ k; `h_minimalPeriod`: the point (1,1) has
  minimal period 6 = lcm 2 3 under h.
* General case (`g p q ζp ζq`, (x, y) ↦ (ζp x, ζq y)) for p, q ≥ 1 coprime and
  ζp, ζq primitive p-th, q-th roots of unity:
  `g_preserves` (x^p + y^q is invariant), `g_iterate_eq_id_iff` (g^[k] = id ↔ p q ∣ k),
  `g_iterate_pq` (g^[p q] = id), `g_iterate_ne_id` (g^[k] ≠ id for 0 < k < p q),
  `g_minimalPeriod` (minimal period of (1,1) is p q).

INTERPRETED (not formalized; cited from Milnor, *Singular points of complex hypersurfaces*, 1968)
* The link of x² + y³ = 0 at the origin is the trefoil, the torus knot T(2,3).
* h restricted to a Milnor fibre {f = t} is the geometric monodromy of the Milnor fibration
  of this weighted-homogeneous singularity; so the trefoil's fibration has periodic
  monodromy of order 6.
-/

namespace TrefoilMonodromyA

open Complex

/-- ω = exp(2πi/3). -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- f(x, y) = x² + y³. -/
def f (z : ℂ × ℂ) : ℂ := z.1 ^ 2 + z.2 ^ 3

/-- h(x, y) = (−x, ω y). -/
noncomputable def h (z : ℂ × ℂ) : ℂ × ℂ := (-z.1, ω * z.2)

/-- The general weighted-homogeneous map (x, y) ↦ (ζp x, ζq y). -/
def g (ζp ζq : ℂ) (z : ℂ × ℂ) : ℂ × ℂ := (ζp * z.1, ζq * z.2)

theorem omega_isPrimitiveRoot : IsPrimitiveRoot ω 3 := by
  have := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  simpa [ω] using this

theorem omega_pow_three : ω ^ 3 = 1 := omega_isPrimitiveRoot.pow_eq_one

theorem omega_ne_one : ω ≠ 1 := omega_isPrimitiveRoot.ne_one (by norm_num)

theorem neg_one_isPrimitiveRoot : IsPrimitiveRoot (-1 : ℂ) 2 :=
  IsPrimitiveRoot.neg_one 0 (by norm_num)

theorem h_eq_g : h = g (-1) ω := by
  funext z
  simp [h, g]

theorem f_comp_h : f ∘ h = f := by
  funext z
  simp only [Function.comp, f, h]
  rw [mul_pow, omega_pow_three, one_mul, neg_sq]

theorem h_mapsTo_fibre (t : ℂ) : Set.MapsTo h {z | f z = t} {z | f z = t} := by
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz ⊢
  rw [← hz, ← Function.comp_apply (f := f), f_comp_h]

theorem g_iterate_apply (ζp ζq : ℂ) (k : ℕ) (z : ℂ × ℂ) :
    (g ζp ζq)^[k] z = (ζp ^ k * z.1, ζq ^ k * z.2) := by
  induction k generalizing z with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [g, pow_succ, mul_assoc, mul_comm, mul_left_comm]

theorem g_iterate_eq_id_iff' (ζp ζq : ℂ) (k : ℕ) :
    (g ζp ζq)^[k] = id ↔ ζp ^ k = 1 ∧ ζq ^ k = 1 := by
  constructor
  · intro hk
    have := congrFun hk (1, 1)
    rw [g_iterate_apply] at this
    simp only [mul_one, id, Prod.mk.injEq] at this
    exact this
  · rintro ⟨h1, h2⟩
    funext z
    rw [g_iterate_apply, h1, h2]
    simp

theorem g_preserves {p q : ℕ} {ζp ζq : ℂ} (hp : IsPrimitiveRoot ζp p)
    (hq : IsPrimitiveRoot ζq q) (z : ℂ × ℂ) :
    (g ζp ζq z).1 ^ p + (g ζp ζq z).2 ^ q = z.1 ^ p + z.2 ^ q := by
  simp only [g, mul_pow, hp.pow_eq_one, hq.pow_eq_one, one_mul]

theorem g_iterate_eq_id_iff {p q : ℕ} (hpq : Nat.Coprime p q) {ζp ζq : ℂ}
    (hp : IsPrimitiveRoot ζp p) (hq : IsPrimitiveRoot ζq q) (k : ℕ) :
    (g ζp ζq)^[k] = id ↔ p * q ∣ k := by
  rw [g_iterate_eq_id_iff', hp.pow_eq_one_iff_dvd, hq.pow_eq_one_iff_dvd]
  constructor
  · rintro ⟨h1, h2⟩
    exact hpq.mul_dvd_of_dvd_of_dvd h1 h2
  · intro h
    exact ⟨dvd_trans (dvd_mul_right p q) h, dvd_trans (dvd_mul_left q p) h⟩

theorem g_iterate_pq {p q : ℕ} (hpq : Nat.Coprime p q) {ζp ζq : ℂ}
    (hp : IsPrimitiveRoot ζp p) (hq : IsPrimitiveRoot ζq q) :
    (g ζp ζq)^[p * q] = id :=
  (g_iterate_eq_id_iff hpq hp hq _).2 dvd_rfl

theorem g_iterate_ne_id {p q : ℕ} (hp1 : 1 ≤ p) (hq1 : 1 ≤ q) (hpq : Nat.Coprime p q)
    {ζp ζq : ℂ} (hp : IsPrimitiveRoot ζp p) (hq : IsPrimitiveRoot ζq q)
    (k : ℕ) (hk0 : 0 < k) (hk : k < p * q) :
    (g ζp ζq)^[k] ≠ id := by
  have _ := hp1
  have _ := hq1
  rw [Ne, g_iterate_eq_id_iff hpq hp hq]
  intro hd
  exact absurd (Nat.le_of_dvd hk0 hd) (not_le.2 hk)

theorem g_iterate_one_one_eq_iff {p q : ℕ} (hpq : Nat.Coprime p q) {ζp ζq : ℂ}
    (hp : IsPrimitiveRoot ζp p) (hq : IsPrimitiveRoot ζq q) (k : ℕ) :
    (g ζp ζq)^[k] (1, 1) = (1, 1) ↔ p * q ∣ k := by
  rw [← g_iterate_eq_id_iff hpq hp hq, g_iterate_eq_id_iff', g_iterate_apply]
  simp

theorem g_minimalPeriod {p q : ℕ} (hp1 : 1 ≤ p) (hq1 : 1 ≤ q) (hpq : Nat.Coprime p q)
    {ζp ζq : ℂ} (hp : IsPrimitiveRoot ζp p) (hq : IsPrimitiveRoot ζq q) :
    Function.minimalPeriod (g ζp ζq) (1, 1) = p * q := by
  have hpos : 0 < p * q := Nat.mul_pos hp1 hq1
  have hper : Function.IsPeriodicPt (g ζp ζq) (p * q) (1, 1) :=
    (g_iterate_one_one_eq_iff hpq hp hq _).2 dvd_rfl
  have hdvd : Function.minimalPeriod (g ζp ζq) (1, 1) ∣ p * q := hper.minimalPeriod_dvd
  have hmpos : 0 < Function.minimalPeriod (g ζp ζq) (1, 1) := hper.minimalPeriod_pos hpos
  have hback : p * q ∣ Function.minimalPeriod (g ζp ζq) (1, 1) :=
    (g_iterate_one_one_eq_iff hpq hp hq _).1 (Function.isPeriodicPt_minimalPeriod _ _)
  exact Nat.dvd_antisymm hdvd hback

theorem two_three_coprime : Nat.Coprime 2 3 := by norm_num

theorem h_iterate_eq_id_iff (k : ℕ) : h^[k] = id ↔ 6 ∣ k := by
  rw [h_eq_g, g_iterate_eq_id_iff two_three_coprime neg_one_isPrimitiveRoot
    omega_isPrimitiveRoot]

theorem h_iterate_six : h^[6] = id := (h_iterate_eq_id_iff 6).2 dvd_rfl

theorem h_iterate_moves (k : ℕ) (hk1 : 1 ≤ k) (hk5 : k ≤ 5) :
    h^[k] (1, 1) ≠ (1, 1) := by
  rw [h_eq_g, Ne, g_iterate_one_one_eq_iff two_three_coprime neg_one_isPrimitiveRoot
    omega_isPrimitiveRoot]
  intro hd
  have := Nat.le_of_dvd (by omega) hd
  omega

theorem h_iterate_ne_id (k : ℕ) (hk1 : 1 ≤ k) (hk5 : k ≤ 5) : h^[k] ≠ id := by
  intro hk
  exact h_iterate_moves k hk1 hk5 (by rw [hk]; rfl)

/-- Explicit witnesses: h^[k] (1,1) = ((−1)^k, ω^k), which differs from (1,1). -/
theorem h_iterate_one_one (k : ℕ) : h^[k] (1, 1) = ((-1) ^ k, ω ^ k) := by
  rw [h_eq_g, g_iterate_apply]
  simp

theorem h_minimalPeriod : Function.minimalPeriod h (1, 1) = 6 := by
  rw [h_eq_g]
  exact g_minimalPeriod (by norm_num) (by norm_num) two_three_coprime
    neg_one_isPrimitiveRoot omega_isPrimitiveRoot

theorem six_eq_lcm : (6 : ℕ) = Nat.lcm 2 3 := by norm_num

theorem h_bijOn_fibre (t : ℂ) : Set.BijOn h {z | f z = t} {z | f z = t} := by
  refine ⟨h_mapsTo_fibre t, ?_, ?_⟩
  · intro a _ b _ hab
    have := congrArg (h^[5]) hab
    rw [← Function.iterate_succ_apply h 5 a, ← Function.iterate_succ_apply h 5 b,
      h_iterate_six] at this
    exact this
  · intro z hz
    refine ⟨h^[5] z, ?_, ?_⟩
    · induction 5 with
      | zero => exact hz
      | succ n ih => rw [Function.iterate_succ_apply']; exact h_mapsTo_fibre t ih
    · rw [← Function.iterate_succ_apply' h 5 z, h_iterate_six]; rfl

end TrefoilMonodromyA
