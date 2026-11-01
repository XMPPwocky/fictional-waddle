import Mathlib

/-!
# Finite sampled orbit iff rational clock ratio

For `α : ℝ` let `phi α n = ((n : ℝ) * α : AddCircle (1 : ℝ))` for `n : ℕ`.

PROVED
* `phi_eq_nsmul`: `phi α n = n • (α : AddCircle 1)`.
* `range_phi_eq_multiples`: the range of `phi α` is the additive submonoid of multiples of `α`.
* `range_phi_finite_iff`: (a) `Set.range (phi α)` is finite iff `α = r` for some `r : ℚ`.
* `ncard_range_phi`: (b) if `α = p / q` with `q > 0` and `Int.gcd p q = 1`, then
  `(Set.range (phi α)).ncard = q`.
* `dense_range_phi`: (c) if `α` is irrational, `Set.range (phi α)` is dense in `AddCircle 1`.
* `phi_add_int`: (d) for every integer `k`, `phi (α + k) = phi α`.
-/

namespace RationalClockFiniteOrbit

/-- The sampled orbit `n ↦ n α mod 1`. -/
noncomputable def phi (α : ℝ) (n : ℕ) : AddCircle (1 : ℝ) := (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ))

theorem phi_eq_nsmul (α : ℝ) (n : ℕ) : phi α n = n • (α : AddCircle (1 : ℝ)) := by
  rw [phi, ← nsmul_eq_mul, AddCircle.coe_nsmul]

theorem range_phi_eq_multiples (α : ℝ) :
    Set.range (phi α) = (AddSubmonoid.multiples (α : AddCircle (1 : ℝ)) : Set _) := by
  rw [AddSubmonoid.coe_multiples]
  ext x
  simp [phi_eq_nsmul]

theorem range_phi_finite_iff (α : ℝ) :
    (Set.range (phi α)).Finite ↔ ∃ r : ℚ, α = r := by
  rw [range_phi_eq_multiples, finite_multiples, AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div]
  simp [eq_comm]

theorem ncard_range_phi (α : ℝ) (p q : ℤ) (hq : 0 < q) (hpq : Int.gcd p q = 1)
    (hα : α = (p : ℝ) / q) : (Set.range (phi α)).ncard = q := by
  rw [range_phi_eq_multiples, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
    Nat.card_addSubmonoidMultiples]
  have hqn : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq.le
  have hpos : 0 < q.toNat := by omega
  have hg : p.natAbs.gcd q.toNat = 1 := by
    have : q.toNat = q.natAbs := by omega
    rw [this]; exact hpq
  have key := AddCircle.addOrderOf_div_of_gcd_eq_one' (p := (1 : ℝ)) hpos hg
  have hcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by exact_mod_cast hqn
  rw [hcast, mul_one, ← hα] at key
  rw [key, hqn]

theorem dense_range_phi (α : ℝ) (hα : Irrational α) : Dense (Set.range (phi α)) := by
  have h1 : DenseRange (· • (α : AddCircle (1 : ℝ)) : ℤ → AddCircle (1 : ℝ)) := by
    rw [AddCircle.denseRange_zsmul_coe_iff, div_one]
    exact hα
  rw [denseRange_zsmul_iff_nsmul] at h1
  have h2 : Set.range (phi α) = Set.range (· • (α : AddCircle (1 : ℝ)) : ℕ → AddCircle (1 : ℝ)) := by
    congr 1; funext n; exact phi_eq_nsmul α n
  rw [h2]; exact h1

theorem phi_add_int (α : ℝ) (k : ℤ) : phi (α + k) = phi α := by
  funext n
  rw [phi, phi, mul_add, AddCircle.coe_add, add_eq_left, AddCircle.coe_eq_zero_iff]
  exact ⟨n * k, by simp [zsmul_eq_mul]⟩

end RationalClockFiniteOrbit
