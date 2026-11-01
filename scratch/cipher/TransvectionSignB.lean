import Mathlib

/-!
# Sign of a transvection on bit vectors

Setting: `BV n = Fin n → ZMod 2`, a linear functional `φ : BV n →ₗ[ZMod 2] ZMod 2`, and a
vector `v` with `φ v = 0`. The transvection is `T x = x + φ x • v`.

## PROVED

* `tvLin φ v` is the `ZMod 2`-linear map `x ↦ x + φ x • v` (`tvLin_apply`), and the
  permutation `tvPerm φ v hv` has the same underlying function (`coe_tvPerm`).
* `tvLin_comp_self`: `tvLin φ v ∘ₗ tvLin φ v = LinearMap.id` when `φ v = 0`.
  `tvPerm_sq`: `tvPerm φ v hv ^ 2 = 1`; `tvPerm_involutive`: it is `Function.Involutive`.
* `tvPerm_eq_one`: if `φ = 0 ∨ v = 0` then `tvPerm φ v hv = 1`.
* `fixedPoints_tvPerm`: if `v ≠ 0` the fixed-point set is exactly `LinearMap.ker φ`.
* `support_tvPerm`: if `v ≠ 0` the support is `{x | φ x = 1}`.
* `card_ker_filter`, `card_one_filter`: if `φ ≠ 0`, both `{x | φ x = 0}` and `{x | φ x = 1}`
  have `2 ^ (n - 1)` elements.
* `card_fixedPoints_tvPerm`, `card_support_tvPerm`: if `φ ≠ 0` and `v ≠ 0`, the fixed-point set
  and the support each have `2 ^ (n - 1)` elements.
* `two_le_of_nontrivial`: if `φ ≠ 0`, `v ≠ 0`, `φ v = 0` then `2 ≤ n`.
* `cycleType_tvPerm`: if `φ ≠ 0` and `v ≠ 0`, the cycle type is
  `Multiset.replicate (2 ^ (n - 2)) 2`, i.e. exactly `2 ^ (n - 2)` disjoint transpositions.
* `sign_tvPerm_of_ne`: if `φ ≠ 0` and `v ≠ 0`, `sign (tvPerm φ v hv) = (-1) ^ (2 ^ (n - 2))`.
* `sign_tvPerm` (main result): for every `n ≥ 3`, every `φ`, every `v` with `φ v = 0`,
  `Equiv.Perm.sign (tvPerm φ v hv) = 1`.
* `sign_tvPerm_two`: for `n = 2`, every `φ ≠ 0`, `v ≠ 0` with `φ v = 0` gives sign `-1`.
* `ex2_*`: the explicit `n = 2` transvection `φ = LinearMap.proj 0`, `v = ![0, 1]`
  satisfies `φ v = 0`, `φ ≠ 0`, `v ≠ 0`, equals `Equiv.swap ![1, 0] ![1, 1]`, and has sign `-1`
  (computed both from the general formula and from `Equiv.Perm.sign_swap`).
* `ex3_*`: the explicit `n = 3` transvection `φ = LinearMap.proj 0`, `v = ![0, 1, 0]`
  satisfies `φ v = 0`, `φ ≠ 0`, `v ≠ 0`, so all hypotheses above are jointly satisfiable;
  `ex_trivial` covers the hypothesis `φ = 0 ∨ v = 0`.

## CITED / INTERPRETED (not proved here)

* Standard fact: transvections generate `SL(n, F)`; over `F = ZMod 2`, `SL = GL`, so the result
  says every element of `GL(n, 2)` acts on `(ZMod 2)^n` as an even permutation when `n ≥ 3`.
  This consequence is not formalized in this file.
* The sign computation uses Mathlib's `Equiv.Perm.sign_of_cycleType'` and
  `Equiv.Perm.cycleType_of_pow_prime_eq_one`.
-/

namespace TransvectionSignB

open Equiv Finset

/-- Bit vectors of length `n`. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

lemma zmod2_ne_zero_iff (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by
  constructor
  · exact zmod2_eq_one_of_ne_zero
  · rintro rfl; decide

lemma bv_add_self (w : BV n) : w + w = 0 :=
  funext fun i => zmod2_add_self (w i)

/-- The linear map `x ↦ x + φ x • v`. -/
def tvLin (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) : BV n →ₗ[ZMod 2] BV n :=
  LinearMap.id + φ.smulRight v

@[simp] theorem tvLin_apply (φ : BV n →ₗ[ZMod 2] ZMod 2) (v x : BV n) :
    tvLin φ v x = x + φ x • v := by
  simp [tvLin]

lemma tv_tv (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0) (x : BV n) :
    (x + φ x • v) + φ (x + φ x • v) • v = x := by
  rw [map_add, map_smul, hv, smul_zero, add_zero, add_assoc, ← add_smul, zmod2_add_self,
    zero_smul, add_zero]

/-- The transvection as a permutation of `BV n`. -/
def tvPerm (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0) : Perm (BV n) where
  toFun x := x + φ x • v
  invFun x := x + φ x • v
  left_inv x := tv_tv φ v hv x
  right_inv x := tv_tv φ v hv x

@[simp] theorem tvPerm_apply (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0)
    (x : BV n) : tvPerm φ v hv x = x + φ x • v := rfl

theorem coe_tvPerm (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0) :
    ⇑(tvPerm φ v hv) = ⇑(tvLin φ v) := by
  funext x; simp

theorem tvLin_comp_self (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0) :
    tvLin φ v ∘ₗ tvLin φ v = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  show tvLin φ v (tvLin φ v x) = x
  simp only [tvLin_apply]
  exact tv_tv φ v hv x

theorem tvPerm_sq (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0) :
    tvPerm φ v hv ^ 2 = 1 := by
  ext1 x
  rw [sq, Perm.mul_apply, Perm.one_apply]
  exact tv_tv φ v hv x

theorem tvPerm_involutive (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0) :
    Function.Involutive (tvPerm φ v hv) :=
  fun x => tv_tv φ v hv x

theorem tvPerm_eq_one (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0)
    (h : φ = 0 ∨ v = 0) : tvPerm φ v hv = 1 := by
  rcases h with rfl | rfl
  · ext1 x; simp
  · ext1 x; simp

lemma tvPerm_apply_eq_iff (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0)
    (hv0 : v ≠ 0) (x : BV n) : tvPerm φ v hv x = x ↔ φ x = 0 := by
  rw [tvPerm_apply]
  constructor
  · intro h
    have h' : φ x • v = 0 := by
      have := congrArg (· - x) h
      simpa using this
    rcases smul_eq_zero.mp h' with h1 | h1
    · exact h1
    · exact absurd h1 hv0
  · intro h; simp [h]

theorem fixedPoints_tvPerm (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0)
    (hv0 : v ≠ 0) :
    Function.fixedPoints (tvPerm φ v hv) = (LinearMap.ker φ : Set (BV n)) := by
  ext x
  rw [Function.mem_fixedPoints, Function.IsFixedPt, tvPerm_apply_eq_iff φ v hv hv0]
  simp

theorem support_tvPerm (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0)
    (hv0 : v ≠ 0) :
    (tvPerm φ v hv).support = univ.filter (fun x => φ x = 1) := by
  ext x
  rw [Perm.mem_support, ne_eq, tvPerm_apply_eq_iff φ v hv hv0, ← ne_eq, mem_filter,
    zmod2_ne_zero_iff]
  simp

lemma card_ker_eq_card_one (φ : BV n →ₗ[ZMod 2] ZMod 2) (hφ : φ ≠ 0) :
    #(univ.filter fun x : BV n => φ x = 0) = #(univ.filter fun x : BV n => φ x = 1) := by
  obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (LinearMap.ext h)
  have hw1 : φ w = 1 := zmod2_eq_one_of_ne_zero hw
  apply card_nbij' (· + w) (· + w)
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    rw [map_add, hx, hw1, zero_add]
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    rw [map_add, hx, hw1, zmod2_add_self]
  · intro x _
    simp only [add_assoc, bv_add_self, add_zero]
  · intro x _
    simp only [add_assoc, bv_add_self, add_zero]

lemma card_ker_add_card_one (φ : BV n →ₗ[ZMod 2] ZMod 2) :
    #(univ.filter fun x : BV n => φ x = 0) + #(univ.filter fun x : BV n => φ x = 1) = 2 ^ n := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (BV n)))
    (fun x : BV n => φ x = 0)
  have hc : (univ.filter fun x : BV n => ¬ φ x = 0) = univ.filter fun x : BV n => φ x = 1 := by
    apply filter_congr
    intro x _
    exact zmod2_ne_zero_iff (φ x)
  rw [hc] at h
  rw [h, card_univ]
  simp

theorem card_ker_filter (φ : BV n →ₗ[ZMod 2] ZMod 2) (hφ : φ ≠ 0) :
    #(univ.filter fun x : BV n => φ x = 0) = 2 ^ (n - 1) := by
  have h1 := card_ker_eq_card_one φ hφ
  have h2 := card_ker_add_card_one φ
  rcases n with _ | m
  · simp only [pow_zero] at h2; omega
  · rw [pow_succ] at h2
    simp only [Nat.add_sub_cancel]
    omega

theorem card_one_filter (φ : BV n →ₗ[ZMod 2] ZMod 2) (hφ : φ ≠ 0) :
    #(univ.filter fun x : BV n => φ x = 1) = 2 ^ (n - 1) := by
  rw [← card_ker_eq_card_one φ hφ, card_ker_filter φ hφ]

theorem card_support_tvPerm (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0)
    (hφ : φ ≠ 0) (hv0 : v ≠ 0) : #(tvPerm φ v hv).support = 2 ^ (n - 1) := by
  rw [support_tvPerm φ v hv hv0, card_one_filter φ hφ]

theorem card_fixedPoints_tvPerm (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0)
    (hφ : φ ≠ 0) (hv0 : v ≠ 0) :
    Fintype.card (Function.fixedPoints (tvPerm φ v hv)) = 2 ^ (n - 1) := by
  rw [Perm.card_fixedPoints, Perm.sum_cycleType, card_support_tvPerm φ v hv hφ hv0]
  have h2 := card_ker_add_card_one φ
  rw [card_ker_filter φ hφ, card_one_filter φ hφ] at h2
  have hc : Fintype.card (BV n) = 2 ^ n := by simp
  rw [hc]
  omega

theorem two_le_of_nontrivial (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0)
    (hφ : φ ≠ 0) (hv0 : v ≠ 0) : 2 ≤ n := by
  have hd := Perm.two_dvd_card_support (tvPerm_sq φ v hv)
  rw [card_support_tvPerm φ v hv hφ hv0] at hd
  by_contra hn
  have : n - 1 = 0 := by omega
  rw [this, pow_zero] at hd
  omega

theorem cycleType_tvPerm (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0)
    (hφ : φ ≠ 0) (hv0 : v ≠ 0) :
    (tvPerm φ v hv).cycleType = Multiset.replicate (2 ^ (n - 2)) 2 := by
  have h1 := Perm.cycleType_of_pow_prime_eq_one (p := 2) (tvPerm_sq φ v hv)
  generalize hk : (tvPerm φ v hv).cycleType.card = k at h1
  have h2 := Perm.sum_cycleType (tvPerm φ v hv)
  rw [h1, card_support_tvPerm φ v hv hφ hv0, Multiset.sum_replicate, smul_eq_mul] at h2
  have hn := two_le_of_nontrivial φ v hv hφ hv0
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, pow_succ] at h2
  rw [h1, e2]
  congr 1
  omega

theorem sign_tvPerm_of_ne (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0)
    (hφ : φ ≠ 0) (hv0 : v ≠ 0) :
    Perm.sign (tvPerm φ v hv) = (-1) ^ (2 ^ (n - 2)) := by
  rw [Perm.sign_of_cycleType', cycleType_tvPerm φ v hv hφ hv0, Multiset.map_replicate,
    Multiset.prod_replicate]
  simp

/-- Main result: for `n ≥ 3` every transvection of `(ZMod 2)^n` is an even permutation. -/
theorem sign_tvPerm (hn : 3 ≤ n) (φ : BV n →ₗ[ZMod 2] ZMod 2) (v : BV n) (hv : φ v = 0) :
    Perm.sign (tvPerm φ v hv) = 1 := by
  by_cases h : φ = 0 ∨ v = 0
  · rw [tvPerm_eq_one φ v hv h, map_one]
  · push Not at h
    rw [sign_tvPerm_of_ne φ v hv h.1 h.2]
    apply Even.neg_one_pow
    exact (Nat.even_pow' (by omega)).mpr even_two

/-- For `n = 2` every nontrivial transvection is an odd permutation. -/
theorem sign_tvPerm_two (φ : BV 2 →ₗ[ZMod 2] ZMod 2) (v : BV 2) (hv : φ v = 0)
    (hφ : φ ≠ 0) (hv0 : v ≠ 0) : Perm.sign (tvPerm φ v hv) = -1 := by
  rw [sign_tvPerm_of_ne φ v hv hφ hv0]
  rfl

/-! ### Explicit instances -/

/-- `n = 2`: `φ x = x 0`. -/
def ex2φ : BV 2 →ₗ[ZMod 2] ZMod 2 := LinearMap.proj 0

/-- `n = 2`: `v = (0, 1)`. -/
def ex2v : BV 2 := ![0, 1]

theorem ex2_hv : ex2φ ex2v = 0 := rfl

theorem ex2_φ_ne : ex2φ ≠ 0 := by
  intro h
  have := LinearMap.congr_fun h ![1, 0]
  exact absurd this (by decide)

theorem ex2_v_ne : ex2v ≠ 0 := by
  intro h
  have := congr_fun h 1
  exact absurd this (by decide)

theorem ex2_eq_swap : tvPerm ex2φ ex2v ex2_hv = Equiv.swap ![1, 0] ![1, 1] := by
  ext1 x
  have hx : x = ![x 0, x 1] := by
    funext i; fin_cases i <;> rfl
  rw [hx]
  generalize x 0 = a
  generalize x 1 = b
  fin_cases a <;> fin_cases b <;> decide

theorem ex2_sign : Perm.sign (tvPerm ex2φ ex2v ex2_hv) = -1 :=
  sign_tvPerm_two ex2φ ex2v ex2_hv ex2_φ_ne ex2_v_ne

theorem ex2_sign_via_swap : Perm.sign (tvPerm ex2φ ex2v ex2_hv) = -1 := by
  rw [ex2_eq_swap]
  exact Perm.sign_swap (by decide)

/-- `n = 3`: `φ x = x 0`. -/
def ex3φ : BV 3 →ₗ[ZMod 2] ZMod 2 := LinearMap.proj 0

/-- `n = 3`: `v = (0, 1, 0)`. -/
def ex3v : BV 3 := ![0, 1, 0]

theorem ex3_hv : ex3φ ex3v = 0 := rfl

theorem ex3_φ_ne : ex3φ ≠ 0 := by
  intro h
  have := LinearMap.congr_fun h ![1, 0, 0]
  exact absurd this (by decide)

theorem ex3_v_ne : ex3v ≠ 0 := by
  intro h
  have := congr_fun h 1
  exact absurd this (by decide)

/-- All hypotheses of the nontrivial-case theorems hold at `n = 3` (and `3 ≤ 3`). -/
theorem ex3_hyps : (3 ≤ 3) ∧ ex3φ ex3v = 0 ∧ ex3φ ≠ 0 ∧ ex3v ≠ 0 :=
  ⟨le_refl 3, ex3_hv, ex3_φ_ne, ex3_v_ne⟩

theorem ex3_sign : Perm.sign (tvPerm ex3φ ex3v ex3_hv) = 1 :=
  sign_tvPerm le_rfl ex3φ ex3v ex3_hv

theorem ex3_card_support : #(tvPerm ex3φ ex3v ex3_hv).support = 4 :=
  card_support_tvPerm ex3φ ex3v ex3_hv ex3_φ_ne ex3_v_ne

/-- The hypothesis `φ = 0 ∨ v = 0` (with `φ v = 0`) is satisfiable. -/
theorem ex_trivial : ∃ (φ : BV 3 →ₗ[ZMod 2] ZMod 2) (v : BV 3), φ v = 0 ∧ (φ = 0 ∨ v = 0) :=
  ⟨0, ex3v, rfl, Or.inl rfl⟩

end TransvectionSignB

#print axioms TransvectionSignB.zmod2_add_self
#print axioms TransvectionSignB.zmod2_eq_one_of_ne_zero
#print axioms TransvectionSignB.zmod2_ne_zero_iff
#print axioms TransvectionSignB.bv_add_self
#print axioms TransvectionSignB.tvLin_apply
#print axioms TransvectionSignB.tv_tv
#print axioms TransvectionSignB.tvPerm_apply
#print axioms TransvectionSignB.coe_tvPerm
#print axioms TransvectionSignB.tvLin_comp_self
#print axioms TransvectionSignB.tvPerm_sq
#print axioms TransvectionSignB.tvPerm_involutive
#print axioms TransvectionSignB.tvPerm_eq_one
#print axioms TransvectionSignB.tvPerm_apply_eq_iff
#print axioms TransvectionSignB.fixedPoints_tvPerm
#print axioms TransvectionSignB.support_tvPerm
#print axioms TransvectionSignB.card_ker_eq_card_one
#print axioms TransvectionSignB.card_ker_add_card_one
#print axioms TransvectionSignB.card_ker_filter
#print axioms TransvectionSignB.card_one_filter
#print axioms TransvectionSignB.card_support_tvPerm
#print axioms TransvectionSignB.card_fixedPoints_tvPerm
#print axioms TransvectionSignB.two_le_of_nontrivial
#print axioms TransvectionSignB.cycleType_tvPerm
#print axioms TransvectionSignB.sign_tvPerm_of_ne
#print axioms TransvectionSignB.sign_tvPerm
#print axioms TransvectionSignB.sign_tvPerm_two
#print axioms TransvectionSignB.ex2_hv
#print axioms TransvectionSignB.ex2_φ_ne
#print axioms TransvectionSignB.ex2_v_ne
#print axioms TransvectionSignB.ex2_eq_swap
#print axioms TransvectionSignB.ex2_sign
#print axioms TransvectionSignB.ex2_sign_via_swap
#print axioms TransvectionSignB.ex3_hv
#print axioms TransvectionSignB.ex3_φ_ne
#print axioms TransvectionSignB.ex3_v_ne
#print axioms TransvectionSignB.ex3_hyps
#print axioms TransvectionSignB.ex3_sign
#print axioms TransvectionSignB.ex3_card_support
#print axioms TransvectionSignB.ex_trivial
