import Mathlib

/-!
# Lewis signaling games: signaling systems, gauge freedom, and mismatch

Setting: `n` states, `n` signals, `n` acts, all `Fin n`. A sender is `s : Fin n → Fin n`
(state to signal), a receiver is `r : Fin n → Fin n` (signal to act). Communication succeeds
on state `x` iff `r (s x) = x`. A signaling system is a pair with `r ∘ s = id`.

PROVED
* `isSignalingSystem_iff`: `(s, r)` is a signaling system iff there is a permutation `e` of
  `Fin n` with `⇑e = s` and `⇑e.symm = r` (i.e. `s` is a bijection and `r` its inverse).
* `isSignalingSystem_iff_bijective`: same, phrased as `Bijective s ∧ LeftInverse r s ∧
  RightInverse r s`.
* `gauge`: for every permutation `π` of signals, `(π ∘ s, r ∘ π⁻¹)` is again a signaling system.
* `card_signalingSystems`: the number of signaling systems (pairs `(s, r)` with `r ∘ s = id`)
  is `n!`.
* `mismatch_eq_fixedPoints`: if speaker 1 sends with `s` and speaker 2 decodes with `s'⁻¹`,
  the number of correctly communicated states equals the number of fixed points of
  `s'⁻¹ * s` (= `s'⁻¹ ∘ s`), and also equals `n - (s'⁻¹ * s).support.card`.
* `card_perm_apply_eq`: for `n ≥ 1` and any `x y`, exactly `(n-1)!` permutations send `x`
  to `y` (stated as `n * #{σ | σ x = y} = n!`, plus the `(n-1)!` form).
* `sum_mismatch`: for `n ≥ 1`, summed over all `n!` choices of `s'`, the number of correctly
  communicated states is `n!`.
* `expected_mismatch`: the uniform average over `s'` of that number is exactly `1`.
* `expected_success_fraction`: the uniform average over `s'` of the success fraction
  (count / n) is exactly `1 / n`.

INTERPRETED
* "Speaker 1 uses (s, s⁻¹), speaker 2 decodes with s'⁻¹": the cross pair is sender `⇑s`,
  receiver `⇑s'.symm`, for permutations `s s' : Equiv.Perm (Fin n)`; the count is
  `successCount s s'.symm`.
* "Averaged over all n! choices of s' (uniform)": the sum over `s' : Equiv.Perm (Fin n)`
  divided by `Fintype.card (Equiv.Perm (Fin n)) = n!`, computed in `ℚ`.
* The set of signaling systems is the subtype of `(Fin n → Fin n) × (Fin n → Fin n)` cut out
  by `p.2 ∘ p.1 = id`.
-/

namespace LewisSignalingGaugeA

open Finset

variable {n : ℕ}

/-- `(s, r)` is a signaling system iff `r ∘ s = id`. -/
def IsSignalingSystem (s r : Fin n → Fin n) : Prop := r ∘ s = id

instance (s r : Fin n → Fin n) : Decidable (IsSignalingSystem s r) :=
  inferInstanceAs (Decidable (r ∘ s = id))

/-- Number of states on which the sender `s` and receiver `r` communicate correctly. -/
def successCount (s r : Fin n → Fin n) : ℕ := (univ.filter fun x => r (s x) = x).card

theorem isSignalingSystem_iff_bijective (s r : Fin n → Fin n) :
    IsSignalingSystem s r ↔
      Function.Bijective s ∧ Function.LeftInverse r s ∧ Function.RightInverse r s := by
  constructor
  · intro h
    have hl : Function.LeftInverse r s := fun x => congrFun h x
    have hinj : Function.Injective s := hl.injective
    have hbij : Function.Bijective s := Finite.injective_iff_bijective.mp hinj
    refine ⟨hbij, hl, ?_⟩
    intro y
    obtain ⟨x, rfl⟩ := hbij.2 y
    rw [hl x]
  · rintro ⟨_, hl, _⟩
    funext x
    exact hl x

theorem isSignalingSystem_iff (s r : Fin n → Fin n) :
    IsSignalingSystem s r ↔ ∃ e : Equiv.Perm (Fin n), ⇑e = s ∧ ⇑e.symm = r := by
  constructor
  · intro h
    obtain ⟨_, hl, hr⟩ := (isSignalingSystem_iff_bijective s r).mp h
    exact ⟨⟨s, r, hl, hr⟩, rfl, rfl⟩
  · rintro ⟨e, rfl, rfl⟩
    funext x
    simp

theorem gauge (s r : Fin n → Fin n) (π : Equiv.Perm (Fin n)) (h : IsSignalingSystem s r) :
    IsSignalingSystem (π ∘ s) (r ∘ ⇑π⁻¹) := by
  funext x
  have hx : r (s x) = x := congrFun h x
  simp [hx]

/-- The type of signaling systems. -/
abbrev SignalingSystems (n : ℕ) :=
  {p : (Fin n → Fin n) × (Fin n → Fin n) // IsSignalingSystem p.1 p.2}

/-- Signaling systems are the same as permutations. -/
def signalingSystemsEquivPerm (n : ℕ) : SignalingSystems n ≃ Equiv.Perm (Fin n) where
  toFun p :=
    { toFun := p.1.1
      invFun := p.1.2
      left_inv := ((isSignalingSystem_iff_bijective _ _).mp p.2).2.1
      right_inv := ((isSignalingSystem_iff_bijective _ _).mp p.2).2.2 }
  invFun e := ⟨(⇑e, ⇑e.symm), (isSignalingSystem_iff _ _).mpr ⟨e, rfl, rfl⟩⟩
  left_inv p := by
    rcases p with ⟨⟨s, r⟩, h⟩
    rfl
  right_inv e := by
    ext x
    rfl

theorem card_signalingSystems (n : ℕ) :
    Fintype.card (SignalingSystems n) = n.factorial := by
  rw [Fintype.card_congr (signalingSystemsEquivPerm n), Fintype.card_perm, Fintype.card_fin]

theorem mismatch_eq_fixedPoints (s s' : Equiv.Perm (Fin n)) :
    successCount ⇑s ⇑s'.symm =
        (univ.filter fun x => Function.IsFixedPt ⇑(s'⁻¹ * s) x).card ∧
      successCount ⇑s ⇑s'.symm = n - (s'⁻¹ * s).support.card := by
  have h1 : successCount ⇑s ⇑s'.symm =
      (univ.filter fun x => Function.IsFixedPt ⇑(s'⁻¹ * s) x).card := by
    unfold successCount
    congr 1
  refine ⟨h1, ?_⟩
  rw [h1]
  have hc : (univ.filter fun x => Function.IsFixedPt ⇑(s'⁻¹ * s) x) = (s'⁻¹ * s).supportᶜ := by
    ext x
    rw [Finset.mem_filter, Finset.mem_compl, Equiv.Perm.mem_support, not_not]
    exact ⟨fun h => h.2, fun h => ⟨mem_univ x, h⟩⟩
  rw [hc, Finset.card_compl, Fintype.card_fin]

/-- For fixed `x`, the number of permutations sending `x` to `y` does not depend on `y`. -/
theorem card_perm_apply_eq_const (x y z : Fin n) :
    (univ.filter fun σ : Equiv.Perm (Fin n) => σ x = y).card =
      (univ.filter fun σ : Equiv.Perm (Fin n) => σ x = z).card := by
  refine Finset.card_bij' (fun σ _ => Equiv.swap y z * σ) (fun σ _ => Equiv.swap y z * σ)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    simp [Equiv.Perm.mul_apply, hσ]
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    simp [Equiv.Perm.mul_apply, hσ]
  · intro σ _
    exact Equiv.swap_mul_self_mul y z σ
  · intro σ _
    exact Equiv.swap_mul_self_mul y z σ

theorem card_perm_apply_eq (x y : Fin n) :
    n * (univ.filter fun σ : Equiv.Perm (Fin n) => σ x = y).card = n.factorial ∧
      (univ.filter fun σ : Equiv.Perm (Fin n) => σ x = y).card = (n - 1).factorial := by
  have hsum : (univ : Finset (Equiv.Perm (Fin n))).card =
      ∑ z : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ x = z).card :=
    Finset.card_eq_sum_card_fiberwise (fun σ _ => mem_univ (σ x))
  have hconst : ∀ z : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ x = z).card =
      (univ.filter fun σ : Equiv.Perm (Fin n) => σ x = y).card :=
    fun z => card_perm_apply_eq_const x z y
  simp only [hconst, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
    Fintype.card_perm] at hsum
  refine ⟨hsum.symm, ?_⟩
  have hn : 0 < n := Fin.pos x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.factorial_succ] at hsum
  simp only [Nat.add_sub_cancel]
  exact (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) hsum).symm

theorem sum_mismatch (hn : 1 ≤ n) (s : Equiv.Perm (Fin n)) :
    ∑ s' : Equiv.Perm (Fin n), successCount ⇑s ⇑s'.symm = n.factorial := by
  unfold successCount
  have hswap : ∑ s' : Equiv.Perm (Fin n), (univ.filter fun x => s'.symm (s x) = x).card =
      ∑ x : Fin n, (univ.filter fun s' : Equiv.Perm (Fin n) => s' x = s x).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun s' _ => ?_
    have : s'.symm (s x) = x ↔ s' x = s x := by
      rw [Equiv.symm_apply_eq, eq_comm]
    simp only [this]
  rw [hswap]
  have hterm : ∀ x : Fin n,
      (univ.filter fun s' : Equiv.Perm (Fin n) => s' x = s x).card = (n - 1).factorial :=
    fun x => (card_perm_apply_eq x (s x)).2
  simp only [hterm, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [Nat.factorial_succ]

theorem expected_mismatch (hn : 1 ≤ n) (s : Equiv.Perm (Fin n)) :
    (∑ s' : Equiv.Perm (Fin n), (successCount ⇑s ⇑s'.symm : ℚ)) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℚ) = 1 := by
  have h := sum_mismatch hn s
  rw [← Nat.cast_sum, h, Fintype.card_perm, Fintype.card_fin]
  have : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  exact div_self this

theorem expected_success_fraction (hn : 1 ≤ n) (s : Equiv.Perm (Fin n)) :
    (∑ s' : Equiv.Perm (Fin n), ((successCount ⇑s ⇑s'.symm : ℚ) / n)) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℚ) = 1 / n := by
  rw [← Finset.sum_div, div_right_comm, expected_mismatch hn s]

end LewisSignalingGaugeA
