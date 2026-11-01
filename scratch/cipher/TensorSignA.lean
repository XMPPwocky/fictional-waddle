import Mathlib

/-!
# Signs of copies of a permutation and of parallel S-box layers

## PROVED

All signs are `Equiv.Perm.sign : Perm X →* ℤˣ`; `σ × τ` below is `Equiv.prodCongr σ τ`
and the S-box layer of `S : Fin c → Perm α` is `Equiv.piCongrRight S : Perm (Fin c → α)`,
i.e. `x ↦ fun i => S i (x i)`. Throughout `α`, `β` are finite types with decidable equality.

* `sign_prodCongr`: `sign (σ × τ) = sign σ ^ card β * sign τ ^ card α`.
* `sign_copies` (target 1): `sign (σ × id_β) = sign σ ^ card β`.
* `copies_even_of_even_card`: if `card β` is even then `sign (σ × id_β) = 1`.
* `copies_odd_of_odd_card`: if `card β` is odd then `sign (σ × id_β) = sign σ`.
* `copies_all_even_iff`: `(∀ σ, sign (σ × id_β) = 1) ↔ card α ≤ 1 ∨ Even (card β)`.
* `copies_three_odd`: with `α = Fin 2`, `β = Fin 3`, `σ = swap 0 1` (sign `-1`),
  `sign (σ × id_β) = -1`. So `card β ≥ 2` does not force evenness.
* `sign_layer` (target 2): for every `c : ℕ`,
  `sign (piCongrRight S) = ∏ i, sign (S i) ^ (card α ^ (c - 1))`
  (for `c = 0` both sides are `1`).
* `layer_even_of_even_card`: if `card α` is even and `2 ≤ c`, `sign (piCongrRight S) = 1`
  for every `S`.
* `layer_odd_card`: if `card α` is odd, `sign (piCongrRight S) = ∏ i, sign (S i)`.
* `layer_one`: for `c = 1`, `sign (piCongrRight S) = sign (S 0)`.
* `layer_one_odd`: `α = Fin 2`, `c = 1`, `S 0 = swap 0 1` gives a layer of sign `-1`.
* `layer_all_even_iff`:
  `(∀ S : Fin c → Perm α, sign (piCongrRight S) = 1) ↔
    c = 0 ∨ card α ≤ 1 ∨ (Even (card α) ∧ 2 ≤ c)`.
* `bits_layer_even` (target 3): for `α = Fin k → ZMod 2` with `1 ≤ k` and `2 ≤ c`,
  `sign (piCongrRight S) = 1` for every `S : Fin c → Perm (Fin k → ZMod 2)`.
* Hypothesis instances: `copies_even_instance` (`β = Fin 2`), `layer_even_instance`
  (`α = Fin 2`, `c = 2`, odd S-boxes), `bits_layer_instance` (`k = 1`, `c = 2`, odd S-boxes,
  each S-box individually of sign `-1`).

## CITED / INTERPRETED (not proved here)

* Reading: a block cipher round built from a parallel layer of `c ≥ 2` S-boxes on `n`-bit
  chunks (`n ≥ 1`) permutes `{0,1}^(c n)` by an even permutation, whatever the S-boxes are.
  If the other round components are also even (for example XOR with a constant on a state
  of at least 2 bits, a fixed-point-free involution or the identity), the rounds generate a
  subgroup of the alternating group. Parity constraints of this kind for iterated ciphers
  appear in the literature (e.g. Coppersmith and Grossman 1975; Even and Goldreich 1983);
  those results, and the evenness of the other components, are not formalised here.
* The word "copies" is read as: `β` indexes identical copies of the point set `α`, and the
  permutation acts the same way in each copy.
-/

open Equiv Equiv.Perm

namespace TensorSignA

/-- An even power of a unit of `ℤ` is `1`. -/
theorem units_pow_even {u : ℤˣ} {n : ℕ} (h : Even n) : u ^ n = 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [← two_mul, pow_mul, Int.units_sq, one_pow]

/-- An odd power of a unit of `ℤ` is the unit itself. -/
theorem units_pow_odd {u : ℤˣ} {n : ℕ} (h : Odd n) : u ^ n = u := by
  obtain ⟨k, rfl⟩ := h
  rw [pow_succ, pow_mul, Int.units_sq, one_pow, one_mul]

/-- `(-1 : ℤˣ) ^ n = 1` exactly when `n` is even. -/
theorem neg_one_units_pow_eq_one_iff (n : ℕ) : (-1 : ℤˣ) ^ n = 1 ↔ Even n := by
  constructor
  · intro h
    by_contra hn
    rw [Nat.not_even_iff_odd] at hn
    rw [units_pow_odd hn] at h
    exact absurd h (by decide)
  · exact units_pow_even

section Copies

variable {α β : Type*} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

/-- Sign of a product permutation. -/
theorem sign_prodCongr (σ : Perm α) (τ : Perm β) :
    sign (Equiv.prodCongr σ τ) = sign σ ^ Fintype.card β * sign τ ^ Fintype.card α := by
  have h : (Equiv.prodCongr σ τ : Perm (α × β)) =
      (Equiv.prodCongr σ (Equiv.refl β) : Perm (α × β)) *
        (Equiv.prodCongr (Equiv.refl α) τ : Perm (α × β)) := by
    ext ⟨a, b⟩ <;> rfl
  rw [h, Perm.sign_mul, prodCongr_refl_right, prodCongr_refl_left, sign_prodCongrLeft,
    sign_prodCongrRight, Finset.prod_const, Finset.prod_const, Finset.card_univ,
    Finset.card_univ]

/-- Target 1: `card β` copies of `σ` have sign `sign σ ^ card β`. -/
theorem sign_copies (σ : Perm α) :
    sign (Equiv.prodCongr σ (Equiv.refl β)) = sign σ ^ Fintype.card β := by
  rw [prodCongr_refl_right, sign_prodCongrLeft, Finset.prod_const, Finset.card_univ]

theorem copies_even_of_even_card (σ : Perm α) (h : Even (Fintype.card β)) :
    sign (Equiv.prodCongr σ (Equiv.refl β)) = 1 := by
  rw [sign_copies, units_pow_even h]

theorem copies_odd_of_odd_card (σ : Perm α) (h : Odd (Fintype.card β)) :
    sign (Equiv.prodCongr σ (Equiv.refl β)) = sign σ := by
  rw [sign_copies, units_pow_odd h]

/-- Copies of every permutation of `α` are even iff `α` has at most one point or the
number of copies is even. -/
theorem copies_all_even_iff :
    (∀ σ : Perm α, sign (Equiv.prodCongr σ (Equiv.refl β)) = 1) ↔
      Fintype.card α ≤ 1 ∨ Even (Fintype.card β) := by
  constructor
  · intro h
    by_cases hα : Fintype.card α ≤ 1
    · exact Or.inl hα
    · right
      obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card α by omega)
      have := h (swap a b)
      rw [sign_copies, sign_swap hab] at this
      exact (neg_one_units_pow_eq_one_iff _).1 this
  · rintro (hα | hβ) σ
    · have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.1 hα
      have : σ = 1 := Subsingleton.elim _ _
      rw [sign_copies, this, map_one, one_pow]
    · exact copies_even_of_even_card σ hβ

end Copies

/-- Three copies of an odd permutation of two points stay odd. -/
theorem copies_three_odd :
    sign (Equiv.prodCongr (swap (0 : Fin 2) 1) (Equiv.refl (Fin 3))) = -1 := by
  rw [sign_copies, sign_swap (by decide), Fintype.card_fin]
  decide

/-- Instance of the hypothesis of `copies_even_of_even_card`: two copies of an odd
permutation. -/
theorem copies_even_instance :
    Even (Fintype.card (Fin 2)) ∧ sign (swap (0 : Fin 2) 1) = -1 ∧
      sign (Equiv.prodCongr (swap (0 : Fin 2) 1) (Equiv.refl (Fin 2))) = 1 :=
  ⟨by decide, sign_swap (by decide), copies_even_of_even_card _ (by decide)⟩

section Layer

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] [Fintype α] in
/-- Splitting off the first chunk turns the layer into a product permutation. -/
theorem layer_conj {n : ℕ} (S : Fin (n + 1) → Perm α) :
    ((Fin.consEquiv (fun _ : Fin (n + 1) => α)).symm.permCongr (Equiv.piCongrRight S) :
        Perm (α × (Fin n → α))) =
      Equiv.prodCongr (S 0) (Equiv.piCongrRight fun i : Fin n => S i.succ) := by
  ext ⟨a, v⟩
  · simp [Equiv.permCongr_apply, Fin.consEquiv]
  · simp [Equiv.permCongr_apply, Fin.consEquiv, Fin.tail]

/-- Target 2: sign of a parallel S-box layer with `c` chunks. -/
theorem sign_layer (c : ℕ) (S : Fin c → Perm α) :
    sign (Equiv.piCongrRight S : Perm (Fin c → α)) =
      ∏ i, sign (S i) ^ (Fintype.card α ^ (c - 1)) := by
  induction c with
  | zero =>
    have : (Equiv.piCongrRight S : Perm (Fin 0 → α)) = 1 := Subsingleton.elim _ _
    simp [this]
  | succ n ih =>
    rw [← sign_permCongr (Fin.consEquiv (fun _ : Fin (n + 1) => α)).symm, layer_conj,
      sign_prodCongr, ih, Fin.prod_univ_succ, Fintype.card_fun, Fintype.card_fin,
      Nat.add_sub_cancel]
    congr 1
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases n with _ | m
    · exact Fin.elim0 i
    · rw [← pow_mul, Nat.add_sub_cancel, ← pow_succ]

theorem layer_even_of_even_card {c : ℕ} (hα : Even (Fintype.card α)) (hc : 2 ≤ c)
    (S : Fin c → Perm α) :
    sign (Equiv.piCongrRight S : Perm (Fin c → α)) = 1 := by
  rw [sign_layer]
  have he : Even (Fintype.card α ^ (c - 1)) := (Nat.even_pow' (by omega)).2 hα
  exact Finset.prod_eq_one fun i _ => units_pow_even he

theorem layer_odd_card {c : ℕ} (hα : Odd (Fintype.card α)) (S : Fin c → Perm α) :
    sign (Equiv.piCongrRight S : Perm (Fin c → α)) = ∏ i, sign (S i) := by
  rw [sign_layer]
  exact Finset.prod_congr rfl fun i _ => units_pow_odd (hα.pow)

theorem layer_one (S : Fin 1 → Perm α) :
    sign (Equiv.piCongrRight S : Perm (Fin 1 → α)) = sign (S 0) := by
  rw [sign_layer]
  simp

/-- The layer is even for every choice of S-boxes exactly when there are no chunks,
the alphabet has at most one symbol, or the alphabet size is even and there are at
least two chunks. -/
theorem layer_all_even_iff (c : ℕ) :
    (∀ S : Fin c → Perm α, sign (Equiv.piCongrRight S : Perm (Fin c → α)) = 1) ↔
      c = 0 ∨ Fintype.card α ≤ 1 ∨ (Even (Fintype.card α) ∧ 2 ≤ c) := by
  constructor
  · intro h
    rcases c with _ | n
    · exact Or.inl rfl
    right
    by_cases hα : Fintype.card α ≤ 1
    · exact Or.inl hα
    right
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card α by omega)
    have := h (Fin.cons (swap a b) fun _ => 1)
    rw [sign_layer, Fin.prod_univ_succ] at this
    simp only [Fin.cons_zero, Fin.cons_succ, map_one, one_pow, Finset.prod_const_one,
      mul_one, sign_swap hab, Nat.add_sub_cancel] at this
    have he := (neg_one_units_pow_eq_one_iff _).1 this
    rw [Nat.even_pow] at he
    exact ⟨he.1, by omega⟩
  · rintro (hc | hα | ⟨hα, hc⟩) S
    · subst hc
      have : (Equiv.piCongrRight S : Perm (Fin 0 → α)) = 1 := Subsingleton.elim _ _
      rw [this, map_one]
    · have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.1 hα
      rw [sign_layer]
      exact Finset.prod_eq_one fun i _ => by
        rw [show S i = 1 from Subsingleton.elim _ _, map_one, one_pow]
    · exact layer_even_of_even_card hα hc S

end Layer

/-- One chunk with an odd S-box gives an odd layer. -/
theorem layer_one_odd :
    sign (Equiv.piCongrRight (fun _ : Fin 1 => swap (0 : Fin 2) 1) :
      Perm (Fin 1 → Fin 2)) = -1 := by
  rw [layer_one, sign_swap (by decide)]

/-- Instance of the hypotheses of `layer_even_of_even_card`: two chunks over a two-letter
alphabet, both S-boxes odd. -/
theorem layer_even_instance :
    Even (Fintype.card (Fin 2)) ∧ 2 ≤ 2 ∧ sign (swap (0 : Fin 2) 1) = -1 ∧
      sign (Equiv.piCongrRight (fun _ : Fin 2 => swap (0 : Fin 2) 1) :
        Perm (Fin 2 → Fin 2)) = 1 :=
  ⟨by decide, le_rfl, sign_swap (by decide), layer_even_of_even_card (by decide) le_rfl _⟩

theorem card_bits (k : ℕ) : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- Target 3: on `k ≥ 1` bit chunks, a layer of `c ≥ 2` arbitrary S-boxes is even. -/
theorem bits_layer_even {k c : ℕ} (hk : 1 ≤ k) (hc : 2 ≤ c)
    (S : Fin c → Perm (Fin k → ZMod 2)) :
    sign (Equiv.piCongrRight S : Perm (Fin c → Fin k → ZMod 2)) = 1 := by
  refine layer_even_of_even_card ?_ hc S
  rw [card_bits]
  exact (Nat.even_pow' (by omega)).2 even_two

/-- Instance of the hypotheses of `bits_layer_even`: `k = 1`, `c = 2`, each S-box the
odd swap of the two one-bit words. -/
theorem bits_layer_instance :
    1 ≤ 1 ∧ 2 ≤ 2 ∧ sign (swap (0 : Fin 1 → ZMod 2) 1) = -1 ∧
      sign (Equiv.piCongrRight (fun _ : Fin 2 => swap (0 : Fin 1 → ZMod 2) 1) :
        Perm (Fin 2 → Fin 1 → ZMod 2)) = 1 :=
  ⟨le_rfl, le_rfl, sign_swap (by decide), bits_layer_even le_rfl le_rfl _⟩

end TensorSignA

#print axioms TensorSignA.units_pow_even
#print axioms TensorSignA.units_pow_odd
#print axioms TensorSignA.neg_one_units_pow_eq_one_iff
#print axioms TensorSignA.sign_prodCongr
#print axioms TensorSignA.sign_copies
#print axioms TensorSignA.copies_even_of_even_card
#print axioms TensorSignA.copies_odd_of_odd_card
#print axioms TensorSignA.copies_all_even_iff
#print axioms TensorSignA.copies_three_odd
#print axioms TensorSignA.copies_even_instance
#print axioms TensorSignA.layer_conj
#print axioms TensorSignA.sign_layer
#print axioms TensorSignA.layer_even_of_even_card
#print axioms TensorSignA.layer_odd_card
#print axioms TensorSignA.layer_one
#print axioms TensorSignA.layer_all_even_iff
#print axioms TensorSignA.layer_one_odd
#print axioms TensorSignA.layer_even_instance
#print axioms TensorSignA.card_bits
#print axioms TensorSignA.bits_layer_even
#print axioms TensorSignA.bits_layer_instance
