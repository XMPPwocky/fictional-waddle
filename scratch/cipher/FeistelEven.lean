/-
# Feistel rounds are even permutations

PROVED (in this file, from Mathlib):

Let `V` be a finite additive commutative group with `∀ x : V, x + x = 0`.

* `sign_addRight` : if `4 ∣ Fintype.card V`, then for every `c : V`,
  `Equiv.Perm.sign (Equiv.addRight c) = 1`.
* `sign_prodComm_eq` : for any finite type `α` with `N = Fintype.card α`,
  `Equiv.Perm.sign (Equiv.prodComm α α) = (-1) ^ ((N * N - N) / 2)`.
* `sign_swapHalves` : for any finite type `V` (no group structure used) with
  `4 ∣ Fintype.card V`, `Equiv.Perm.sign (Equiv.prodComm V V) = 1`.
* `feistel f` is the permutation of `V × V` sending `(L, R)` to `(R, L + f R)`, and
  `feistel_eq` : `feistel f = Equiv.prodComm V V * Equiv.prodCongrLeft (fun R => Equiv.addRight (f R))`.
* `sign_feistel` : if `4 ∣ Fintype.card V`, then `Equiv.Perm.sign (feistel f) = 1` for every
  `f : V → V`.
* `feistel_cipher_even` : if `4 ∣ Fintype.card V`, then for every list of round functions `fs`,
  `Equiv.Perm.sign (fs.map feistel).prod = 1`, and
  `feistel_cipher_mem_alternatingGroup` : `(fs.map feistel).prod ∈ alternatingGroup (V × V)`.
* `bitvec_hyps` : for `V = Fin m → ZMod 2` with `2 ≤ m`, both hypotheses hold (so they are not
  vacuous); `bitvec_feistel_cipher_even` : every Feistel cipher on `V × V` then lies in the
  alternating group.
* `sign_swapHalves_one_bit` : for `V = ZMod 2` (one bit per half, `4 ∤ card V`), the half swap has
  sign `-1`, so the divisibility hypothesis cannot be dropped from `sign_swapHalves`;
  `feistel_zero_one_bit_odd` : with one bit per half, the Feistel round with `f = 0` is odd.
* `zmod4_odd_round` : with halves in `ZMod 4` (so `4 ∣ card V` but `x + x = 0` fails), some
  Feistel round is odd. The XOR hypothesis `x + x = 0` cannot be dropped.

CITED / INTERPRETED (not proved here):

* Coppersmith and Grossman (1975), "Generators for certain alternating groups with applications
  to cryptography", SIAM J. Appl. Math. 29: the permutations realised by DES-like rounds on
  `n`-bit blocks generate the alternating group (for suitable block sizes). The evenness half of
  that statement, in the general form above, is what this file proves; the generation half is not.
* Even and Goldreich (1983), "DES-like functions can generate the alternating group",
  IEEE Trans. Inform. Theory 29: Feistel-type round functions generate exactly the alternating
  group on the block space. Again only the inclusion into the alternating group is proved here.
* Interpretation: a cipher that is a product of these Feistel rounds, with XOR-combined halves of
  at least 2 bits, can never realise an odd permutation of the block space, whatever the round
  functions or key schedule. Real DES also omits the swap in its last round and adds the initial
  and final permutations; those variants are not stated here.
-/
import Mathlib

namespace FeistelEven

open Equiv Equiv.Perm

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Translation by `c` in a group of exponent dividing 2, with `4 ∣ card V`, is even. -/
theorem sign_addRight (hV : ∀ x : V, x + x = 0) (h4 : 4 ∣ Fintype.card V) (c : V) :
    Perm.sign (Equiv.addRight c) = 1 := by
  by_cases hc : c = 0
  · subst hc
    have : (Equiv.addRight (0 : V) : Perm V) = 1 := by
      ext x; simp
    rw [this, Perm.sign_one]
  · have hsq : (Equiv.addRight c : Perm V) ^ 2 = 1 := by
      ext x; simp [sq, Perm.mul_apply, add_assoc, hV]
    rw [sign_of_pow_two_eq_one hsq]
    have hfix : Fintype.card (Function.fixedPoints ⇑(Equiv.addRight c : Perm V)) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      refine ⟨fun ⟨x, hx⟩ => hc ?_⟩
      have hx' : x + c = x := hx
      simpa using hx'
    rw [hfix, Nat.sub_zero]
    obtain ⟨k, hk⟩ := h4
    rw [hk]
    have : 4 * k / 2 = 2 * k := by omega
    rw [this]
    exact (even_two_mul k).neg_one_pow

/-- The half swap on `α × α` has sign `(-1) ^ ((N * N - N) / 2)` where `N = card α`. -/
theorem sign_prodComm_eq {α : Type*} [Fintype α] [DecidableEq α] :
    Perm.sign (Equiv.prodComm α α) =
      (-1) ^ ((Fintype.card α * Fintype.card α - Fintype.card α) / 2) := by
  have hsq : (Equiv.prodComm α α : Perm (α × α)) ^ 2 = 1 := by
    ext ⟨a, b⟩ <;> simp [sq, Perm.mul_apply]
  rw [sign_of_pow_two_eq_one hsq]
  have e : α ≃ Function.fixedPoints ⇑(Equiv.prodComm α α : Perm (α × α)) :=
    { toFun := fun x => ⟨(x, x), rfl⟩
      invFun := fun p => p.1.1
      left_inv := fun x => rfl
      right_inv := by
        rintro ⟨⟨a, b⟩, h⟩
        have h' : (b, a) = (a, b) := h
        have hab : b = a := (Prod.mk.inj h').1
        subst hab
        rfl }
  have hfix : Fintype.card (Function.fixedPoints ⇑(Equiv.prodComm α α : Perm (α × α))) =
      Fintype.card α := (Fintype.card_congr e).symm
  rw [hfix, Fintype.card_prod]

omit [AddCommGroup V] in
/-- The half swap on `V × V` is even when `4 ∣ card V`. -/
theorem sign_swapHalves (h4 : 4 ∣ Fintype.card V) :
    Perm.sign (Equiv.prodComm V V) = 1 := by
  rw [sign_prodComm_eq]
  obtain ⟨k, hk⟩ := h4
  set N := Fintype.card V with hN
  have h : N * N - N = 2 * (2 * k * (N - 1)) := by
    rw [← Nat.mul_sub_one]
    nth_rewrite 1 [hk]
    ring
  rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have : 2 * k * (N - 1) = 2 * (k * (N - 1)) := by ring
  rw [this]
  exact (even_two_mul _).neg_one_pow

omit [Fintype V] [DecidableEq V] in
/-- One Feistel round on `V × V`: `(L, R) ↦ (R, L + f R)`. -/
def feistel (f : V → V) : Perm (V × V) where
  toFun p := (p.2, p.1 + f p.2)
  invFun q := (q.2 - f q.1, q.1)
  left_inv p := by simp
  right_inv q := by simp

omit [Fintype V] [DecidableEq V] in
@[simp] theorem feistel_apply (f : V → V) (L R : V) : feistel f (L, R) = (R, L + f R) := rfl

omit [Fintype V] [DecidableEq V] in
/-- A Feistel round is the half swap after the fiberwise translation `(L, R) ↦ (L + f R, R)`. -/
theorem feistel_eq (f : V → V) :
    feistel f =
      (Equiv.prodComm V V : Perm (V × V)) *
        Equiv.prodCongrLeft (fun R : V => Equiv.addRight (f R)) := by
  ext ⟨L, R⟩ <;> simp [Perm.mul_apply]

/-- Every Feistel round is an even permutation of `V × V` when `4 ∣ card V`. -/
theorem sign_feistel (hV : ∀ x : V, x + x = 0) (h4 : 4 ∣ Fintype.card V) (f : V → V) :
    Perm.sign (feistel f) = 1 := by
  rw [feistel_eq, Perm.sign_mul, sign_swapHalves h4, sign_prodCongrLeft, one_mul]
  exact Finset.prod_eq_one fun R _ => sign_addRight hV h4 (f R)

/-- Every composite of Feistel rounds is an even permutation of `V × V` when `4 ∣ card V`. -/
theorem feistel_cipher_even (hV : ∀ x : V, x + x = 0) (h4 : 4 ∣ Fintype.card V)
    (fs : List (V → V)) : Perm.sign (fs.map feistel).prod = 1 := by
  induction fs with
  | nil => simp
  | cons f fs ih => rw [List.map_cons, List.prod_cons, Perm.sign_mul, sign_feistel hV h4, ih, one_mul]

/-- Every composite of Feistel rounds lies in the alternating group of `V × V`. -/
theorem feistel_cipher_mem_alternatingGroup (hV : ∀ x : V, x + x = 0)
    (h4 : 4 ∣ Fintype.card V) (fs : List (V → V)) :
    (fs.map feistel).prod ∈ alternatingGroup (V × V) :=
  mem_alternatingGroup.mpr (feistel_cipher_even hV h4 fs)

/-- Bit vectors of length `m ≥ 2` satisfy both hypotheses. -/
theorem bitvec_hyps (m : ℕ) (hm : 2 ≤ m) :
    (∀ x : Fin m → ZMod 2, x + x = 0) ∧ 4 ∣ Fintype.card (Fin m → ZMod 2) := by
  refine ⟨fun x => ?_, ?_⟩
  · funext i
    exact CharTwo.add_self_eq_zero (x i)
  · rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this]
    exact pow_dvd_pow 2 hm

/-- Feistel ciphers on pairs of `m`-bit halves, `m ≥ 2`, are even permutations. -/
theorem bitvec_feistel_cipher_even (m : ℕ) (hm : 2 ≤ m)
    (fs : List ((Fin m → ZMod 2) → (Fin m → ZMod 2))) :
    Perm.sign (fs.map feistel).prod = 1 ∧
      (fs.map feistel).prod ∈ alternatingGroup ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
  ⟨feistel_cipher_even (bitvec_hyps m hm).1 (bitvec_hyps m hm).2 fs,
    feistel_cipher_mem_alternatingGroup (bitvec_hyps m hm).1 (bitvec_hyps m hm).2 fs⟩

/-- With one bit per half the half swap is odd, so `4 ∣ card V` is needed in `sign_swapHalves`. -/
theorem sign_swapHalves_one_bit :
    Perm.sign (Equiv.prodComm (ZMod 2) (ZMod 2)) = -1 := by
  rw [sign_prodComm_eq, ZMod.card]
  norm_num

/-- With one bit per half, the Feistel round with `f = 0` is the half swap, which is odd. -/
theorem feistel_zero_one_bit_odd :
    Perm.sign (feistel (fun _ : ZMod 2 => (0 : ZMod 2))) = -1 := by
  have : feistel (fun _ : ZMod 2 => (0 : ZMod 2)) = Equiv.prodComm (ZMod 2) (ZMod 2) := by
    ext ⟨L, R⟩ <;> simp
  rw [this]
  exact sign_swapHalves_one_bit

/-- Halves combined by addition mod 4 instead of XOR: some round is odd. -/
theorem zmod4_odd_round :
    Perm.sign (feistel (fun R : ZMod 4 => if R = 0 then (1 : ZMod 4) else 0)) = -1 := by
  decide

end FeistelEven

#print axioms FeistelEven.sign_addRight
#print axioms FeistelEven.sign_prodComm_eq
#print axioms FeistelEven.sign_swapHalves
#print axioms FeistelEven.feistel_eq
#print axioms FeistelEven.sign_feistel
#print axioms FeistelEven.feistel_cipher_even
#print axioms FeistelEven.feistel_cipher_mem_alternatingGroup
#print axioms FeistelEven.bitvec_hyps
#print axioms FeistelEven.bitvec_feistel_cipher_even
#print axioms FeistelEven.sign_swapHalves_one_bit
#print axioms FeistelEven.feistel_zero_one_bit_odd
#print axioms FeistelEven.zmod4_odd_round
