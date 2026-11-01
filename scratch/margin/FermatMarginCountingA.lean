import Mathlib

/-!
# Counting bound on short proofs

MODEL.
* Proofs are bit strings: `List Bool`.
* A proof system over a statement type `S` is any function `check : List Bool → S`;
  the proof `p` proves exactly the statement `check p`. No other structure (soundness,
  decidability, computability) is assumed, so the bounds hold for every such system.
* A statement `s` has a proof shorter than `m` bits iff `∃ p, p.length < m ∧ check p = s`.
  The finset of such statements is `shortProvable check m`, the image under `check` of the
  finite type `Short m = Σ j : Fin m, (Fin j → Bool)` of bit strings of length `< m`
  (embedded into `List Bool` by `List.ofFn`).
* For part (2)/(3) the statements are the `n`-bit strings, `S = Fin n → Bool`.

PROVED.
* `card_short`: `Fintype.card (Short m) = 2 ^ m - 1`.
* `mem_shortProvable`: `s ∈ shortProvable check m ↔ ∃ p : List Bool, p.length < m ∧ check p = s`.
* `card_shortProvable_le` (1): `(shortProvable check m).card ≤ 2 ^ m - 1`.
* `card_shortProvable_lt` (2): for `S = Fin n → Bool`, `(shortProvable check m).card < 2 ^ m`,
  out of `Fintype.card (Fin n → Bool) = 2 ^ n` statements (`card_statements`).
* `fraction_shortProvable_lt` (2): the fraction `card / 2 ^ n` is `< 2 ^ ((m : ℤ) - n)` in `ℚ`.
* `card_mul_pow_lt` and `fraction_shortProvable_lt_of_le` (2): if `m + k ≤ n` then
  `card * 2 ^ k < 2 ^ n`, i.e. the fraction is `< 2 ^ (-(k : ℤ))`.
* `exists_no_short_proof` (3): for every `n` (in particular every `n ≥ 1`, see
  `exists_no_short_proof_of_one_le`) and every `check : List Bool → (Fin n → Bool)` there is
  `s : Fin n → Bool` such that every proof `p` with `check p = s` has `n ≤ p.length`.
* `not_uniform_unprovable`: the quantifier order in (3) cannot be swapped: for `n ≥ 1` there is
  no single `n`-bit statement lacking a proof shorter than `n` bits in every proof system
  (the constant system proves it with the empty proof).

INTERPRETED.
* "Number of statements that have a proof of length less than m" is the cardinality of the
  finset `shortProvable check m`, characterised by `mem_shortProvable`.
* "At most a 2^(m−n) fraction" is read as the rational number `card / 2 ^ n` compared with the
  integer power `(2 : ℚ) ^ ((m : ℤ) - n)`; the bound proved is strict.
* "m ≤ n − k" is stated as `m + k ≤ n` (natural-number subtraction avoided).
* "Under any proof system of this kind" is read as: for every `check` there exists such a
  statement (the statement may depend on `check`); `not_uniform_unprovable` shows the
  other reading is false.
-/

namespace FermatMarginCountingA

/-- Bit strings of length strictly less than `m`. -/
abbrev Short (m : ℕ) := Σ j : Fin m, (Fin j → Bool)

/-- The bit string underlying an element of `Short m`. -/
def Short.toList {m : ℕ} (p : Short m) : List Bool := List.ofFn p.2

/-- Statements having a proof shorter than `m` bits in the proof system `check`. -/
def shortProvable {S : Type*} [DecidableEq S] (check : List Bool → S) (m : ℕ) : Finset S :=
  Finset.univ.image (fun p : Short m => check p.toList)

theorem card_short (m : ℕ) : Fintype.card (Short m) = 2 ^ m - 1 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun j => 2 ^ j) m]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have := Nat.one_le_two_pow (n := m)
    omega

theorem mem_shortProvable {S : Type*} [DecidableEq S] (check : List Bool → S) (m : ℕ) (s : S) :
    s ∈ shortProvable check m ↔ ∃ p : List Bool, p.length < m ∧ check p = s := by
  unfold shortProvable
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, -, rfl⟩
    exact ⟨p.toList, by simp [Short.toList], rfl⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨⟨p.length, hp⟩, fun i => p.get i⟩, Finset.mem_univ _, ?_⟩
    simp [Short.toList]

/-- (1) At most `2 ^ m - 1` statements have a proof shorter than `m` bits. -/
theorem card_shortProvable_le {S : Type*} [DecidableEq S] (check : List Bool → S) (m : ℕ) :
    (shortProvable check m).card ≤ 2 ^ m - 1 := by
  unfold shortProvable
  calc (Finset.univ.image (fun p : Short m => check p.toList)).card
      ≤ (Finset.univ : Finset (Short m)).card := Finset.card_image_le
    _ = 2 ^ m - 1 := by rw [Finset.card_univ, card_short]

theorem card_statements (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

/-- (2) Fewer than `2 ^ m` of the `2 ^ n` statements have a proof shorter than `m` bits. -/
theorem card_shortProvable_lt {n : ℕ} (check : List Bool → (Fin n → Bool)) (m : ℕ) :
    (shortProvable check m).card < 2 ^ m := by
  have h1 := card_shortProvable_le check m
  have h2 := Nat.one_le_two_pow (n := m)
  omega

/-- (2) The fraction of `n`-bit statements with a proof shorter than `m` bits is
below `2 ^ (m - n)`. -/
theorem fraction_shortProvable_lt {n : ℕ} (check : List Bool → (Fin n → Bool)) (m : ℕ) :
    ((shortProvable check m).card : ℚ) / (Fintype.card (Fin n → Bool) : ℚ)
      < (2 : ℚ) ^ ((m : ℤ) - (n : ℤ)) := by
  rw [card_statements, zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
  push_cast
  apply div_lt_div_of_pos_right _ (by positivity)
  exact_mod_cast card_shortProvable_lt check m

/-- (2) If `m + k ≤ n`, then `card * 2 ^ k < 2 ^ n`. -/
theorem card_mul_pow_lt {n : ℕ} (check : List Bool → (Fin n → Bool)) (m k : ℕ)
    (hmk : m + k ≤ n) :
    (shortProvable check m).card * 2 ^ k < 2 ^ n := by
  calc (shortProvable check m).card * 2 ^ k < 2 ^ m * 2 ^ k :=
        Nat.mul_lt_mul_of_pos_right (card_shortProvable_lt check m) (by positivity)
    _ = 2 ^ (m + k) := (pow_add 2 m k).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hmk

/-- (2) If `m + k ≤ n`, fewer than a `2 ^ (-k)` fraction of the `n`-bit statements have a
proof shorter than `m` bits. -/
theorem fraction_shortProvable_lt_of_le {n : ℕ} (check : List Bool → (Fin n → Bool))
    (m k : ℕ) (hmk : m + k ≤ n) :
    ((shortProvable check m).card : ℚ) / (Fintype.card (Fin n → Bool) : ℚ)
      < (2 : ℚ) ^ (-(k : ℤ)) := by
  have h : (((shortProvable check m).card * 2 ^ k : ℕ) : ℚ) < ((2 ^ n : ℕ) : ℚ) := by
    exact_mod_cast card_mul_pow_lt check m k hmk
  push_cast at h
  rw [card_statements, zpow_neg, zpow_natCast]
  push_cast
  rw [div_lt_iff₀ (by positivity), ← div_eq_inv_mul, lt_div_iff₀ (by positivity)]
  exact h

/-- (3) Every proof system on `n`-bit statements leaves some statement without a proof
shorter than `n` bits. -/
theorem exists_no_short_proof (n : ℕ) (check : List Bool → (Fin n → Bool)) :
    ∃ s : Fin n → Bool, ∀ p : List Bool, check p = s → n ≤ p.length := by
  have hlt : (shortProvable check n).card < (Finset.univ : Finset (Fin n → Bool)).card := by
    rw [Finset.card_univ, card_statements]
    exact card_shortProvable_lt check n
  obtain ⟨s, -, hs⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨s, fun p hp => ?_⟩
  by_contra hlen
  exact hs ((mem_shortProvable check n s).2 ⟨p, by omega, hp⟩)

/-- (3), as stated for `n ≥ 1`. -/
theorem exists_no_short_proof_of_one_le (n : ℕ) (_hn : 1 ≤ n)
    (check : List Bool → (Fin n → Bool)) :
    ∃ s : Fin n → Bool, ∀ p : List Bool, check p = s → n ≤ p.length :=
  exists_no_short_proof n check

/-- The statement in (3) must depend on the proof system: for `n ≥ 1` no single statement
lacks a proof shorter than `n` bits in every proof system. -/
theorem not_uniform_unprovable (n : ℕ) (hn : 1 ≤ n) :
    ¬ ∃ s : Fin n → Bool, ∀ check : List Bool → (Fin n → Bool),
        ∀ p : List Bool, check p = s → n ≤ p.length := by
  rintro ⟨s, hs⟩
  have := hs (fun _ => s) [] rfl
  simp at this
  omega

end FermatMarginCountingA
