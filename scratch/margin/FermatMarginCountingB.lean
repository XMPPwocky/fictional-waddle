import Mathlib

/-!
# Counting bound for short proofs

Model. A proof is a bit string `p : List Bool`; its length is `p.length`.
A proof system over a statement type `S` is an arbitrary function
`check : List Bool → S`: every proof proves exactly one statement, namely `check p`.
No soundness, computability or other structure is assumed. A statement `s` has a
proof shorter than `m` bits iff `∃ p, p.length < m ∧ check p = s`.
The bit strings of length `< m` are enumerated by
`Short m := Σ j : Fin m, (Fin j → Bool)` via `List.ofFn`.

PROVED
* `card_short` : `Fintype.card (Short m) = 2 ^ m - 1`.
* `mem_provable` : `s ∈ provable check m ↔ ∃ p, p.length < m ∧ check p = s`.
* `card_provable_le` (1) : for any `S` and any `check`, the number of statements
  with a proof shorter than `m` bits is `≤ 2 ^ m - 1`.
* `card_provable_lt` (2) : with `S = Fin n → Bool` (n-bit strings, of which there are
  `2 ^ n`, `card_bitstrings`), fewer than `2 ^ m` statements have a proof shorter than
  `m` bits.
* `fraction_lt` (2) : that number divided by `2 ^ n` is `< 2 ^ ((m : ℤ) - n)` (in `ℝ`).
* `fraction_lt_of_le_sub` (2) : if `m ≤ n - k` (natural subtraction) then
  `count * 2 ^ k < 2 ^ n`, and `fraction_lt_zpow_neg`: the fraction is `< 2 ^ (-k)`.
* `exists_no_short_proof` (3) : for every `n` (in particular every `n ≥ 1`) and every
  `check`, some n-bit statement has no proof shorter than `n` bits.
* `not_exists_uniform` : for `n ≥ 1` the quantifiers in (3) cannot be swapped: no single
  n-bit statement lacks a short proof in every proof system.

INTERPRETED
* "proof system" = arbitrary function `List Bool → S`; "fraction" = count divided by
  `2 ^ n`, compared in `ℝ` with integer powers of `2`.
* (3) is proved for all `n`, which contains the `n ≥ 1` case.
-/

namespace FermatMarginCountingB

/-- Bit strings of length less than `m`. -/
abbrev Short (m : ℕ) := Σ j : Fin m, (Fin j → Bool)

/-- The bit string represented by an element of `Short m`. -/
def Short.toList {m : ℕ} (s : Short m) : List Bool := List.ofFn s.2

theorem Short.length_toList {m : ℕ} (s : Short m) : s.toList.length < m := by
  simp [Short.toList]

theorem Short.surj {m : ℕ} (p : List Bool) (hp : p.length < m) :
    ∃ s : Short m, s.toList = p :=
  ⟨⟨⟨p.length, hp⟩, p.get⟩, by simp [Short.toList, List.ofFn_get]⟩

theorem sum_pow_two (m : ℕ) : ∑ i ∈ Finset.range m, 2 ^ i = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega

theorem card_short (m : ℕ) : Fintype.card (Short m) = 2 ^ m - 1 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun j => 2 ^ j) m, sum_pow_two]

/-- Statements having a proof shorter than `m` bits under `check`. -/
def provable {S : Type*} [DecidableEq S] (check : List Bool → S) (m : ℕ) : Finset S :=
  Finset.univ.image (fun s : Short m => check s.toList)

theorem mem_provable {S : Type*} [DecidableEq S] (check : List Bool → S) (m : ℕ) (s : S) :
    s ∈ provable check m ↔ ∃ p : List Bool, p.length < m ∧ check p = s := by
  constructor
  · intro h
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp h
    exact ⟨t.toList, t.length_toList, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨t, rfl⟩ := Short.surj p hp
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩

/-- (1) At most `2 ^ m - 1` statements have a proof shorter than `m` bits. -/
theorem card_provable_le {S : Type*} [DecidableEq S] (check : List Bool → S) (m : ℕ) :
    (provable check m).card ≤ 2 ^ m - 1 := by
  calc (provable check m).card ≤ (Finset.univ : Finset (Short m)).card :=
        Finset.card_image_le
    _ = 2 ^ m - 1 := by rw [Finset.card_univ, card_short]

theorem card_bitstrings (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

/-- (2) Of the `2 ^ n` n-bit statements, fewer than `2 ^ m` have a proof shorter
than `m` bits. -/
theorem card_provable_lt {n : ℕ} (check : List Bool → (Fin n → Bool)) (m : ℕ) :
    (provable check m).card < 2 ^ m := by
  have h := card_provable_le check m
  have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

/-- (2) The fraction of n-bit statements with a proof shorter than `m` bits is
less than `2 ^ (m - n)`. -/
theorem fraction_lt {n : ℕ} (check : List Bool → (Fin n → Bool)) (m : ℕ) :
    ((provable check m).card : ℝ) / (Fintype.card (Fin n → Bool) : ℝ)
      < (2 : ℝ) ^ ((m : ℤ) - n) := by
  rw [card_bitstrings, zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
  push_cast
  apply div_lt_div_of_pos_right _ (by positivity)
  exact_mod_cast card_provable_lt check m

/-- (2) If `m ≤ n - k`, fewer than a `2 ^ (-k)` fraction, in integer form. -/
theorem fraction_lt_of_le_sub {n : ℕ} (check : List Bool → (Fin n → Bool)) (m k : ℕ)
    (hm : m ≤ n - k) : (provable check m).card * 2 ^ k < 2 ^ n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have h := card_provable_le check 0
    simp only [pow_zero, Nat.sub_self, Nat.le_zero] at h
    rw [h, zero_mul]
    exact Nat.two_pow_pos n
  · have hmk : m + k ≤ n := by omega
    calc (provable check m).card * 2 ^ k < 2 ^ m * 2 ^ k :=
          Nat.mul_lt_mul_of_pos_right (card_provable_lt check m) (Nat.two_pow_pos k)
      _ = 2 ^ (m + k) := (pow_add 2 m k).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hmk

/-- (2) If `m ≤ n - k`, the fraction is less than `2 ^ (-k)`. -/
theorem fraction_lt_zpow_neg {n : ℕ} (check : List Bool → (Fin n → Bool)) (m k : ℕ)
    (hm : m ≤ n - k) :
    ((provable check m).card : ℝ) / (Fintype.card (Fin n → Bool) : ℝ)
      < (2 : ℝ) ^ (-(k : ℤ)) := by
  have h : (((provable check m).card * 2 ^ k : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast fraction_lt_of_le_sub check m k hm
  push_cast at h
  rw [card_bitstrings, zpow_neg, zpow_natCast]
  push_cast
  rw [div_lt_iff₀ (by positivity)]
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  calc ((provable check m).card : ℝ) = ((provable check m).card * 2 ^ k) * (2 ^ k)⁻¹ := by
        field_simp
    _ < 2 ^ n * (2 ^ k)⁻¹ := mul_lt_mul_of_pos_right h (inv_pos.mpr hk)
    _ = (2 ^ k)⁻¹ * 2 ^ n := mul_comm _ _

/-- (3) Every proof system leaves some n-bit statement without a proof shorter than
`n` bits. -/
theorem exists_no_short_proof (n : ℕ) (check : List Bool → (Fin n → Bool)) :
    ∃ s : Fin n → Bool, ∀ p : List Bool, check p = s → n ≤ p.length := by
  have hlt : (provable check n).card < (Finset.univ : Finset (Fin n → Bool)).card := by
    rw [Finset.card_univ, card_bitstrings]
    exact card_provable_lt check n
  obtain ⟨s, -, hs⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨s, fun p hp => ?_⟩
  by_contra hlen
  exact hs ((mem_provable check n s).mpr ⟨p, by omega, hp⟩)

/-- (3), restricted to `n ≥ 1` as in the target statement. -/
theorem exists_no_short_proof_of_pos (n : ℕ) (_hn : 1 ≤ n)
    (check : List Bool → (Fin n → Bool)) :
    ∃ s : Fin n → Bool, ∀ p : List Bool, check p = s → n ≤ p.length :=
  exists_no_short_proof n check

/-- For `n ≥ 1` the statement in (3) depends on the proof system: no n-bit statement
lacks a proof shorter than `n` bits under every proof system. -/
theorem not_exists_uniform (n : ℕ) (hn : 1 ≤ n) :
    ¬ ∃ s : Fin n → Bool, ∀ check : List Bool → (Fin n → Bool),
      ∀ p : List Bool, check p = s → n ≤ p.length := by
  rintro ⟨s, hs⟩
  have := hs (fun _ => s) [] rfl
  simp at this
  omega

end FermatMarginCountingB
