/-
# Perfect secrecy of the one-time pad, and Shannon's key bound

PROVED
1. `key_unique`: over a finite abelian group G, for each plaintext p and ciphertext c exactly one key k
   satisfies p + k = c.
2. `ciphertext_uniform`: with a uniform key, P(C = c | P = p) = 1/|G| for every p and c.
3. `perfect_secrecy`: for any plaintext distribution μ, the joint law of (P, C) factors as
   P(P = p, C = c) = μ(p) · P(C = c), and P(C = c) = 1/|G|. The ciphertext is independent of the
   plaintext.
4. `shannon_key_bound`: any encryption scheme enc : M → K → C that decrypts correctly (for a fixed key,
   different messages give different ciphertexts) and is perfectly secret in the counting sense (every
   message has the same number of keys leading to each ciphertext) has |M| ≤ |K|.
5. `otp_correct`, `otp_secret`: the one-time pad satisfies both hypotheses of item 4.

Item 4 is the uniform-key (counting) form of perfect secrecy; it is weaker than Shannon's theorem,
which allows any key distribution.

CITED
- Shannon, "Communication Theory of Secrecy Systems" (1949): perfect secrecy needs at least as many keys
  as messages.
-/

import Mathlib

namespace PerfectSecrecy

open Finset

section OTP

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem key_unique (p c : G) : (univ.filter fun k => p + k = c).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨c - p, ?_⟩
  ext k
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h; rw [← h]; abel
  · intro h; rw [h]; abel

/-- P(C = c | P = p) with a uniform key. -/
noncomputable def condProb (p c : G) : ℚ := ((univ.filter fun k => p + k = c).card : ℚ) / Fintype.card G

theorem ciphertext_uniform (p c : G) : condProb p c = 1 / Fintype.card G := by
  unfold condProb
  rw [key_unique]
  norm_num

/-- P(C = c) for plaintext distribution μ. -/
noncomputable def cProb (μ : G → ℚ) (c : G) : ℚ := ∑ p, μ p * condProb p c

theorem perfect_secrecy (μ : G → ℚ) (hμ : ∑ p, μ p = 1) (p c : G) :
    cProb μ c = 1 / Fintype.card G ∧ μ p * condProb p c = μ p * cProb μ c := by
  have hc : cProb μ c = 1 / Fintype.card G := by
    unfold cProb
    simp_rw [ciphertext_uniform]
    rw [← Finset.sum_mul, hμ, one_mul]
  refine ⟨hc, ?_⟩
  rw [hc, ciphertext_uniform]

end OTP

section Shannon

theorem shannon_key_bound {M K C : Type*} [Fintype M] [Fintype K] [DecidableEq C] [Nonempty M]
    [Nonempty K] (enc : M → K → C)
    (correct : ∀ m m' k, enc m k = enc m' k → m = m')
    (secret : ∀ m m' c, (univ.filter fun k => enc m k = c).card =
      (univ.filter fun k => enc m' k = c).card) :
    Fintype.card M ≤ Fintype.card K := by
  classical
  obtain ⟨m₀⟩ := ‹Nonempty M›
  obtain ⟨k₀⟩ := ‹Nonempty K›
  set c := enc m₀ k₀
  have hex : ∀ m, ∃ k, enc m k = c := by
    intro m
    have hpos : 0 < (univ.filter fun k => enc m₀ k = c).card :=
      Finset.card_pos.mpr ⟨k₀, by simp [c]⟩
    rw [← secret m m₀ c] at hpos
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
    exact ⟨k, (mem_filter.mp hk).2⟩
  choose g hg using hex
  have hinj : Function.Injective g := by
    intro m m' h
    apply correct m m' (g m)
    rw [hg m]
    conv_rhs => rw [h, hg m']
  exact Fintype.card_le_of_injective g hinj

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem otp_correct (m m' k : G) (h : m + k = m' + k) : m = m' := add_right_cancel h

theorem otp_secret (m m' c : G) :
    (univ.filter fun k => m + k = c).card = (univ.filter fun k => m' + k = c).card := by
  rw [key_unique, key_unique]

theorem otp_meets_bound [Nonempty G] : Fintype.card G ≤ Fintype.card G :=
  shannon_key_bound (fun m k => m + k) otp_correct otp_secret

end Shannon

end PerfectSecrecy

#print axioms PerfectSecrecy.key_unique
#print axioms PerfectSecrecy.ciphertext_uniform
#print axioms PerfectSecrecy.perfect_secrecy
#print axioms PerfectSecrecy.shannon_key_bound
#print axioms PerfectSecrecy.otp_secret
#print axioms PerfectSecrecy.otp_meets_bound
