import Mathlib

/-!
# Erdős problem 203

* CONJECTURE (open, no proof claimed): `Erdos203Conjecture`.
* Unconditional: `erdos_203_k_zero`, `erdos_203_of_periodic_cover`, `erdos_203_not_78557`.
* CONDITIONAL on the existence of a finite periodic covering certificate:
  `erdos_203_of_exists_cover`, which concludes `Erdos203Conjecture`.
-/

namespace Erdos203

/-- CONJECTURE (Erdős problem 203, open): there is `m` coprime to 6 such that
`2^k * 3^l * m + 1` is never prime. -/
def Erdos203Conjecture : Prop := ∃ m, m.Coprime 6 ∧ ∀ k l, ¬ (2^k * 3^l * m + 1).Prime

/-- Partial result: for `m > 1` coprime to 6 (so `m` odd) and `k = 0`, the number
`3^l * m + 1` is even and greater than 2, hence not prime. -/
theorem erdos_203_k_zero (m : ℕ) (hm : m.Coprime 6) (hm1 : 1 < m) (l : ℕ) :
    ¬ (2^0 * 3^l * m + 1).Prime := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hodd : Odd m := by
    have h2 : Nat.Coprime m 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hm
    exact h2.odd_of_right
  have h3 : Odd (3^l * m) := (Odd.pow (by decide : Odd 3)).mul hodd
  intro hp
  have heven : Even (2^0 * 3^l * m + 1) := by
    simpa using h3.add_one
  rcases hp.eq_one_or_self_of_dvd 2 (even_iff_two_dvd.1 heven) with h | h
  · omega
  · have : m ≤ 3^l * m := Nat.le_mul_of_pos_left m (by positivity)
    simp at h
    omega

/-- Partial result (periodic covering criterion): suppose `m` is coprime to 6 and for every
residue pair `(i, j)` with `i < N₁`, `j < N₂` there is a divisor `d i j` of `2^i * 3^j * m + 1`
with `1 < d i j ≤ m`, `2^N₁ ≡ 1` and `3^N₂ ≡ 1` modulo `d i j`. Then `m` answers Erdős
problem 203 affirmatively. This reduces the problem to exhibiting a finite certificate; it does
not supply one. -/
theorem erdos_203_of_periodic_cover (m N₁ N₂ : ℕ) (hm : m.Coprime 6)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (d : ℕ → ℕ → ℕ)
    (hd : ∀ i < N₁, ∀ j < N₂, 1 < d i j ∧ d i j ≤ m ∧ 2^N₁ ≡ 1 [MOD d i j] ∧
      3^N₂ ≡ 1 [MOD d i j] ∧ d i j ∣ 2^i * 3^j * m + 1) :
    m.Coprime 6 ∧ ∀ k l, ¬ (2^k * 3^l * m + 1).Prime := by
  refine ⟨hm, fun k l hp => ?_⟩
  obtain ⟨h1, hle, h2, h3, hdvd⟩ :=
    hd (k % N₁) (Nat.mod_lt _ hN₁) (l % N₂) (Nat.mod_lt _ hN₂)
  set q := d (k % N₁) (l % N₂) with hq
  have e2 : 2^k ≡ 2^(k % N₁) [MOD q] := by
    have hk : k = N₁ * (k / N₁) + k % N₁ := (Nat.div_add_mod k N₁).symm
    have : 2^k = (2^N₁)^(k / N₁) * 2^(k % N₁) := by
      rw [← pow_mul, ← pow_add, ← hk]
    rw [this]
    have := (h2.pow (k / N₁)).mul_right (2^(k % N₁))
    simpa using this
  have e3 : 3^l ≡ 3^(l % N₂) [MOD q] := by
    have hl : l = N₂ * (l / N₂) + l % N₂ := (Nat.div_add_mod l N₂).symm
    have : 3^l = (3^N₂)^(l / N₂) * 3^(l % N₂) := by
      rw [← pow_mul, ← pow_add, ← hl]
    rw [this]
    have := (h3.pow (l / N₂)).mul_right (3^(l % N₂))
    simpa using this
  have e : 2^k * 3^l * m + 1 ≡ 2^(k % N₁) * 3^(l % N₂) * m + 1 [MOD q] :=
    ((e2.mul e3).mul_right m).add_right 1
  have hqdvd : q ∣ 2^k * 3^l * m + 1 := (Nat.ModEq.dvd_iff e dvd_rfl).2 hdvd
  rcases hp.eq_one_or_self_of_dvd q hqdvd with h | h
  · omega
  · have : m ≤ 2^k * 3^l * m := Nat.le_mul_of_pos_left m (by positivity)
    omega

/-- CONDITIONAL: the existence of a periodic covering certificate (as in
`erdos_203_of_periodic_cover`) implies `Erdos203Conjecture`. -/
theorem erdos_203_of_exists_cover
    (h : ∃ m N₁ N₂ : ℕ, ∃ d : ℕ → ℕ → ℕ, m.Coprime 6 ∧ 0 < N₁ ∧ 0 < N₂ ∧
      ∀ i < N₁, ∀ j < N₂, 1 < d i j ∧ d i j ≤ m ∧ 2^N₁ ≡ 1 [MOD d i j] ∧
        3^N₂ ≡ 1 [MOD d i j] ∧ d i j ∣ 2^i * 3^j * m + 1) :
    Erdos203Conjecture := by
  obtain ⟨m, N₁, N₂, d, hm, hN₁, hN₂, hd⟩ := h
  exact ⟨m, erdos_203_of_periodic_cover m N₁ N₂ hm hN₁ hN₂ d hd⟩

/-- Partial result: the Sierpiński number `78557` is not a witness, since
`2 * 3^2 * 78557 + 1 = 1414027` is prime. -/
theorem erdos_203_not_78557 : (2^1 * 3^2 * 78557 + 1).Prime := by
  norm_num

end Erdos203
