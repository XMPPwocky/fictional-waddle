import Mathlib

/-!
# Pólya urn with `k` colours and Bose–Einstein counting

Urn model. There are `k` colours (`Fin k`), one ball of each colour initially; each draw picks a ball
uniformly and returns it together with one more ball of the same colour. A draw sequence of length
`n` is a function `f : Fin n → Fin k` (`f i` = colour drawn at step `i`). After the history `g` of
length `n`, the urn holds `cnt g c + 1` balls of colour `c` and `n + k` balls in total, so

  `seqProb (n+1) (snoc g a) = seqProb n g * (cnt g a + 1) / (n + k)`,  `seqProb 0 _ = 1`.

`countProb n v` is the sum of `seqProb n f` over all draw sequences `f` whose colour counts equal `v`.

## PROVED

* `seqProb_eq`: for every `k`, `n` and every draw sequence `f : Fin n → Fin k`,
  `seqProb n f = (∏_c (cnt f c)!) / ∏_{j < n} (j + k)`.
* `seqProb_exchangeable`: two draw sequences with the same colour counts have the same probability.
* `sum_seqProb`: for `k > 0`, `∑_f seqProb n f = 1` (the model is a probability distribution on
  draw sequences of length `n`).
* `countProb_uniform`: for `k > 0` and every count vector `v : Fin k → ℕ` with `∑_c v c = n`,
  `countProb n v = 1 / (n + k - 1).choose (k - 1)`.
* `countProb_two`: for `k = 2` and `j ≤ n`, `countProb n ![j, n - j] = 1 / (n + 1)`.

## INTERPRETED (not formalized)

* `(n + k - 1).choose (k - 1)` is the number of count vectors `v : Fin k → ℕ` with `∑ v = n`
  (stars and bars); that count is not proved in this file, so "uniform over compositions" is
  read off from the formula rather than stated as a theorem about the set of compositions.
* Reading a count vector as an occupation of `k` single-particle states by `n` indistinguishable
  bosons, the uniform law over occupations is Bose–Einstein counting. No physics is formalized.
-/

namespace PolyaBoseEinstein

open Finset

variable {k : ℕ}

/-- Number of draws of colour `c` in the draw sequence `f`. -/
def cnt {n : ℕ} (f : Fin n → Fin k) (c : Fin k) : ℕ := (univ.filter fun i => f i = c).card

/-- The colour-count vector of a draw sequence. -/
def counts {n : ℕ} (f : Fin n → Fin k) : Fin k → ℕ := fun c => cnt f c

theorem cnt_snoc {n : ℕ} (f : Fin n → Fin k) (a c : Fin k) :
    cnt (Fin.snoc (α := fun _ => Fin k) f a) c = cnt f c + if a = c then 1 else 0 := by
  unfold cnt
  rw [card_filter, card_filter, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem cnt_zero (f : Fin 0 → Fin k) (c : Fin k) : cnt f c = 0 := by
  simp [cnt]

theorem sum_cnt {n : ℕ} (f : Fin n → Fin k) : ∑ c, cnt f c = n := by
  induction n with
  | zero => simp [cnt_zero]
  | succ n ih =>
    rw [← Fin.snoc_init_self (α := fun _ => Fin k) f]
    simp only [cnt_snoc, sum_add_distrib, ih, sum_ite_eq, mem_univ, ite_true]

/-- Probability of a draw sequence in the Pólya urn. -/
def seqProb : (n : ℕ) → (Fin n → Fin k) → ℚ
  | 0, _ => 1
  | n + 1, f => seqProb n (Fin.init f) * (((cnt (Fin.init f) (f (Fin.last n)) : ℚ) + 1) / (n + k))

theorem seqProb_snoc {n : ℕ} (g : Fin n → Fin k) (a : Fin k) :
    seqProb (n + 1) (Fin.snoc (α := fun _ => Fin k) g a) =
      seqProb n g * (((cnt g a : ℚ) + 1) / (n + k)) := by
  simp [seqProb, Fin.init_snoc, Fin.snoc_last]

/-- Product of the first `n` urn totals: `k (k+1) ⋯ (k+n-1)`. -/
def den (k n : ℕ) : ℚ := ∏ j ∈ range n, ((j : ℚ) + k)

theorem prod_factorial_snoc {n : ℕ} (g : Fin n → Fin k) (a : Fin k) :
    ∏ c, ((cnt (Fin.snoc (α := fun _ => Fin k) g a) c).factorial : ℚ) =
      (∏ c, ((cnt g c).factorial : ℚ)) * ((cnt g a : ℚ) + 1) := by
  have h : ∀ c, ((cnt (Fin.snoc (α := fun _ => Fin k) g a) c).factorial : ℚ) =
      ((cnt g c).factorial : ℚ) * (if a = c then ((cnt g c : ℚ) + 1) else 1) := by
    intro c
    rw [cnt_snoc]
    split_ifs with hac
    · rw [Nat.factorial_succ]; push_cast; ring
    · simp
  simp only [h, prod_mul_distrib, prod_ite_eq, mem_univ, ite_true]

/-- Exchangeability formula: the probability of a draw sequence depends only on its counts. -/
theorem seqProb_eq (n : ℕ) (f : Fin n → Fin k) :
    seqProb n f = (∏ c, ((cnt f c).factorial : ℚ)) / den k n := by
  induction n with
  | zero => simp [seqProb, den, cnt_zero]
  | succ n ih =>
    rw [← Fin.snoc_init_self (α := fun _ => Fin k) f, seqProb_snoc, prod_factorial_snoc, ih,
      div_mul_div_comm]
    simp only [den, prod_range_succ]

theorem seqProb_exchangeable {n : ℕ} (f f' : Fin n → Fin k) (h : counts f = counts f') :
    seqProb n f = seqProb n f' := by
  rw [seqProb_eq, seqProb_eq]
  congr 1
  exact prod_congr rfl fun c _ => by rw [show cnt f c = cnt f' c from congrFun h c]

theorem sum_snoc {n : ℕ} (F : (Fin (n + 1) → Fin k) → ℚ) :
    ∑ f, F f = ∑ a, ∑ g : Fin n → Fin k, F (Fin.snoc (α := fun _ => Fin k) g a) := by
  rw [← (Fin.snocEquiv (fun _ => Fin k)).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The urn defines a probability distribution on draw sequences of each length. -/
theorem sum_seqProb (hk : 0 < k) (n : ℕ) : ∑ f : Fin n → Fin k, seqProb n f = 1 := by
  induction n with
  | zero => simp [seqProb]
  | succ n ih =>
    rw [sum_snoc]
    simp only [seqProb_snoc]
    rw [sum_comm]
    have hnk : (n : ℚ) + k ≠ 0 := by positivity
    have : ∀ g : Fin n → Fin k,
        ∑ a, seqProb n g * (((cnt g a : ℚ) + 1) / (n + k)) = seqProb n g := by
      intro g
      rw [← mul_sum, ← sum_div, sum_add_distrib]
      have hs : ∑ a, (cnt g a : ℚ) = n := by exact_mod_cast sum_cnt g
      rw [hs]
      simp [div_self hnk]
    simp only [this, ih]

/-- Probability that after `n` draws the colour counts equal `v`. -/
def countProb (n : ℕ) (v : Fin k → ℕ) : ℚ :=
  ∑ f : Fin n → Fin k, if counts f = v then seqProb n f else 0

theorem counts_snoc_eq_iff {n : ℕ} (g : Fin n → Fin k) (a : Fin k) (v : Fin k → ℕ) :
    counts (Fin.snoc (α := fun _ => Fin k) g a) = v ↔
      1 ≤ v a ∧ counts g = Function.update v a (v a - 1) := by
  unfold counts
  constructor
  · intro h
    have ha := congrFun h a
    simp only [cnt_snoc, ite_true] at ha
    refine ⟨by omega, funext fun c => ?_⟩
    by_cases hc : c = a
    · subst hc; simp; omega
    · have := congrFun h c
      simp only [cnt_snoc, Ne.symm hc, ite_false, add_zero] at this
      rw [Function.update_of_ne hc, this]
  · rintro ⟨h1, h⟩
    funext c
    have := congrFun h c
    rw [cnt_snoc]
    by_cases hc : c = a
    · subst hc; simp at this ⊢; omega
    · rw [Function.update_of_ne hc] at this
      simp [this, Ne.symm hc]

/-- Bose–Einstein law: after `n` draws every count vector with total `n` has probability
`1 / C(n + k - 1, k - 1)`. -/
theorem countProb_uniform (hk : 0 < k) (n : ℕ) (v : Fin k → ℕ) (hv : ∑ c, v c = n) :
    countProb n v = 1 / ((n + k - 1).choose (k - 1) : ℚ) := by
  induction n generalizing v with
  | zero =>
    have hv0 : v = 0 := funext fun c => by
      have := (sum_eq_zero_iff.mp hv) c (mem_univ c); simpa using this
    subst hv0
    have hc : ∀ f : Fin 0 → Fin k, counts f = 0 := fun f => funext fun c => cnt_zero f c
    simp [countProb, hc, seqProb]
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hnk : (n : ℚ) + (m + 1 : ℕ) ≠ 0 := by positivity
    set Q : ℚ := 1 / ((n + (m + 1) - 1).choose (m + 1 - 1) : ℚ) with hQ
    have step : ∀ a : Fin (m + 1),
        ∑ g : Fin n → Fin (m + 1),
          (if counts (Fin.snoc (α := fun _ => Fin (m + 1)) g a) = v then
            seqProb (n + 1) (Fin.snoc (α := fun _ => Fin (m + 1)) g a) else 0) =
          (v a : ℚ) / (n + (m + 1 : ℕ)) * Q := by
      intro a
      simp only [counts_snoc_eq_iff]
      by_cases hva : 1 ≤ v a
      · set w := Function.update v a (v a - 1) with hw
        have hwsum : ∑ c, w c = n := by
          have h1 := sum_update_of_mem (mem_univ a) v (v a - 1)
          have h2 := add_sum_erase univ v (mem_univ a)
          rw [← hw] at h1
          rw [h1, ← sdiff_singleton_eq_erase] at *
          omega
        have hterm : ∀ g : Fin n → Fin (m + 1),
            (if 1 ≤ v a ∧ counts g = w then
              seqProb (n + 1) (Fin.snoc (α := fun _ => Fin (m + 1)) g a) else 0) =
            (if counts g = w then seqProb n g else 0) * ((v a : ℚ) / (n + (m + 1 : ℕ))) := by
          intro g
          by_cases hg : counts g = w
          · have hca : cnt g a = v a - 1 := by
              have := congrFun hg a; simpa [counts, hw] using this
            rw [ite_eq_left ⟨hva, hg⟩, ite_eq_left hg, seqProb_snoc, hca]
            congr 2
            rw [Nat.cast_sub hva]; ring
          · rw [ite_eq_right (fun h => hg h.2), ite_eq_right hg, zero_mul]
        rw [sum_congr rfl fun g _ => hterm g, ← sum_mul]
        rw [show (∑ g : Fin n → Fin (m + 1), if counts g = w then seqProb n g else 0) =
          countProb n w from rfl, ih w hwsum, hQ]
        ring_nf
      · have : v a = 0 := by omega
        simp [this]
    rw [countProb, sum_snoc, sum_congr rfl fun a _ => step a, ← sum_mul, ← sum_div]
    have hs : ∑ a, (v a : ℚ) = n + 1 := by exact_mod_cast hv
    rw [hs, hQ]
    -- binomial identity C(n+m, m) (n+m+1) = C(n+m+1, m) (n+1)
    have hid := Nat.choose_mul_succ_eq (n + m) m
    rw [show n + m + 1 - m = n + 1 by omega] at hid
    have hpos1 : 0 < (n + m).choose m := Nat.choose_pos (by omega)
    have hpos2 : 0 < (n + m + 1).choose m := Nat.choose_pos (by omega)
    simp only [show n + (m + 1) - 1 = n + m by omega, show n + 1 + (m + 1) - 1 = n + m + 1 by omega,
      show m + 1 - 1 = m by omega]
    have hidq : ((n + m).choose m : ℚ) * ((n + m : ℕ) + 1) = ((n + m + 1).choose m : ℚ) * (n + 1) := by
      exact_mod_cast hid
    field_simp
    push_cast at hidq ⊢
    linarith

/-- Two colours: the number of draws of the first colour is uniform on `{0, …, n}`. -/
theorem countProb_two (n j : ℕ) (hj : j ≤ n) :
    countProb (k := 2) n ![j, n - j] = 1 / (n + 1) := by
  rw [countProb_uniform (by norm_num) n _ (by simp [Fin.sum_univ_two]; omega)]
  simp

end PolyaBoseEinstein
