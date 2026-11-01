import Mathlib

/-!
# Stars and bars, and uniformity of the Polya-urn law on count vectors

## PROVED

* `card_antidiagonalTuple_choose`: for every `k n : ℕ`, the number of count vectors
  `v : Fin k → ℕ` with `∑ i, v i = n` (the Finset `Finset.Nat.antidiagonalTuple k n`) equals
  `(k + n - 1).choose n`.
* `card_antidiagonalTuple`: for `k ≥ 1`, that number equals `(n + k - 1).choose (k - 1)`
  (stars and bars).
* `card_filter_fin_choose`: for `k ≥ 1`, the number of `v : Fin k → Fin (n + 1)` with
  `∑ i, (v i : ℕ) = n` also equals `(n + k - 1).choose (k - 1)`.
* `sum_prob_eq_one`: if `p v = 1 / (n + k - 1).choose (k - 1)` for every count vector `v` with
  `∑ v = n` (the per-vector law of the Polya urn started with one ball per colour, taken as a
  hypothesis), then `∑_{v : ∑ v = n} p v = 1`, for `k ≥ 1`.
* `prob_eq_inv_card`: under the same hypothesis, every such `v` has
  `p v = 1 / #(antidiagonalTuple k n)`, i.e. `p` is the uniform distribution on the set of
  compositions of `n` into `k` nonnegative parts.
* `prob_uniform`: under the same hypothesis, any two compositions `v w` of `n` into `k` parts have
  `p v = p w`.
* `sum_prob_eq_one_iff_uniform`: for `k ≥ 1`, a function `p` that is constant on the compositions
  sums to `1` over them if and only if that constant is `1 / (n + k - 1).choose (k - 1)`.

## INTERPRETED (not formalized)

* That the Polya urn with one initial ball per colour assigns probability
  `1 / (n + k - 1).choose (k - 1)` to each count vector is not imported here; it is the hypothesis
  `hp` (proved as `PolyaBoseEinstein.countProb_uniform` in
  `scratch/optics/PolyaBoseEinstein.lean`).
-/

namespace StarsAndBarsPolyaUniform

open Finset

/-- Stars and bars, in the form `(k + n - 1).choose n`, valid for all `k n`. -/
theorem card_antidiagonalTuple_choose (k n : ℕ) :
    #(Finset.Nat.antidiagonalTuple k n) = (k + n - 1).choose n := by
  have h := Finset.card_finsuppAntidiag_nat_eq_choose (s := (univ : Finset (Fin k))) n
  rw [card_univ, Fintype.card_fin] at h
  rw [← h]
  refine Finset.card_bij' (fun v _ => Finsupp.equivFunOnFinite.symm v) (fun f _ => ⇑f)
    ?_ ?_ ?_ ?_
  · intro v hv
    rw [Finset.Nat.mem_antidiagonalTuple] at hv
    rw [mem_finsuppAntidiag]
    refine ⟨?_, subset_univ _⟩
    simpa using hv
  · intro f hf
    rw [mem_finsuppAntidiag] at hf
    rw [Finset.Nat.mem_antidiagonalTuple]
    simpa using hf.1
  · intro v _
    simp
  · intro f _
    simp

/-- Stars and bars: for `k ≥ 1`, the number of `v : Fin k → ℕ` with `∑ v = n` is
`(n + k - 1).choose (k - 1)`. -/
theorem card_antidiagonalTuple (k n : ℕ) (hk : 1 ≤ k) :
    #(Finset.Nat.antidiagonalTuple k n) = (n + k - 1).choose (k - 1) := by
  rw [card_antidiagonalTuple_choose]
  have h1 : k + n - 1 = n + k - 1 := by omega
  rw [h1]
  have h2 : n + k - 1 - (k - 1) = n := by omega
  conv_rhs => rw [← Nat.choose_symm (by omega : k - 1 ≤ n + k - 1), h2]

/-- The same count over the bounded encoding `Fin k → Fin (n + 1)`. -/
theorem card_filter_fin_choose (k n : ℕ) (hk : 1 ≤ k) :
    #(univ.filter fun v : Fin k → Fin (n + 1) => ∑ i, (v i : ℕ) = n)
      = (n + k - 1).choose (k - 1) := by
  rw [← card_antidiagonalTuple k n hk]
  have hle : ∀ v : Fin k → ℕ, ∑ i, v i = n → ∀ i, v i < n + 1 := by
    intro v hv i
    have : v i ≤ ∑ j, v j := Finset.single_le_sum (fun j _ => Nat.zero_le (v j)) (mem_univ i)
    omega
  refine Finset.card_bij' (fun v _ => fun i => (v i : ℕ))
    (fun v hv => fun i => ⟨v i, hle v (Finset.Nat.mem_antidiagonalTuple.mp hv) i⟩) ?_ ?_ ?_ ?_
  · intro v hv
    rw [mem_filter] at hv
    rw [Finset.Nat.mem_antidiagonalTuple]
    exact hv.2
  · intro v hv
    rw [mem_filter]
    exact ⟨mem_univ _, by simpa using Finset.Nat.mem_antidiagonalTuple.mp hv⟩
  · intro v _
    rfl
  · intro v _
    rfl

/-- The per-vector probabilities `1 / (n + k - 1).choose (k - 1)` sum to `1`. -/
theorem sum_prob_eq_one (k n : ℕ) (hk : 1 ≤ k) (p : (Fin k → ℕ) → ℝ)
    (hp : ∀ v ∈ Finset.Nat.antidiagonalTuple k n,
      p v = 1 / ((n + k - 1).choose (k - 1) : ℝ)) :
    ∑ v ∈ Finset.Nat.antidiagonalTuple k n, p v = 1 := by
  rw [Finset.sum_congr rfl hp, sum_const, card_antidiagonalTuple k n hk, nsmul_eq_mul]
  have hpos : (0 : ℝ) < ((n + k - 1).choose (k - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  field_simp

/-- Under the hypothesis, `p` is the uniform distribution on compositions: each composition has
probability `1 / #(compositions)`. -/
theorem prob_eq_inv_card (k n : ℕ) (hk : 1 ≤ k) (p : (Fin k → ℕ) → ℝ)
    (hp : ∀ v ∈ Finset.Nat.antidiagonalTuple k n,
      p v = 1 / ((n + k - 1).choose (k - 1) : ℝ))
    (v : Fin k → ℕ) (hv : ∑ i, v i = n) :
    p v = 1 / (#(Finset.Nat.antidiagonalTuple k n) : ℝ) := by
  rw [card_antidiagonalTuple k n hk]
  exact hp v (Finset.Nat.mem_antidiagonalTuple.mpr hv)

/-- Under the hypothesis, any two compositions of `n` into `k` parts are equally likely. -/
theorem prob_uniform (k n : ℕ) (p : (Fin k → ℕ) → ℝ)
    (hp : ∀ v ∈ Finset.Nat.antidiagonalTuple k n,
      p v = 1 / ((n + k - 1).choose (k - 1) : ℝ))
    (v w : Fin k → ℕ) (hv : ∑ i, v i = n) (hw : ∑ i, w i = n) :
    p v = p w := by
  rw [hp v (Finset.Nat.mem_antidiagonalTuple.mpr hv),
    hp w (Finset.Nat.mem_antidiagonalTuple.mpr hw)]

/-- A constant law `c` on the compositions is normalized iff `c = 1 / (n + k - 1).choose (k - 1)`. -/
theorem sum_prob_eq_one_iff_uniform (k n : ℕ) (hk : 1 ≤ k) (p : (Fin k → ℕ) → ℝ) (c : ℝ)
    (hc : ∀ v ∈ Finset.Nat.antidiagonalTuple k n, p v = c) :
    ∑ v ∈ Finset.Nat.antidiagonalTuple k n, p v = 1 ↔
      c = 1 / ((n + k - 1).choose (k - 1) : ℝ) := by
  rw [Finset.sum_congr rfl hc, sum_const, card_antidiagonalTuple k n hk, nsmul_eq_mul]
  have hpos : (0 : ℝ) < ((n + k - 1).choose (k - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp

end StarsAndBarsPolyaUniform
