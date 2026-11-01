import Mathlib

/-!
# P1: Maximum entropy gives the exponential family (and the discrete Gaussian)

Setting: a finite type `ι`, real statistics, natural logarithms, and distributions that are
strictly positive (`∀ i, 0 < q i`) and sum to one.

What is PROVED here:
* `gibbs` — Gibbs' inequality `∑ p log b ≤ ∑ p log p` (via `log x ≤ x - 1`).
* `maxent_one` — for one statistic `f` and any `lam : ℝ`, the Gibbs distribution
  `p i = exp (lam * f i) / Z` has entropy at least that of every positive distribution `q`
  with the same expectation of `f`.
* `maxent_multi` — the same for `k` statistics `f : Fin k → ι → ℝ` and parameters
  `lam : Fin k → ℝ`, with `p i ∝ exp (∑ j, lam j * f j i)`, matching all `k` expectations.
* `maxent_discrete_gaussian` — on any finite family of reals `x : ι → ℝ`, the distribution
  `∝ exp (lam * x i ^ 2)` maximises entropy among positive distributions with the same
  second moment.
* `maxent_discrete_gaussian_mean_var` — `∝ exp (a * x i + b * x i ^ 2)` maximises entropy
  among positive distributions with the same first and second moments.
* `maxent_multi_nonneg` (added by the second agent) — `maxent_multi` with the comparison
  distribution `q` only NONNEGATIVE (zeros allowed), using `0 log 0 = 0`, which Mathlib gives
  for free since `Real.log 0 = 0`. The Gibbs distribution itself is always strictly positive.

What is only INTERPRETED (not proved): that this is "the" Jaynes maxent principle in general;
we do not prove that for every moment value there EXISTS a `lam` attaining it (the
parameter is given and the moment constraint is taken to be the Gibbs distribution's own),
nor uniqueness of the maximiser, nor anything about continuous densities. When `lam < 0`
the second-moment family is a genuine discretised Gaussian `exp (-x²/(2σ²))`; the theorem
holds for every real `lam`.
-/

open Finset Real

namespace P1Maxent

variable {ι : Type*} [Fintype ι]

/-- Shannon entropy (natural log) of a function `q : ι → ℝ`. -/
noncomputable def entropy (q : ι → ℝ) : ℝ := -∑ i, q i * log (q i)

/-- Partition function for one statistic. -/
noncomputable def partition (f : ι → ℝ) (lam : ℝ) : ℝ := ∑ i, exp (lam * f i)

/-- Gibbs / exponential-family distribution for one statistic. -/
noncomputable def gibbsDist (f : ι → ℝ) (lam : ℝ) (i : ι) : ℝ :=
  exp (lam * f i) / partition f lam

/-- Partition function for `k` statistics. -/
noncomputable def partitionK {k : ℕ} (f : Fin k → ι → ℝ) (lam : Fin k → ℝ) : ℝ :=
  ∑ i, exp (∑ j, lam j * f j i)

/-- Gibbs / exponential-family distribution for `k` statistics. -/
noncomputable def gibbsDistK {k : ℕ} (f : Fin k → ι → ℝ) (lam : Fin k → ℝ) (i : ι) : ℝ :=
  exp (∑ j, lam j * f j i) / partitionK f lam

/-- **Gibbs' inequality.** For positive `p` summing to one and positive `b` with total mass
at most one, `∑ p log b ≤ ∑ p log p`. -/
theorem gibbs (p b : ι → ℝ) (hp : ∀ i, 0 < p i) (hb : ∀ i, 0 < b i)
    (hp1 : ∑ i, p i = 1) (hb1 : ∑ i, b i ≤ 1) :
    ∑ i, p i * log (b i) ≤ ∑ i, p i * log (p i) := by
  have key : ∀ i, p i * log (b i) - p i * log (p i) ≤ b i - p i := by
    intro i
    have h := log_le_sub_one_of_pos (div_pos (hb i) (hp i))
    rw [log_div (hb i).ne' (hp i).ne'] at h
    have h2 : p i * (log (b i) - log (p i)) ≤ p i * (b i / p i - 1) :=
      mul_le_mul_of_nonneg_left h (hp i).le
    have e : p i * (b i / p i - 1) = b i - p i := by
      have hp0 := (hp i).ne'
      field_simp
    linarith [h2, e, show p i * (log (b i) - log (p i)) = p i * log (b i) - p i * log (p i) by ring]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at this
  linarith

/-- The Gibbs distribution is a strictly positive probability distribution. -/
theorem gibbsDist_pos [Nonempty ι] (f : ι → ℝ) (lam : ℝ) (i : ι) : 0 < gibbsDist f lam i := by
  unfold gibbsDist partition
  exact div_pos (exp_pos _) (Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty)

theorem gibbsDist_sum [Nonempty ι] (f : ι → ℝ) (lam : ℝ) : ∑ i, gibbsDist f lam i = 1 := by
  unfold gibbsDist
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty).ne'

theorem gibbsDistK_pos [Nonempty ι] {k : ℕ} (f : Fin k → ι → ℝ) (lam : Fin k → ℝ) (i : ι) :
    0 < gibbsDistK f lam i := by
  unfold gibbsDistK partitionK
  exact div_pos (exp_pos _) (Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty)

theorem gibbsDistK_sum [Nonempty ι] {k : ℕ} (f : Fin k → ι → ℝ) (lam : Fin k → ℝ) :
    ∑ i, gibbsDistK f lam i = 1 := by
  unfold gibbsDistK
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty).ne'

/-- Helper (not in the statements file): a distribution summing to one lives on a nonempty
type. -/
theorem nonempty_of_sum_eq_one (q : ι → ℝ) (hq1 : ∑ i, q i = 1) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  simp [Finset.univ_eq_empty] at hq1

/-- Helper (not in the statements file): swapping a weighted double sum. -/
theorem swap_sum {k : ℕ} (r : ι → ℝ) (f : Fin k → ι → ℝ) (lam : Fin k → ℝ) :
    ∑ i, r i * ∑ j, lam j * f j i = ∑ j, lam j * ∑ i, r i * f j i := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))

/-- Helper (not in the statements file): the core maxent argument. If `log p = g - c`
pointwise and `q` matches the mean of `g`, then `entropy q ≤ entropy p`. -/
theorem maxent_core (p q g : ι → ℝ) (c : ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1) (hlog : ∀ i, log (p i) = g i - c)
    (hg : ∑ i, q i * g i = ∑ i, p i * g i) : entropy q ≤ entropy p := by
  have G := gibbs q p hq hp hq1 hp1.le
  have e : ∀ r : ι → ℝ, ∑ i, r i = 1 → ∑ i, r i * log (p i) = ∑ i, r i * g i - c := by
    intro r hr
    simp only [hlog, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hr, one_mul]
  unfold entropy
  rw [e q hq1] at G
  rw [e p hp1]
  linarith

/-- **Maxent, one statistic.** Among strictly positive distributions `q` with the same mean
of `f` as the Gibbs distribution `∝ exp (lam * f)`, the Gibbs distribution has maximal
Shannon entropy. -/
theorem maxent_one (f : ι → ℝ) (lam : ℝ) (q : ι → ℝ) (hq : ∀ i, 0 < q i)
    (hq1 : ∑ i, q i = 1)
    (hmean : ∑ i, q i * f i = ∑ i, gibbsDist f lam i * f i) :
    entropy q ≤ entropy (gibbsDist f lam) := by
  have := nonempty_of_sum_eq_one q hq1
  have hZ : 0 < partition f lam :=
    Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty
  refine maxent_core (gibbsDist f lam) q (fun i => lam * f i) (log (partition f lam))
    (gibbsDist_pos f lam) (gibbsDist_sum f lam) hq hq1 ?_ ?_
  · intro i
    unfold gibbsDist
    rw [log_div (exp_pos _).ne' hZ.ne', log_exp]
  · simp only [mul_left_comm _ lam, ← Finset.mul_sum]
    rw [hmean]

/-- **Maxent, `k` statistics.** Among strictly positive distributions matching all `k`
expectations of the Gibbs distribution `∝ exp (∑ j, lam j * f j)`, the Gibbs distribution
has maximal Shannon entropy. -/
theorem maxent_multi {k : ℕ} (f : Fin k → ι → ℝ) (lam : Fin k → ℝ) (q : ι → ℝ)
    (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1)
    (hmean : ∀ j, ∑ i, q i * f j i = ∑ i, gibbsDistK f lam i * f j i) :
    entropy q ≤ entropy (gibbsDistK f lam) := by
  have := nonempty_of_sum_eq_one q hq1
  have hZ : 0 < partitionK f lam :=
    Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty
  refine maxent_core (gibbsDistK f lam) q (fun i => ∑ j, lam j * f j i)
    (log (partitionK f lam)) (gibbsDistK_pos f lam) (gibbsDistK_sum f lam) hq hq1 ?_ ?_
  · intro i
    unfold gibbsDistK
    rw [log_div (exp_pos _).ne' hZ.ne', log_exp]
  · rw [swap_sum, swap_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [hmean j])

/-- **Discrete Gaussian (second moment).** On any finite family of reals `x`, the
distribution `∝ exp (lam * x i ^ 2)` maximises entropy among strictly positive
distributions with the same second moment. -/
theorem maxent_discrete_gaussian (x : ι → ℝ) (lam : ℝ) (q : ι → ℝ) (hq : ∀ i, 0 < q i)
    (hq1 : ∑ i, q i = 1)
    (hmom : ∑ i, q i * x i ^ 2 = ∑ i, gibbsDist (fun i => x i ^ 2) lam i * x i ^ 2) :
    entropy q ≤ entropy (gibbsDist (fun i => x i ^ 2) lam) := by
  exact maxent_one (fun i => x i ^ 2) lam q hq hq1 hmom

/-- **Discrete Gaussian (mean and second moment).** The distribution
`∝ exp (a * x i + b * x i ^ 2)` maximises entropy among strictly positive distributions with
the same first and second moments. -/
theorem maxent_discrete_gaussian_mean_var (x : ι → ℝ) (a b : ℝ) (q : ι → ℝ)
    (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1)
    (hm1 : ∑ i, q i * x i = ∑ i, gibbsDistK ![x, fun i => x i ^ 2] ![a, b] i * x i)
    (hm2 : ∑ i, q i * x i ^ 2 =
      ∑ i, gibbsDistK ![x, fun i => x i ^ 2] ![a, b] i * x i ^ 2) :
    entropy q ≤ entropy (gibbsDistK ![x, fun i => x i ^ 2] ![a, b]) := by
  refine maxent_multi ![x, fun i => x i ^ 2] ![a, b] q hq hq1 ?_
  intro j
  fin_cases j
  · simpa using hm1
  · simpa using hm2


/-- Helper (not in the statements file): Gibbs' inequality with `p` only nonnegative.
Mathlib's `Real.log 0 = 0` makes `0 * log 0 = 0`, i.e. the usual `0 log 0 = 0` convention. -/
theorem gibbs_nonneg (p b : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hb : ∀ i, 0 < b i)
    (hp1 : ∑ i, p i = 1) (hb1 : ∑ i, b i ≤ 1) :
    ∑ i, p i * log (b i) ≤ ∑ i, p i * log (p i) := by
  have key : ∀ i, p i * log (b i) - p i * log (p i) ≤ b i - p i := by
    intro i
    rcases (hp i).eq_or_lt with h0 | hpos
    · rw [← h0]; simp [(hb i).le]
    have h := log_le_sub_one_of_pos (div_pos (hb i) hpos)
    rw [log_div (hb i).ne' hpos.ne'] at h
    have h2 : p i * (log (b i) - log (p i)) ≤ p i * (b i / p i - 1) :=
      mul_le_mul_of_nonneg_left h hpos.le
    have e : p i * (b i / p i - 1) = b i - p i := by
      have hp0 := hpos.ne'
      field_simp
    linarith [h2, e, show p i * (log (b i) - log (p i)) = p i * log (b i) - p i * log (p i) by ring]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at this
  linarith

/-- **Maxent, `k` statistics, comparison distributions allowed to have zeros.** Same as
`maxent_multi` but `q` need only be nonnegative (`0 ≤ q i`); entropy uses `0 log 0 = 0`
(automatic in Mathlib since `Real.log 0 = 0`). This strictly generalises `maxent_multi`,
and with `k = 1` it covers `maxent_one` for `q` with zeros. -/
theorem maxent_multi_nonneg {k : ℕ} (f : Fin k → ι → ℝ) (lam : Fin k → ℝ) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (hmean : ∀ j, ∑ i, q i * f j i = ∑ i, gibbsDistK f lam i * f j i) :
    entropy q ≤ entropy (gibbsDistK f lam) := by
  have := nonempty_of_sum_eq_one q hq1
  have hZ : 0 < partitionK f lam :=
    Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty
  set p := gibbsDistK f lam with hpdef
  have hlog : ∀ i, log (p i) = (∑ j, lam j * f j i) - log (partitionK f lam) := by
    intro i
    rw [hpdef]; unfold gibbsDistK
    rw [log_div (exp_pos _).ne' hZ.ne', log_exp]
  have G := gibbs_nonneg q p hq (gibbsDistK_pos f lam) hq1 (gibbsDistK_sum f lam).le
  have e : ∀ r : ι → ℝ, ∑ i, r i = 1 →
      ∑ i, r i * log (p i) = ∑ i, r i * ∑ j, lam j * f j i - log (partitionK f lam) := by
    intro r hr
    simp only [hlog, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hr, one_mul]
  have hg : ∑ i, q i * ∑ j, lam j * f j i = ∑ i, p i * ∑ j, lam j * f j i := by
    rw [swap_sum, swap_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [hmean j])
  unfold entropy
  rw [e q hq1] at G
  rw [e p (gibbsDistK_sum f lam)]
  linarith

/-- Sanity check (non-vacuity): on `x = (-1, 0, 1)` with statistic `x²` and `lam = 0`, the
Gibbs distribution is uniform (second moment `2/3`), and `q = (1/2, 1/3, 1/6)` — a different
positive distribution — has the same second moment, so `maxent_discrete_gaussian` applies. -/
example : entropy (![1/2, 1/3, 1/6] : Fin 3 → ℝ) ≤
    entropy (gibbsDist (fun i => (![-1, 0, 1] : Fin 3 → ℝ) i ^ 2) 0) := by
  have hp : ∀ i, gibbsDist (fun i => (![-1, 0, 1] : Fin 3 → ℝ) i ^ 2) 0 i = 1 / 3 := by
    intro i
    simp [gibbsDist, partition]
  refine maxent_discrete_gaussian _ 0 _ ?_ ?_ ?_
  · intro i; fin_cases i <;> norm_num
  · simp [Fin.sum_univ_three]; norm_num
  · simp only [hp, Fin.sum_univ_three]; norm_num

/-- Sanity check (non-vacuity, with a zero): on `x = (-1, 0, 1)` with the single statistic
`x²` and `lam = 0`, the Gibbs distribution is uniform (second moment `2/3`), and
`q = (0, 1/3, 2/3)`, which has a zero entry, has the same second moment, so
`maxent_multi_nonneg` applies (`maxent_multi` would not). -/
example : entropy (![0, 1/3, 2/3] : Fin 3 → ℝ) ≤
    entropy (gibbsDistK ![fun i => (![-1, 0, 1] : Fin 3 → ℝ) i ^ 2] ![0]) := by
  have hp : ∀ i, gibbsDistK ![fun i => (![-1, 0, 1] : Fin 3 → ℝ) i ^ 2] ![0] i = 1 / 3 := by
    intro i
    simp [gibbsDistK, partitionK]
  refine maxent_multi_nonneg _ _ _ ?_ ?_ ?_
  · intro i; fin_cases i <;> norm_num
  · simp [Fin.sum_univ_three]; norm_num
  · intro j; fin_cases j
    simp only [hp, Fin.sum_univ_three]; norm_num

end P1Maxent
