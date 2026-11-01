/-
# Why time averages and ensemble averages come apart

PROVED
Multiplicative growth:
1. `sum_prod_eq_pow`: summing a product of per-round factors over all 2-outcome histories of length m
   gives (sum of the factors)^m. So the ensemble mean after m fair rounds is ((u + d)/2)^m.
2. `ensemble_mean`: for factors u (heads) and d (tails), the average over all 2^m equally likely
   histories of the final wealth is ((u + d)/2)^m.
3. `geometric_le_arithmetic`, `geometric_lt_arithmetic`: √(u d) ≤ (u + d)/2 for u, d ≥ 0, strictly
   when u ≠ d. `typical_history`: u^n d^n = (u d)^n, the final wealth of any history with n heads and
   n tails.
4. `coin_example`: with u = 3/2 and d = 3/5, the ensemble mean grows by 21/20 per round while the
   typical history shrinks by 9/10 every two rounds.

Many uncertain factors (the Fermi-estimate shape):
5. `fermi_mean`: if each of k independent factors is 1/10, 1 or 10 with equal probability, the mean of
   their product is (37/10)^k, which grows without bound in k.
6. `fermi_median`: yet the product is at most 1 in at least half of the 3^k equally likely cases,
   for every k (by the symmetry 1/10 ↔ 10).

Selection from a complete library:
7. `complete_library_uninformative`: a source whose output is the same in every world cannot be read
   to decide anything that differs between worlds.
8. `selection_cost`: the arithmetic identity |A| · ((1/|A|) · log((1/|A|)/(1/|Ω|))) = log(|Ω|/|A|),
   which is the value of KL(uniform on A ‖ uniform on Ω); the distributions are not defined in Lean.

INTERPRETED (not formalized)
- Histories with equal heads and tails are the typical ones (law of large numbers, not proved here),
  so a typical history grows at the geometric mean, below the arithmetic mean.
- Picking A out of Ω costs log(|Ω|/|A|) nats of selection.
- The ensemble mean is carried by rare histories (all heads; all factors 10); one trajectory, observed
  over time, sees the typical value. They agree only when the growth factor is constant (item 3's
  equality case), i.e. when the process is ergodic in the relevant sense (Peters, "The ergodicity
  problem in economics", 2019).
- Sandberg, Drexler and Ord, "Dissolving the Fermi Paradox" (2018): with uncertainties spanning orders of
  magnitude, the expected number of civilizations can be large while the probability of being alone is
  substantial. Items 5–6 are the smallest exact version.
- Stories are a selected ensemble (see ImaginedVsReal.any_posterior_reachable); a life is one
  trajectory. Comparing the two is comparing an ensemble mean carried by rare histories with a typical
  time path.
-/

import Mathlib

namespace TimeVsEnsemble

open Finset

theorem sum_prod_eq_pow {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) (m : ℕ) :
    ∑ s : Fin m → α, ∏ i, f (s i) = (∑ a, f a) ^ m := by
  rw [← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- Final wealth after a history of heads (true) and tails (false), starting from 1. -/
def wealth (u d : ℝ) {m : ℕ} (s : Fin m → Bool) : ℝ := ∏ i, if s i then u else d

theorem ensemble_mean (u d : ℝ) (m : ℕ) :
    (∑ s : Fin m → Bool, wealth u d s) / 2 ^ m = ((u + d) / 2) ^ m := by
  unfold wealth
  rw [sum_prod_eq_pow (fun b : Bool => if b then u else d) m, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [div_pow]

theorem typical_history (u d : ℝ) (n : ℕ) : u ^ n * d ^ n = (u * d) ^ n := (mul_pow u d n).symm

theorem geometric_le_arithmetic (u d : ℝ) (hu : 0 ≤ u) (hd : 0 ≤ d) :
    Real.sqrt (u * d) ≤ (u + d) / 2 := by
  rw [Real.sqrt_mul hu]
  nlinarith [sq_nonneg (Real.sqrt u - Real.sqrt d), Real.sq_sqrt hu, Real.sq_sqrt hd]

theorem geometric_lt_arithmetic (u d : ℝ) (hu : 0 ≤ u) (hd : 0 ≤ d) (hne : u ≠ d) :
    Real.sqrt (u * d) < (u + d) / 2 := by
  rw [Real.sqrt_mul hu]
  have hne' : Real.sqrt u ≠ Real.sqrt d := fun h => hne (by
    rw [← Real.sq_sqrt hu, ← Real.sq_sqrt hd, h])
  have hpos : 0 < (Real.sqrt u - Real.sqrt d) ^ 2 := by
    have : Real.sqrt u - Real.sqrt d ≠ 0 := sub_ne_zero.mpr hne'
    positivity
  nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hd]

theorem coin_example :
    ((3 / 2 : ℝ) + 3 / 5) / 2 = 21 / 20 ∧ (3 / 2 : ℝ) * (3 / 5) = 9 / 10 ∧
      (1 : ℝ) < 21 / 20 ∧ (9 / 10 : ℝ) < 1 := by
  norm_num

/-! ## Many uncertain factors -/

/-- Factor value for index j ∈ {0, 1, 2}: 10^j / 10, i.e. 1/10, 1 or 10. -/
noncomputable def factor (j : Fin 3) : ℝ := (10 : ℝ) ^ (j : ℕ) / 10

theorem fermi_mean (k : ℕ) :
    (∑ v : Fin k → Fin 3, ∏ i, factor (v i)) / 3 ^ k = (37 / 10) ^ k := by
  rw [sum_prod_eq_pow factor k, Fin.sum_univ_three]
  simp only [factor, Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [← div_pow]
  norm_num

/-- The product is at most 1 exactly when the index sum is at most k. -/
theorem product_le_one_iff (k : ℕ) (v : Fin k → Fin 3) :
    ∏ i, factor (v i) ≤ 1 ↔ ∑ i, (v i : ℕ) ≤ k := by
  simp only [factor, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [div_le_one (by positivity)]
  exact pow_le_pow_iff_right₀ (by norm_num)

/-- Reflect each index: j ↦ 2 − j. -/
def flip (j : Fin 3) : Fin 3 := ⟨2 - j, by omega⟩

theorem flip_flip (j : Fin 3) : flip (flip j) = j := by
  ext; simp [flip]; omega

theorem flip_sum (k : ℕ) (v : Fin k → Fin 3) :
    ∑ i, ((flip (v i) : Fin 3) : ℕ) + ∑ i, (v i : ℕ) = 2 * k := by
  rw [← Finset.sum_add_distrib]
  have : ∀ i, ((flip (v i) : Fin 3) : ℕ) + (v i : ℕ) = 2 := fun i => by
    simp only [flip]; omega
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem fermi_median (k : ℕ) :
    3 ^ k ≤ 2 * (univ.filter fun v : Fin k → Fin 3 => ∏ i, factor (v i) ≤ 1).card := by
  simp_rw [product_le_one_iff]
  set lo := univ.filter fun v : Fin k → Fin 3 => ∑ i, (v i : ℕ) ≤ k
  set hi := univ.filter fun v : Fin k → Fin 3 => ¬ ∑ i, (v i : ℕ) ≤ k
  have htot : lo.card + hi.card = 3 ^ k := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin]
  have hmap : hi.card ≤ lo.card := by
    apply Finset.card_le_card_of_injOn (fun v i => flip (v i))
    · intro v hv
      simp only [hi, lo, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe,
        Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      have := flip_sum k v
      omega
    · intro v _ w _ h
      funext i
      have := congrFun h i
      simp only at this
      rw [← flip_flip (v i), this, flip_flip]
  omega

/-! ## Selection from a complete library -/

theorem complete_library_uninformative {World Book : Type*} (truth : World → Prop)
    (library : World → Set Book) (hall : ∀ w, library w = Set.univ) (read : Set Book → Prop)
    (hread : ∀ w, read (library w) ↔ truth w) (w w' : World) : truth w ↔ truth w' := by
  rw [← hread w, ← hread w', hall w, hall w']

theorem selection_cost (nΩ nA : ℕ) (hA : 0 < nA) (hle : nA ≤ nΩ) :
    (nA : ℝ) * ((1 / nA) * Real.log ((1 / nA) / (1 / nΩ))) = Real.log (nΩ / nA) := by
  have h1 : (0 : ℝ) < nA := by exact_mod_cast hA
  have h2 : (0 : ℝ) < nΩ := by exact_mod_cast lt_of_lt_of_le hA hle
  rw [← mul_assoc, mul_one_div_cancel h1.ne', one_mul]
  congr 1
  field_simp

end TimeVsEnsemble

#print axioms TimeVsEnsemble.sum_prod_eq_pow
#print axioms TimeVsEnsemble.ensemble_mean
#print axioms TimeVsEnsemble.geometric_lt_arithmetic
#print axioms TimeVsEnsemble.coin_example
#print axioms TimeVsEnsemble.fermi_mean
#print axioms TimeVsEnsemble.product_le_one_iff
#print axioms TimeVsEnsemble.fermi_median
#print axioms TimeVsEnsemble.complete_library_uninformative
#print axioms TimeVsEnsemble.selection_cost
