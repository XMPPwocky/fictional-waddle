/-
# The square-root law for cutting with a kerf

Model from L: cutting into K pieces costs w·K in kerf (w = kerf
width) and c/K in envy (c = λρ, how much envy matters times how intensely agents want particular
parts).

PROVED
1. `kerf_lower_bound`: for every K > 0, total cost w·K + c/K ≥ 2√(w·c).
2. `kerf_optimum_attained`: the bound is attained at K* = √(w·c)/w, which equals √(c/w).
3. `kerf_optimum_eq_sqrt_ratio`: √(w·c)/w = √(c/w).

INTERPRETED (not formalized)
- Whether real kerf and envy costs scale as w·K and c/K is the post's modelling assumption. The
  post also states a cube-root law for higher-dimensional settings; that is not checked here.
-/

import Mathlib

namespace KerfLaw

theorem kerf_lower_bound (w c K : ℝ) (hw : 0 < w) (hc : 0 < c) (hK : 0 < K) :
    2 * Real.sqrt (w * c) ≤ w * K + c / K := by
  set s := Real.sqrt (w * c) with hs_def
  have hs : s ^ 2 = w * c := Real.sq_sqrt (by positivity)
  have key : w * K + c / K = (w * K ^ 2 + c) / K := by field_simp
  rw [key, le_div_iff₀ hK]
  nlinarith [sq_nonneg (w * K - s), hs, hw, mul_pos hw hK]

theorem kerf_optimum_attained (w c : ℝ) (hw : 0 < w) (hc : 0 < c) :
    let K := Real.sqrt (w * c) / w
    0 < K ∧ w * K + c / K = 2 * Real.sqrt (w * c) := by
  intro K
  have hs0 : 0 < Real.sqrt (w * c) := Real.sqrt_pos.mpr (by positivity)
  have hs : Real.sqrt (w * c) ^ 2 = w * c := Real.sq_sqrt (by positivity)
  refine ⟨div_pos hs0 hw, ?_⟩
  simp only [K]
  field_simp
  nlinarith [hs]

theorem kerf_optimum_eq_sqrt_ratio (w c : ℝ) (hw : 0 < w) (hc : 0 < c) :
    Real.sqrt (w * c) / w = Real.sqrt (c / w) := by
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  have hs : Real.sqrt (w * c) * Real.sqrt (w * c) = w * c :=
    Real.mul_self_sqrt (by positivity)
  have hs' : Real.sqrt (c * w) ^ 2 = c * w := Real.sq_sqrt (by positivity)
  field_simp
  nlinarith [hs, hs']

end KerfLaw

#print axioms KerfLaw.kerf_lower_bound
#print axioms KerfLaw.kerf_optimum_attained
#print axioms KerfLaw.kerf_optimum_eq_sqrt_ratio
