import Mathlib

/-!
# Turning around + closing the ledger ⇒ the Standard Model's charges and three colours

One generation shaped like the Standard Model's, with gauge group SU(N) × SU(2) × U(1) and the number of colours `N`
left free. Hypercharges: quark doublet `Q (N, 2, yQ)`, `u^c (N̄, 1, yu)`, `d^c (N̄, 1, yd)`, lepton doublet
`L (1, 2, yL)`, `e^c (1, 1, ye)`, Higgs `H (1, 2, yH)`.

Principle 1, **every trader can turn around** (each chiral fermion gets a mass from the one Higgs): the Yukawa terms
`Q H u^c`, `Q H̃ d^c`, `L H̃ e^c` are invariant, i.e. `yQ + yH + yu = 0`, `yQ - yH + yd = 0`, `yL - yH + ye = 0`.

Principle 2, **every ledger closes** (anomaly freedom): `[SU(2)]²U(1)`: `N yQ + yL = 0`; gravitational:
`2N yQ + N yu + N yd + 2 yL + ye = 0`; Witten's global SU(2) anomaly: the number of doublets `N + 1` is even.

* L1 `hypercharges_forced`: the five fermion hypercharges are fixed in terms of `yH` alone, for every `N`.
* L2 `colour_ledger_automatic`, L3 `cubic_ledger_automatic`: the `[SU(N)]²U(1)` and `U(1)³` ledgers then close by
  themselves.
* L4 `electric_charges`: with `yH = 1/2`, the up and down quarks have charges `1/2 + 1/(2N)` and `-1/2 + 1/(2N)`, the
  electron `-1`; at `N = 3`: `2/3` and `-1/3`.
* L5 `witten_forces_odd`, `three_is_minimal`: the global ledger forces `N` odd, so the smallest non-abelian colour group
  is `N = 3`.
-/

namespace LedgerColour

/-- **L1.** Turning around + closing the two linear ledgers fixes every fermion hypercharge in terms of `yH`. -/
theorem hypercharges_forced (N yQ yu yd yL ye yH : ℝ) (hN : N ≠ 0)
    (y1 : yQ + yH + yu = 0) (y2 : yQ - yH + yd = 0) (y3 : yL - yH + ye = 0)
    (a2 : N * yQ + yL = 0) (ag : 2 * N * yQ + N * yu + N * yd + 2 * yL + ye = 0) :
    yQ = yH / N ∧ yu = -yH * (N + 1) / N ∧ yd = yH * (N - 1) / N ∧ yL = -yH ∧ ye = 2 * yH := by
  have hyL : yL = -N * yQ := by linarith
  have hyu : yu = -yQ - yH := by linarith
  have hyd : yd = -yQ + yH := by linarith
  have hye : ye = -yL + yH := by linarith
  have hH : yL + yH = 0 := by
    rw [hyu, hyd, hye] at ag; linarith
  have hQ : yQ = yH / N := by
    field_simp; linarith [hyL, hH]
  refine ⟨hQ, ?_, ?_, by linarith, by linarith⟩
  · rw [hyu, hQ]; field_simp; ring
  · rw [hyd, hQ]; field_simp; ring

/-- **L2.** The `[SU(N)]²U(1)` ledger closes automatically once every quark can turn around. -/
theorem colour_ledger_automatic (yQ yu yd yH : ℝ) (y1 : yQ + yH + yu = 0) (y2 : yQ - yH + yd = 0) :
    2 * yQ + yu + yd = 0 := by
  linarith

/-- **L3.** The cubic `U(1)³` ledger closes automatically on the forced hypercharges, for every `N ≠ 0`. -/
theorem cubic_ledger_automatic (N yH : ℝ) (hN : N ≠ 0) :
    2 * N * (yH / N) ^ 3 + N * (-yH * (N + 1) / N) ^ 3 + N * (yH * (N - 1) / N) ^ 3
      + 2 * (-yH) ^ 3 + (2 * yH) ^ 3 = 0 := by
  field_simp
  ring

/-- **L4.** Electric charges `Q = T₃ + Y` with `yH = 1/2`: up `1/2 + 1/(2N)`, down `-1/2 + 1/(2N)`, electron `-1`. -/
theorem electric_charges (N : ℝ) (hN : N ≠ 0) :
    (1 / 2 + (1 / 2) / N = 1 / 2 + 1 / (2 * N)) ∧ (-1 / 2 + (1 / 2) / N = -1 / 2 + 1 / (2 * N)) ∧
      (-1 / 2 + -(1 / 2 : ℝ) = -1) ∧
      ((1 / 2 : ℝ) + 1 / (2 * 3) = 2 / 3) ∧ ((-1 / 2 : ℝ) + 1 / (2 * 3) = -1 / 3) := by
  refine ⟨?_, ?_, by norm_num, by norm_num, by norm_num⟩ <;> field_simp <;> ring

/-- **L5a.** Witten's global anomaly: an even number `N + 1` of doublets forces `N` odd. -/
theorem witten_forces_odd (N : ℕ) (h : Even (N + 1)) : Odd N := by
  rcases h with ⟨k, hk⟩
  exact ⟨k - 1, by omega⟩

/-- **L5b.** The smallest non-abelian (`N ≥ 2`) colour group allowed by the global ledger is `N = 3`, and it is
allowed. -/
theorem three_is_minimal : (∀ N : ℕ, 2 ≤ N → Even (N + 1) → 3 ≤ N) ∧ (2 ≤ 3 ∧ Even (3 + 1)) := by
  refine ⟨?_, by norm_num, by decide⟩
  intro N h2 he
  rcases he with ⟨k, hk⟩
  omega

/-- **L6.** The π⁰ → γγ amplitude is proportional to `N (Q_u² − Q_d²)`. On the forced charges it is `1` for every `N`:
that decay cannot see the number of colours once the charges are anomaly-consistent (cf. Bär & Wiese 2001). -/
theorem pi0_blind_to_colour (N : ℝ) (hN : N ≠ 0) :
    N * ((1 / 2 + 1 / (2 * N)) ^ 2 - (-1 / 2 + 1 / (2 * N)) ^ 2) = 1 := by
  field_simp
  ring

end LedgerColour
