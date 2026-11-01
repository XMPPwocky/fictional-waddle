import Mathlib

/-!
# Futarchy with a randomised branch: the N/A rule removes confounding

Model (for one fixed action `a`; all quantities are explicit finite sums over `U, R ∈ Fin 2`
derived from the joint law, no measure theory):

* confounder `U ∈ Fin 2`, `P(U = 1) = π`, `P(U = 0) = 1 - π`;
* branch `R ∈ Fin 2`, independent of `U`, `P(R = 1) = ε`, `P(R = 0) = 1 - ε`;
* action law `P(A = a | U = u, R = 1) = ρ a` (random branch, independent of `U`),
  `P(A = a | U = u, R = 0) = c a u` (chooser branch, depends on `U`);
* outcome: `E[Y | U = u, R = r, A = a] = m u a` (the branch has no direct effect on `Y`).

Hence `P(U = u, R = r, A = a) = pU π u * pR ε r * pA ρ c u r a` (`joint`), and every
conditional expectation below is the ratio of two such finite sums.

PROVED
* `joint_sum_one`: for finite action sets with `∑ ρ = 1` and `∑_a c a u = 1`, `joint` is a
  probability law on `Fin 2 × Fin 2 × α`.
* `samin_price_eq_causal`: `E[Y | A = a, R = 1] = V a = (1 - π) m 0 a + π m 1 a`
  (needs only `ε ≠ 0`, `ρ a ≠ 0`).
* `margA_eq`, `postU1_eq`: `P(A = a) = ε ρ a + (1 - ε)((1 - π) c a 0 + π c a 1)` and
  `P(U = 1 | A = a) = (ε ρ a π + (1 - ε) c a 1 π) / P(A = a)`.
* `bias_eq`: `E[Y | A = a] - V a = (P(U = 1 | A = a) - π)(m 1 a - m 0 a)` whenever
  `P(A = a) ≠ 0`.
* `bias_closed_form`: the same bias equals
  `(1 - ε) π (1 - π) (c a 1 - c a 0)(m 1 a - m 0 a) / P(A = a)`.
* `bias_ne_zero`: for `π ∈ (0,1)`, `ε ∈ (0,1)`, `ρ a > 0`, `c ≥ 0`, `c a 1 ≠ c a 0`,
  `m 1 a ≠ m 0 a`, the bias is nonzero.
* `bias_at_zero`, `tendsto_bias_zero`, `tendsto_bias_zero_within`: as `ε → 0` the bias tends
  to the fully-chosen bias `(π c a 1 / ((1 - π) c a 0 + π c a 1) - π)(m 1 a - m 0 a)`
  (assuming the chooser plays `a` with positive probability, i.e. that denominator `≠ 0`);
  `chosenBias_ne_zero`: that limit is itself nonzero under the hypotheses of `bias_ne_zero`.
* `tendsto_bias_one`, `tendsto_bias_one_within`: as `ε → 1` the bias tends to `0`
  (assuming `ρ a ≠ 0`).

INTERPRETED
* `condMeanAR π ε ρ c m 1 a` is the price of Samin's market on `a` (resolves only when `R = 1`,
  N/A otherwise), i.e. `E[Y | A = a, R = 1]`; `condMeanA` is the price without the N/A rule,
  i.e. `E[Y | A = a]`.
* The limits are taken in the parameter `ε` with all other parameters fixed; the
  `nhds` versions are stronger than the requested one-sided `ε → 0⁺` / `ε → 1⁻` versions,
  which are stated as the `_within` corollaries on `Set.Ioo 0 1`.
* The key modelling assumption is that `E[Y | U, R, A]` does not depend on `R`: being in the
  random branch changes which action is taken, not what that action does.
-/

namespace FutarchyRandomBranchA

open Filter Topology

variable {α : Type*}

/-- `P(U = u)`. -/
def pU (π : ℝ) (u : Fin 2) : ℝ := if u = 1 then π else 1 - π

/-- `P(R = r)`. -/
def pR (ε : ℝ) (r : Fin 2) : ℝ := if r = 1 then ε else 1 - ε

/-- `P(A = a | U = u, R = r)`. -/
def pA (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (u r : Fin 2) (a : α) : ℝ :=
  if r = 1 then ρ a else c a u

/-- `P(U = u, R = r, A = a)`. -/
def joint (π ε : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (u r : Fin 2) (a : α) : ℝ :=
  pU π u * pR ε r * pA ρ c u r a

/-- Causal value `V a = E[m(U, a)] = (1 - π) m 0 a + π m 1 a`. -/
def V (π : ℝ) (m : Fin 2 → α → ℝ) (a : α) : ℝ := ∑ u, pU π u * m u a

/-- `E[Y | A = a, R = r]`. -/
noncomputable def condMeanAR (π ε : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ)
    (r : Fin 2) (a : α) : ℝ :=
  (∑ u, joint π ε ρ c u r a * m u a) / ∑ u, joint π ε ρ c u r a

/-- `P(A = a)`. -/
def margA (π ε : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (a : α) : ℝ :=
  ∑ u, ∑ r, joint π ε ρ c u r a

/-- `E[Y | A = a]`. -/
noncomputable def condMeanA (π ε : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ)
    (a : α) : ℝ :=
  (∑ u, ∑ r, joint π ε ρ c u r a * m u a) / margA π ε ρ c a

/-- `P(U = 1 | A = a)`. -/
noncomputable def postU1 (π ε : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (a : α) : ℝ :=
  (∑ r, joint π ε ρ c 1 r a) / margA π ε ρ c a

/-- Price bias of the market without the N/A rule. -/
noncomputable def bias (π ε : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ)
    (a : α) : ℝ :=
  condMeanA π ε ρ c m a - V π m a

/-- Bias when the chooser always decides (`ε = 0`). -/
noncomputable def chosenBias (π : ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ) (a : α) : ℝ :=
  (π * c a 1 / ((1 - π) * c a 0 + π * c a 1) - π) * (m 1 a - m 0 a)

theorem joint_sum_one [Fintype α] (π ε : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ)
    (hρ : ∑ a, ρ a = 1) (hc : ∀ u, ∑ a, c a u = 1) :
    ∑ u, ∑ r, ∑ a, joint π ε ρ c u r a = 1 := by
  have h : ∀ u r, ∑ a, joint π ε ρ c u r a = pU π u * pR ε r := by
    intro u r
    simp only [joint, ← Finset.mul_sum, pA]
    by_cases hr : r = 1
    · simp [hr, hρ]
    · simp [hr, hc]
  simp only [h, Fin.sum_univ_two, pU, pR]
  norm_num
  ring

/-- (1) Samin's N/A scheme: the random-branch price equals the causal value. -/
theorem samin_price_eq_causal (π ε : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ)
    (a : α) (hε : ε ≠ 0) (hρ : ρ a ≠ 0) :
    condMeanAR π ε ρ c m 1 a = V π m a := by
  simp only [condMeanAR, V, joint, pU, pR, pA, Fin.sum_univ_two]
  norm_num
  field_simp
  ring

theorem margA_eq (π ε : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (a : α) :
    margA π ε ρ c a = ε * ρ a + (1 - ε) * ((1 - π) * c a 0 + π * c a 1) := by
  simp only [margA, joint, pU, pR, pA, Fin.sum_univ_two]
  norm_num
  ring

theorem postU1_eq (π ε : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (a : α) :
    postU1 π ε ρ c a = (ε * ρ a * π + (1 - ε) * c a 1 * π) /
      (ε * ρ a + (1 - ε) * ((1 - π) * c a 0 + π * c a 1)) := by
  rw [postU1, margA_eq]
  congr 1
  simp only [joint, pU, pR, pA, Fin.sum_univ_two]
  norm_num
  ring

/-- (2) Without the N/A rule the price is biased by `(P(U=1|A=a) - π)(m 1 a - m 0 a)`. -/
theorem bias_eq (π ε : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ) (a : α)
    (hD : margA π ε ρ c a ≠ 0) :
    condMeanA π ε ρ c m a - V π m a = (postU1 π ε ρ c a - π) * (m 1 a - m 0 a) := by
  have hD' := hD
  rw [margA_eq] at hD'
  rw [condMeanA, postU1, margA_eq] at *
  simp only [V, joint, pU, pR, pA, Fin.sum_univ_two]
  norm_num
  field_simp
  ring

theorem bias_closed_form (π ε : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ)
    (a : α) (hD : margA π ε ρ c a ≠ 0) :
    bias π ε ρ c m a =
      (1 - ε) * π * (1 - π) * (c a 1 - c a 0) * (m 1 a - m 0 a) / margA π ε ρ c a := by
  rw [bias, bias_eq π ε ρ c m a hD, postU1_eq]
  rw [margA_eq] at hD ⊢
  field_simp
  ring

theorem margA_pos (π ε : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (a : α)
    (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ a)
    (hc : ∀ u, 0 ≤ c a u) : 0 < margA π ε ρ c a := by
  rw [margA_eq]
  have h1 : 0 < ε * ρ a := mul_pos hε0 hρ
  have h2 : 0 ≤ (1 - ε) * ((1 - π) * c a 0 + π * c a 1) := by
    apply mul_nonneg (by linarith)
    exact add_nonneg (mul_nonneg (by linarith) (hc 0)) (mul_nonneg hπ0 (hc 1))
  linarith

/-- (3a) The bias is nonzero for every `ε ∈ (0,1)` when the chooser's action depends on `U`
and `U` matters for the outcome under `a`. -/
theorem bias_ne_zero (π ε : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ) (a : α)
    (hπ0 : 0 < π) (hπ1 : π < 1) (hε0 : 0 < ε) (hε1 : ε < 1) (hρ : 0 < ρ a)
    (hc : ∀ u, 0 ≤ c a u) (hcne : c a 1 ≠ c a 0) (hmne : m 1 a ≠ m 0 a) :
    bias π ε ρ c m a ≠ 0 := by
  have hD := margA_pos π ε ρ c a hπ0.le hπ1.le hε0 hε1.le hρ hc
  rw [bias_closed_form π ε ρ c m a hD.ne']
  apply div_ne_zero _ hD.ne'
  have h1 : (1 - ε) ≠ 0 := by linarith
  have h2 : (1 - π) ≠ 0 := by linarith
  have h3 : c a 1 - c a 0 ≠ 0 := sub_ne_zero.mpr hcne
  have h4 : m 1 a - m 0 a ≠ 0 := sub_ne_zero.mpr hmne
  have h5 : π ≠ 0 := hπ0.ne'
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h5) h2) h3) h4

/-- The bias as an explicit rational function of `ε`. -/
theorem bias_fun_eq (π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ) (a : α) :
    (fun ε => bias π ε ρ c m a) = fun ε =>
      ((1 - π) * ((1 - ε) * c a 0 * m 0 a + ε * ρ a * m 0 a) +
          π * ((1 - ε) * c a 1 * m 1 a + ε * ρ a * m 1 a)) /
        (ε * ρ a + (1 - ε) * ((1 - π) * c a 0 + π * c a 1)) -
      ((1 - π) * m 0 a + π * m 1 a) := by
  funext ε
  rw [bias, condMeanA, margA_eq]
  congr 1
  · congr 1
    simp only [joint, pU, pR, pA, Fin.sum_univ_two]
    norm_num
    ring
  · simp only [V, pU, Fin.sum_univ_two]
    norm_num

theorem continuousAt_bias (π ε₀ : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ)
    (a : α) (hD : ε₀ * ρ a + (1 - ε₀) * ((1 - π) * c a 0 + π * c a 1) ≠ 0) :
    ContinuousAt (fun ε => bias π ε ρ c m a) ε₀ := by
  rw [bias_fun_eq]
  exact ContinuousAt.sub (ContinuousAt.div (by fun_prop) (by fun_prop) hD) continuousAt_const

theorem bias_at_zero (π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ) (a : α)
    (hc : (1 - π) * c a 0 + π * c a 1 ≠ 0) :
    bias π 0 ρ c m a = chosenBias π c m a := by
  have h := congrFun (bias_fun_eq π ρ c m a) 0
  rw [h, chosenBias]
  norm_num
  field_simp
  ring

/-- (3b) As `ε → 0` the bias tends to the fully-chosen bias. -/
theorem tendsto_bias_zero (π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ) (a : α)
    (hc : (1 - π) * c a 0 + π * c a 1 ≠ 0) :
    Tendsto (fun ε => bias π ε ρ c m a) (𝓝 0) (𝓝 (chosenBias π c m a)) := by
  have hD : (0 : ℝ) * ρ a + (1 - 0) * ((1 - π) * c a 0 + π * c a 1) ≠ 0 := by
    simpa using hc
  have := (continuousAt_bias π 0 ρ c m a hD).tendsto
  rwa [bias_at_zero π ρ c m a hc] at this

theorem tendsto_bias_zero_within (π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ)
    (m : Fin 2 → α → ℝ) (a : α) (hc : (1 - π) * c a 0 + π * c a 1 ≠ 0) :
    Tendsto (fun ε => bias π ε ρ c m a) (𝓝[Set.Ioo 0 1] 0) (𝓝 (chosenBias π c m a)) :=
  (tendsto_bias_zero π ρ c m a hc).mono_left nhdsWithin_le_nhds

theorem chosenBias_ne_zero (π : ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ) (a : α)
    (hπ0 : 0 < π) (hπ1 : π < 1) (hc : (1 - π) * c a 0 + π * c a 1 ≠ 0)
    (hcne : c a 1 ≠ c a 0) (hmne : m 1 a ≠ m 0 a) :
    chosenBias π c m a ≠ 0 := by
  rw [chosenBias]
  apply mul_ne_zero _ (sub_ne_zero.mpr hmne)
  rw [div_sub' hc]
  apply div_ne_zero _ hc
  have h : π * c a 1 - ((1 - π) * c a 0 + π * c a 1) * π =
      π * (1 - π) * (c a 1 - c a 0) := by ring
  rw [h]
  exact mul_ne_zero (mul_ne_zero hπ0.ne' (by linarith)) (sub_ne_zero.mpr hcne)

/-- (3c) As `ε → 1` the bias tends to `0`. -/
theorem tendsto_bias_one (π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ) (a : α)
    (hρ : ρ a ≠ 0) :
    Tendsto (fun ε => bias π ε ρ c m a) (𝓝 1) (𝓝 0) := by
  have hD : (1 : ℝ) * ρ a + (1 - 1) * ((1 - π) * c a 0 + π * c a 1) ≠ 0 := by
    simpa using hρ
  have h := (continuousAt_bias π 1 ρ c m a hD).tendsto
  have h1 : bias π 1 ρ c m a = 0 := by
    rw [congrFun (bias_fun_eq π ρ c m a) 1]
    norm_num
    field_simp
    ring
  rwa [h1] at h

theorem tendsto_bias_one_within (π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ)
    (m : Fin 2 → α → ℝ) (a : α) (hρ : ρ a ≠ 0) :
    Tendsto (fun ε => bias π ε ρ c m a) (𝓝[Set.Ioo 0 1] 1) (𝓝 0) :=
  (tendsto_bias_one π ρ c m a hρ).mono_left nhdsWithin_le_nhds

end FutarchyRandomBranchA
