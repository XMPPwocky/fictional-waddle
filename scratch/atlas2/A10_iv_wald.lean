import Mathlib

/-!
# A10 (iv): the Wald / instrumental-variables ratio on finite samples

Proofs. Statements are identical to `A10_iv_wald.statements.lean`; one
private helper lemma (`mean_affine`) and one concrete `example` (n = 3,
Wald = 3 vs OLS = 24/7) are added in this file only.

All quantities are *sample* moments of vectors `Fin n → ℝ`; no probability
theory is involved. "Exclusion" and "relevance" are hypotheses on sample
covariances, not on population ones.
-/

namespace Atlas2.A10

open Finset BigOperators

variable {n : ℕ}

/-- Sample mean `(1/n) Σ X_i` (equal to `0` when `n = 0`, by `x / 0 = 0`). -/
noncomputable def mean (X : Fin n → ℝ) : ℝ := (∑ i, X i) / n

/-- Sample covariance `(1/n) Σ (X_i - mean X)(Y_i - mean Y)`. -/
noncomputable def cov (X Y : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (X i - mean X) * (Y i - mean Y)

/-- Sample variance `var X = cov X X`. -/
noncomputable def var (X : Fin n → ℝ) : ℝ := cov X X

/-- Helper (added in the proofs file only): for `n ≠ 0` the sample mean is
affine. -/
private lemma mean_affine (X Y : Fin n → ℝ) (a b c : ℝ) (hn : (n : ℝ) ≠ 0) :
    mean (fun i => a * X i + b * Y i + c) = a * mean X + b * mean Y + c := by
  simp only [mean, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Proved:** the sample covariance against an affine combination splits:
`cov(Z, a·X + b·Y + c) = a·cov(Z,X) + b·cov(Z,Y)`.
(Holds for every `n`, including `n = 0` where both sides are `0`.) -/
theorem cov_affine_right (Z X Y : Fin n → ℝ) (a b c : ℝ) :
    cov Z (fun i => a * X i + b * Y i + c) = a * cov Z X + b * cov Z Y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cov]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [cov, cov, cov, mean_affine X Y a b c hn']
    have hpt : ∀ i, (Z i - mean Z) * (a * X i + b * Y i + c - (a * mean X + b * mean Y + c))
        = a * ((Z i - mean Z) * (X i - mean X)) + b * ((Z i - mean Z) * (Y i - mean Y)) := by
      intro i; ring
    simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

/-- **Proved (Wald ratio identifies β):** if `A = β·G + U + c₁` and
`G = π·Z + V + c₂` componentwise, `cov(Z,U) = 0` (sample exclusion) and
`cov(Z,G) ≠ 0` (sample relevance), then `cov(Z,A) / cov(Z,G) = β`.

*Interpretation (not proved):* the first-stage equation for `G` is not
actually used — the identity is purely the exclusion restriction plus
relevance; the first stage only explains *why* relevance might hold. -/
theorem wald_eq_beta (Z G A U V : Fin n → ℝ) (β π c₁ c₂ : ℝ)
    (hA : ∀ i, A i = β * G i + U i + c₁)
    (hG : ∀ i, G i = π * Z i + V i + c₂)
    (hexcl : cov Z U = 0) (hrel : cov Z G ≠ 0) :
    cov Z A / cov Z G = β := by
  -- `hG` (first stage) is not needed for the identity; the unused-variable
  -- warning is expected (see docstring).
  have hAf : A = fun i => β * G i + 1 * U i + c₁ := by
    funext i; rw [hA i]; ring
  rw [hAf, cov_affine_right, hexcl]
  field_simp
  ring

/-- **Proved (first stage):** under `G = π·Z + V + c₂`,
`cov(Z,G) = π·var(Z) + cov(Z,V)`. -/
theorem first_stage (Z G V : Fin n → ℝ) (π c₂ : ℝ)
    (hG : ∀ i, G i = π * Z i + V i + c₂) :
    cov Z G = π * var Z + cov Z V := by
  have hGf : G = fun i => π * Z i + 1 * V i + c₂ := by
    funext i; rw [hG i]; ring
  rw [hGf, cov_affine_right, var]
  ring

/-- **Proved:** under `G = π·Z + V + c₂` with `cov(Z,V) = 0`, sample
relevance `cov(Z,G) ≠ 0` holds iff `π ≠ 0` and `var Z ≠ 0`. -/
theorem relevance_iff (Z G V : Fin n → ℝ) (π c₂ : ℝ)
    (hG : ∀ i, G i = π * Z i + V i + c₂) (hZV : cov Z V = 0) :
    cov Z G ≠ 0 ↔ (π ≠ 0 ∧ var Z ≠ 0) := by
  rw [first_stage Z G V π c₂ hG, hZV, add_zero, mul_ne_zero_iff]

/-- **Proved (OLS bias):** if `A = β·G + U + c₁` and `var G ≠ 0`, the OLS
slope satisfies `cov(G,A)/var(G) = β + cov(G,U)/var(G)` exactly.

*Interpretation (not proved):* the bias term `cov(G,U)/var(G)` is the
confounding term; it vanishes iff `cov(G,U) = 0` (see `ols_unbiased_iff`). -/
theorem ols_slope (G A U : Fin n → ℝ) (β c₁ : ℝ)
    (hA : ∀ i, A i = β * G i + U i + c₁) (hvar : var G ≠ 0) :
    cov G A / var G = β + cov G U / var G := by
  have hAf : A = fun i => β * G i + 1 * U i + c₁ := by
    funext i; rw [hA i]; ring
  rw [hAf, cov_affine_right, ← var]
  field_simp

/-- **Proved:** OLS recovers `β` exactly iff the sample confounding term
`cov(G,U)` vanishes. -/
theorem ols_unbiased_iff (G A U : Fin n → ℝ) (β c₁ : ℝ)
    (hA : ∀ i, A i = β * G i + U i + c₁) (hvar : var G ≠ 0) :
    cov G A / var G = β ↔ cov G U = 0 := by
  rw [ols_slope G A U β c₁ hA hvar, add_eq_left, div_eq_zero_iff]
  simp [hvar]

/-- **Proved (exclusion violated):** if instead `A = β·G + δ·Z + U + c₁`
with `cov(Z,U) = 0` and `cov(Z,G) ≠ 0`, the Wald ratio is
`β + δ·var(Z)/cov(Z,G)`. -/
theorem wald_exclusion_violated (Z G A U : Fin n → ℝ) (β δ c₁ : ℝ)
    (hA : ∀ i, A i = β * G i + δ * Z i + U i + c₁)
    (hexcl : cov Z U = 0) (hrel : cov Z G ≠ 0) :
    cov Z A / cov Z G = β + δ * var Z / cov Z G := by
  have hAf : A = fun i => β * G i + 1 * (δ * Z i + U i) + c₁ := by
    funext i; rw [hA i]; ring
  have hW : (fun i => δ * Z i + U i) = fun i => δ * Z i + 1 * U i + 0 := by
    funext i; ring
  rw [hAf, cov_affine_right, hW, cov_affine_right, hexcl, ← var]
  field_simp
  ring

/-- **Proved (added by second agent; generalization):** with no exclusion
hypothesis at all, if `A = β·G + U + c₁` and `cov(Z,G) ≠ 0`, then the Wald
ratio is `cov(Z,A)/cov(Z,G) = β + cov(Z,U)/cov(Z,G)`.

`wald_eq_beta` is the special case `cov(Z,U) = 0`; `wald_exclusion_violated`
is the special case `U := δ·Z + U'` with `cov(Z,U') = 0`.

*Interpretation (not proved):* the IV bias is the instrument–error
covariance scaled by the inverse first-stage strength, so a weak instrument
(small `cov(Z,G)`) amplifies any exclusion violation. -/
theorem wald_bias (Z G A U : Fin n → ℝ) (β c₁ : ℝ)
    (hA : ∀ i, A i = β * G i + U i + c₁) (hrel : cov Z G ≠ 0) :
    cov Z A / cov Z G = β + cov Z U / cov Z G := by
  have hAf : A = fun i => β * G i + 1 * U i + c₁ := by
    funext i; rw [hA i]; ring
  rw [hAf, cov_affine_right]
  field_simp

/-- **Concrete check (proved):** `n = 3`, instrument `Z = (-1, 0, 1)`,
error `U = (1, -2, 1)` (so `cov(Z,U) = 0`), first stage `G = 2·Z + U`
(`π = 2`, `V = U`, so `G` is confounded with `U`), outcome `A = 3·G + U`
(`β = 3`). The Wald ratio from `wald_eq_beta` is `3`, while OLS from
`ols_slope` is `3 + cov(G,U)/var(G) = 3 + 2/(14/3) = 24/7`. -/
example :
    let Z : Fin 3 → ℝ := ![-1, 0, 1]
    let U : Fin 3 → ℝ := ![1, -2, 1]
    let G : Fin 3 → ℝ := fun i => 2 * Z i + U i + 0
    let A : Fin 3 → ℝ := fun i => 3 * G i + U i + 0
    cov Z A / cov Z G = 3 ∧ cov G A / var G = 24 / 7 := by
  intro Z U G A
  have hZU : cov Z U = 0 := by
    simp [cov, mean, Z, U, Fin.sum_univ_three]
  have hZG : cov Z G = 4 / 3 := by
    simp [cov, mean, Z, U, G, Fin.sum_univ_three]; norm_num
  have hGU : cov G U = 2 := by
    simp [cov, mean, Z, U, G, Fin.sum_univ_three]; norm_num
  have hGG : var G = 14 / 3 := by
    simp [var, cov, mean, Z, U, G, Fin.sum_univ_three]; norm_num
  refine ⟨?_, ?_⟩
  · exact wald_eq_beta Z G A U U 3 2 0 0 (fun _ => rfl) (fun _ => rfl) hZU
      (by rw [hZG]; norm_num)
  · rw [ols_slope G A U 3 0 (fun _ => rfl) (by rw [hGG]; norm_num), hGU, hGG]
    norm_num

end Atlas2.A10
