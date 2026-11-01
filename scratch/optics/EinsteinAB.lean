import Mathlib

/-!
# Einstein's 1917 A/B coefficients as algebra

Two-level system. Level populations `N₁, N₂`, degeneracies `g₁, g₂`, and `x` a real parameter
(read as `hν / kT`). The Boltzmann relation is `N₂ = N₁ · (g₂ / g₁) · exp (-x)`.
Detailed balance with spontaneous emission `A`, stimulated emission `B₂₁` and absorption `B₁₂`
for a radiation density `ρ` is `N₂ (A + B₂₁ ρ) = N₁ B₁₂ ρ`.

`rhoSol` is the closed form `(A / B₂₁) / ((g₁ B₁₂) / (g₂ B₂₁) · exp x - 1)`
(Lean's real division, so it is `0` where the denominator vanishes).

## PROVED

* `detailedBalance_iff_rhoSol`: assume `N₁ > 0`, `g₁ > 0`, `g₂ > 0`, `B₂₁ > 0`, the Boltzmann
  relation, and that the denominator `(g₁ B₁₂)/(g₂ B₂₁) · exp x - 1` is nonzero. Then detailed
  balance holds for `ρ` if and only if `ρ = rhoSol A B₁₂ B₂₁ g₁ g₂ x`. (No sign assumption on `x`.)
* `planck_form_iff`: assume `A, B₁₂, B₂₁, g₁, g₂ > 0`. For a constant `C`,
  `rhoSol … x = C / (exp x - 1)` for every `x > 0` if and only if `g₁ B₁₂ = g₂ B₂₁` and `C = A / B₂₁`.
* `exists_planck_form_iff`: under the same positivity, there is some `C` with
  `rhoSol … x = C / (exp x - 1)` for all `x > 0` if and only if `g₁ B₁₂ = g₂ B₂₁`.
* `planck_solves_iff`: a division-free version. Assume `A, B₂₁, g₁, g₂ > 0`. For a constant `C`,
  the density `ρ(x) = C / (exp x - 1)` satisfies detailed balance (with Boltzmann populations,
  for every `N₁ > 0`) at every `x > 0` if and only if `g₁ B₁₂ = g₂ B₂₁` and `C = A / B₂₁`.
* `noStim_solution`: dropping the stimulated term, i.e. `N₂ A = N₁ B₁₂ ρ`, with Boltzmann
  populations, `N₁ > 0`, `g₁ > 0`, `B₁₂ ≠ 0`, the unique solution is
  `ρ = (g₂ A / (g₁ B₁₂)) · exp (-x)`.
* `wien_ne_planck`: for any `C' ≠ 0` and any `C`, there is an `x > 0`
  with `C' · exp (-x) ≠ C / (exp x - 1)` (the proof checks `x = log 2` and `x = log 4`).
* `noStim_planck_impossible`: with `A, g₁, g₂ > 0` (any `B₁₂`, any `C`), no density of the form `C / (exp x - 1)`
  satisfies the no-stimulated-emission balance `N₂ A = N₁ B₁₂ ρ` (Boltzmann `N₂`) for every
  `x > 0` and every `N₁ > 0` (the proof uses `x = log 2` and `x = log 3` with `N₁ = 1`).

## INTERPRETED (not formalized)

* `x = hν/kT`, so `x > 0` covers all positive temperatures and frequencies; `ρ` is the spectral
  energy density of thermal radiation. Matching the Rayleigh–Jeans limit to fix
  `A / B₂₁ = 8π h ν³ / c³` is not formalized; neither is any statistical mechanics behind the
  Boltzmann ratio, nor the quantity `exp x − 1` as coming from Bose counting.
* "Stimulated emission is needed to obtain Planck's law" is the reading of
  `noStim_planck_impossible` and `wien_ne_planck`.
-/

namespace EinsteinAB

open Real

/-- Detailed balance between absorption and (spontaneous + stimulated) emission. -/
def DetailedBalance (N₁ N₂ A B₁₂ B₂₁ ρ : ℝ) : Prop := N₂ * (A + B₂₁ * ρ) = N₁ * B₁₂ * ρ

/-- The Boltzmann population ratio. -/
def Boltzmann (N₁ N₂ g₁ g₂ x : ℝ) : Prop := N₂ = N₁ * (g₂ / g₁) * exp (-x)

/-- The closed-form solution of detailed balance for `ρ`. -/
noncomputable def rhoSol (A B₁₂ B₂₁ g₁ g₂ x : ℝ) : ℝ :=
  (A / B₂₁) / ((g₁ * B₁₂) / (g₂ * B₂₁) * exp x - 1)

/-- (a) Solving detailed balance for `ρ`. -/
theorem detailedBalance_iff_rhoSol (N₁ N₂ A B₁₂ B₂₁ g₁ g₂ x ρ : ℝ) (hN : 0 < N₁) (hg₁ : 0 < g₁)
    (hg₂ : 0 < g₂) (hB₂₁ : 0 < B₂₁) (hBz : Boltzmann N₁ N₂ g₁ g₂ x)
    (hD : (g₁ * B₁₂) / (g₂ * B₂₁) * exp x - 1 ≠ 0) :
    DetailedBalance N₁ N₂ A B₁₂ B₂₁ ρ ↔ ρ = rhoSol A B₁₂ B₂₁ g₁ g₂ x := by
  unfold DetailedBalance Boltzmann rhoSol at *
  subst hBz
  have hex : 0 < exp x := exp_pos x
  rw [eq_div_iff hD]
  constructor
  · intro h
    -- multiply detailed balance by g₁ exp x / (N₁ g₂ B₂₁)
    have h2 : (N₁ * (g₂ / g₁) * exp (-x) * (A + B₂₁ * ρ)) * (g₁ * exp x / (N₁ * g₂ * B₂₁)) =
        (N₁ * B₁₂ * ρ) * (g₁ * exp x / (N₁ * g₂ * B₂₁)) := by rw [h]
    field_simp at h2 ⊢
    rw [show exp (-x) = (exp x)⁻¹ by rw [exp_neg]] at h2
    field_simp at h2
    linarith
  · intro h
    have h2 : ρ * (g₁ * B₁₂ * exp x - g₂ * B₂₁) = A * g₂ := by
      field_simp at h; linarith
    rw [exp_neg]
    have hgoal : N₁ * g₂ * (A + B₂₁ * ρ) = N₁ * B₁₂ * ρ * (g₁ * exp x) := by
      linear_combination -N₁ * h2
    rw [show N₁ * (g₂ / g₁) * (exp x)⁻¹ * (A + B₂₁ * ρ) =
      N₁ * g₂ * (A + B₂₁ * ρ) / (g₁ * exp x) by field_simp, hgoal]
    field_simp

/-- (b) `rhoSol` is of Planck form `C / (exp x - 1)` on `x > 0` iff `g₁ B₁₂ = g₂ B₂₁` and `C = A/B₂₁`. -/
theorem planck_form_iff (A B₁₂ B₂₁ g₁ g₂ C : ℝ) (hA : 0 < A) (hB₁₂ : 0 < B₁₂) (hB₂₁ : 0 < B₂₁)
    (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) :
    (∀ x > 0, rhoSol A B₁₂ B₂₁ g₁ g₂ x = C / (exp x - 1)) ↔
      (g₁ * B₁₂ = g₂ * B₂₁ ∧ C = A / B₂₁) := by
  set k := (g₁ * B₁₂) / (g₂ * B₂₁) with hk
  have kpos : 0 < k := by positivity
  constructor
  · intro h
    -- evaluate at exp x = t and exp x = t + 1 with t = 1/k + 2
    set t : ℝ := 1 / k + 2 with ht
    have ht1 : 1 < t := by have : 0 < 1 / k := by positivity
                           linarith
    have key : ∀ u : ℝ, 1 < u → 0 < k * u - 1 →
        A / B₂₁ * (u - 1) = C * (k * u - 1) := by
      intro u hu hku
      have hx : 0 < log u := log_pos hu
      have := h (log u) hx
      rw [rhoSol, exp_log (by linarith), ← hk] at this
      rw [div_eq_div_iff hku.ne' (by linarith)] at this
      linarith
    have hkt : 0 < k * t - 1 := by
      rw [ht, mul_add, mul_one_div_cancel kpos.ne']; linarith
    have e1 := key t ht1 hkt
    have e2 := key (t + 1) (by linarith) (by nlinarith)
    have hCk : A / B₂₁ = C * k := by linear_combination e2 - e1
    have hC : C = A / B₂₁ := by
      have := e1; rw [hCk] at this; linarith
    have hAB : 0 < A / B₂₁ := by positivity
    have hk1 : k = 1 := by
      rw [hC] at hCk
      have := hCk; field_simp at this
      nlinarith [this]
    refine ⟨?_, hC⟩
    rw [hk, div_eq_one_iff_eq (by positivity)] at hk1
    exact hk1
  · rintro ⟨hg, hC⟩ x _
    rw [rhoSol, hg, div_self (by positivity), one_mul, hC]

theorem exists_planck_form_iff (A B₁₂ B₂₁ g₁ g₂ : ℝ) (hA : 0 < A) (hB₁₂ : 0 < B₁₂)
    (hB₂₁ : 0 < B₂₁) (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) :
    (∃ C, ∀ x > 0, rhoSol A B₁₂ B₂₁ g₁ g₂ x = C / (exp x - 1)) ↔ g₁ * B₁₂ = g₂ * B₂₁ := by
  constructor
  · rintro ⟨C, hC⟩
    exact ((planck_form_iff A B₁₂ B₂₁ g₁ g₂ C hA hB₁₂ hB₂₁ hg₁ hg₂).mp hC).1
  · intro h
    exact ⟨A / B₂₁, (planck_form_iff A B₁₂ B₂₁ g₁ g₂ _ hA hB₁₂ hB₂₁ hg₁ hg₂).mpr ⟨h, rfl⟩⟩

/-- (b, division-free) The Planck density solves detailed balance at all `x > 0`
iff `g₁ B₁₂ = g₂ B₂₁` and `C = A / B₂₁`. -/
theorem planck_solves_iff (A B₁₂ B₂₁ g₁ g₂ C : ℝ) (hA : 0 < A)
    (hB₂₁ : 0 < B₂₁) (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) :
    (∀ x > 0, ∀ N₁ > 0, DetailedBalance N₁ (N₁ * (g₂ / g₁) * exp (-x)) A B₁₂ B₂₁
        (C / (exp x - 1))) ↔
      (g₁ * B₁₂ = g₂ * B₂₁ ∧ C = A / B₂₁) := by
  -- balance at `x` with `u = exp x > 1` is equivalent to a linear identity in `u`
  have red : ∀ x > 0, ∀ N₁ > 0, (DetailedBalance N₁ (N₁ * (g₂ / g₁) * exp (-x)) A B₁₂ B₂₁
      (C / (exp x - 1)) ↔ g₂ * A * exp x - g₂ * A + g₂ * B₂₁ * C = g₁ * B₁₂ * C * exp x) := by
    intro x hx N₁ hN
    have hu : 1 < exp x := one_lt_exp_iff.mpr hx
    have hu' : exp x - 1 ≠ 0 := by linarith
    unfold DetailedBalance
    rw [exp_neg]
    constructor
    · intro h; field_simp at h; linarith
    · intro h; field_simp; linarith
  constructor
  · intro h
    have l2 := (red (log 2) (log_pos (by norm_num)) 1 one_pos).mp (h _ (log_pos (by norm_num)) 1 one_pos)
    have l3 := (red (log 3) (log_pos (by norm_num)) 1 one_pos).mp (h _ (log_pos (by norm_num)) 1 one_pos)
    rw [exp_log (by norm_num)] at l2 l3
    have c1 : g₂ * A = g₁ * B₁₂ * C := by linarith
    have c2 : g₂ * B₂₁ * C = g₂ * A := by linarith
    have hC : C = A / B₂₁ := by
      field_simp
      have := mul_left_cancel₀ hg₂.ne' (show g₂ * (B₂₁ * C) = g₂ * A by linarith)
      linarith
    refine ⟨?_, hC⟩
    rw [hC] at c1
    field_simp at c1
    linarith
  · rintro ⟨hg, hC⟩ x hx N₁ hN
    rw [red x hx N₁ hN, hC]
    field_simp
    rw [← hg]; ring

/-- (c) Without stimulated emission, the balance `N₂ A = N₁ B₁₂ ρ` forces a Wien-type law. -/
theorem noStim_solution (N₁ N₂ A B₁₂ g₁ g₂ x ρ : ℝ) (hN : 0 < N₁) (hg₁ : 0 < g₁) (hB₁₂ : B₁₂ ≠ 0)
    (hBz : Boltzmann N₁ N₂ g₁ g₂ x) :
    N₂ * A = N₁ * B₁₂ * ρ ↔ ρ = (g₂ * A / (g₁ * B₁₂)) * exp (-x) := by
  unfold Boltzmann at hBz
  subst hBz
  constructor
  · intro h
    have h' : g₂ * exp (-x) * A = g₁ * B₁₂ * ρ := by
      have := mul_left_cancel₀ hN.ne'
        (show N₁ * (g₂ * exp (-x) * A) = N₁ * (g₁ * B₁₂ * ρ) by
          rw [← mul_left_cancel_iff_of_pos hg₁]; field_simp at h ⊢; linarith)
      exact this
    field_simp
    linarith
  · intro h; rw [h]; field_simp

/-- (c) A Wien-type law `C' exp (-x)` with `C' ≠ 0` is never of Planck form on all of `x > 0`. -/
theorem wien_ne_planck (C' C : ℝ) (hC' : C' ≠ 0) :
    ∃ x > 0, C' * exp (-x) ≠ C / (exp x - 1) := by
  by_contra hcon
  push Not at hcon
  have h2 := hcon (log 2) (log_pos (by norm_num))
  have h4 := hcon (log 4) (log_pos (by norm_num))
  rw [exp_neg, exp_log (by norm_num)] at h2 h4
  norm_num at h2 h4
  apply hC'
  linarith

/-- (c) No Planck-form density satisfies the balance without stimulated emission at all `x > 0`. -/
theorem noStim_planck_impossible (A B₁₂ g₁ g₂ C : ℝ) (hA : 0 < A) (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) :
    ¬ ∀ x > 0, ∀ N₁ > 0,
      (N₁ * (g₂ / g₁) * exp (-x)) * A = N₁ * B₁₂ * (C / (exp x - 1)) := by
  intro h
  have h2 := h (log 2) (log_pos (by norm_num)) 1 one_pos
  have h3 := h (log 3) (log_pos (by norm_num)) 1 one_pos
  rw [exp_neg, exp_log (by norm_num)] at h2 h3
  field_simp at h2 h3
  have : g₂ * A = 0 := by nlinarith
  have : 0 < g₂ * A := mul_pos hg₂ hA
  linarith

end EinsteinAB
