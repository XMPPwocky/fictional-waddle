import Mathlib

/-!
# Two copying channels, one Gibbs law, two temperatures

Model: a copy is made by choosing between the right symbol (`r`) and a wrong one (`w`) with Gibbs weights.
For a gene the weights are Boltzmann factors `exp (-β E)` with `β = 1/kT` set by the physical environment. For a
meme the weights are logit-choice factors `exp (u/τ)`, where `u` is how appealing the version is to the host and
`τ` is the host's choice temperature (attention).

PROVED:
* `error_ratio`: the wrong/right ratio of a Gibbs copy is `exp (-β (E_w - E_r))`.
* `proofreading`: `n` independent Gibbs discrimination stages multiply to `exp (-(n β Δ))`.
* `wrong_share_le`, `wrong_share_ge`: for `E_w ≥ E_r` the error share lies between `exp (-βΔ)/2` and `exp (-βΔ)`.
  At a fixed temperature a single equilibrium step cannot copy more accurately than `exp (-βΔ)/2`.
* `meme_eq_gene`: the logit share of a meme with appeal `u` at temperature `τ` is exactly the Gibbs share of a
  gene with energy `-u` at `β = 1/τ`. Same law, different meaning of temperature.
* `meme_error_vanishes`: for a fixed appeal gap `Δ > 0`, the bound `exp (-Δ/τ)` on the meme error share tends to 0 as
  the host's temperature `τ → 0⁺`.
INTERPRETED (not formalized): `β = 1/kT` is fixed by the environment, so genes buy accuracy only with stages that
dissipate free energy (Hopfield kinetic proofreading); `τ` belongs to the host, who can lower it by paying attention.
So genes see thermodynamics and memes see the host's attention: decision theory with a temperature the host controls.
-/

namespace GenesMemes
open Real Filter Topology

noncomputable def share (a b : ℝ) : ℝ := exp b / (exp a + exp b)

theorem error_ratio (β Er Ew : ℝ) : exp (-β * Ew) / exp (-β * Er) = exp (-β * (Ew - Er)) := by
  rw [← exp_sub]; ring_nf

theorem proofreading (β Δ : ℝ) (n : ℕ) : (exp (-β * Δ)) ^ n = exp (-(n * β * Δ)) := by
  rw [← exp_nat_mul]; ring_nf

theorem wrong_share_le (β Er Ew : ℝ) : share (-β * Er) (-β * Ew) ≤ exp (-β * (Ew - Er)) := by
  unfold share
  have h1 : 0 < exp (-β * Er) := exp_pos _
  have h2 : 0 < exp (-β * Ew) := exp_pos _
  rw [div_le_iff₀ (by positivity), show -β * (Ew - Er) = -β * Ew - -β * Er by ring, exp_sub]
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  nlinarith [mul_pos h2 h2]

theorem wrong_share_ge (β Er Ew : ℝ) (hβ : 0 ≤ β) (h : Er ≤ Ew) :
    exp (-β * (Ew - Er)) / 2 ≤ share (-β * Er) (-β * Ew) := by
  unfold share
  have h1 : 0 < exp (-β * Er) := exp_pos _
  have h2 : 0 < exp (-β * Ew) := exp_pos _
  have hle : exp (-β * Ew) ≤ exp (-β * Er) := exp_le_exp.mpr (by nlinarith)
  rw [show -β * (Ew - Er) = -β * Ew - -β * Er by ring, exp_sub, le_div_iff₀ (by positivity)]
  rw [div_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_pos h2 h1]

theorem meme_eq_gene (τ ur uw : ℝ) :
    share (ur / τ) (uw / τ) = share (-(1 / τ) * (-ur)) (-(1 / τ) * (-uw)) := by
  unfold share; congr 1 <;> ring_nf

theorem meme_error_vanishes (Δ : ℝ) (hΔ : 0 < Δ) :
    Tendsto (fun τ : ℝ => exp (-(Δ / τ))) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun τ : ℝ => τ⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun τ : ℝ => -Δ * τ⁻¹) (𝓝[>] 0) atBot := h1.const_mul_atTop_of_neg (by linarith)
  have h3 := tendsto_exp_atBot.comp h2
  refine h3.congr (fun τ => ?_)
  simp [Function.comp, div_eq_mul_inv]

end GenesMemes
