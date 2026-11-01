import Mathlib

/-!
# S3_heatbath: the heat-bath / Gibbs update is reversible

General finite setting: `Ω` finite, `π : Ω → ℝ` positive, `key : Ω → K`.
Configurations with equal key form a fiber (= "agree off the updated site").
The heat-bath kernel resamples inside the fiber proportionally to `π`.

## What is proved
* `row_sum`: each row of `kernel` sums to 1 (needs `π > 0`).
* `detailed_balance`: `π x K(x,y) = π y K(y,x)` for *every* `π` (no positivity needed).
* `stationary`: `Σ_x π x K(x,y) = π y` (derived from the two above).
* Ising instantiation on `Fin n → Bool` with normalized `gibbs β E ∝ exp(-β E)` for an
  arbitrary energy `E` and any real `β`; `siteKey i` forgets spin `i`. We prove the fiber is
  exactly `{σ[i↦true], σ[i↦false]}` and the explicit Glauber formula `ising_kernel_update`,
  then specialize (1)-(3).
* Going up (added by the second agent): `sweep_stochastic_stationary` shows that a composition
  (matrix product) of stochastic kernels that each leave `π` stationary is again stochastic and
  leaves `π` stationary. `heatbath_sweep_stationary` and `ising_sweep_stationary`
  (systematic scan over any list of sites, repeats allowed) are its corollaries. A sweep is
  *not* claimed to be reversible, and in general it is not.
* Concrete `example`s at the end check that the theorems are not vacuous: `π = (1,3)` on `Bool` gives
  `K(false,true) = 1/4`; distinct keys give `0`; one Ising spin at `β = 0` lands on `true` w.p. `1/2`.

## What is interpreted (not formalized)
* "Single-site update at site `i`" is modelled by `siteKey i`; the kernel is a bare function
  `Ω → Ω → ℝ`, not a Mathlib `Kernel`/`PMF`; no claim about convergence/ergodicity
  (irreducibility of a full sweep), reversibility of sweeps, or any connection to attention masks is made here.
-/

open Finset

namespace HeatBath

variable {Ω K : Type*} [Fintype Ω] [DecidableEq K]

/-- Total `π`-mass of the fiber containing `x`. -/
noncomputable def fiberMass (π : Ω → ℝ) (key : Ω → K) (x : Ω) : ℝ :=
  ∑ z ∈ univ.filter (fun z => key z = key x), π z

/-- Heat-bath kernel: `K(x,y) = π y / Σ_{key z = key x} π z` if `key y = key x`, else `0`. -/
noncomputable def kernel (π : Ω → ℝ) (key : Ω → K) (x y : Ω) : ℝ :=
  if key y = key x then π y / fiberMass π key x else 0

theorem fiberMass_pos (π : Ω → ℝ) (key : Ω → K) (hπ : ∀ x, 0 < π x) (x : Ω) :
    0 < fiberMass π key x := by
  unfold fiberMass
  exact Finset.sum_pos (fun z _ => hπ z) ⟨x, by simp⟩

theorem kernel_nonneg (π : Ω → ℝ) (key : Ω → K) (hπ : ∀ x, 0 < π x) (x y : Ω) :
    0 ≤ kernel π key x y := by
  unfold kernel
  split_ifs
  · exact div_nonneg (hπ y).le (fiberMass_pos π key hπ x).le
  · exact le_rfl

/-- (1) Each row of the heat-bath kernel sums to 1. -/
theorem row_sum (π : Ω → ℝ) (key : Ω → K) (hπ : ∀ x, 0 < π x) (x : Ω) :
    ∑ y, kernel π key x y = 1 := by
  unfold kernel
  rw [← Finset.sum_filter, ← Finset.sum_div]
  exact div_self (fiberMass_pos π key hπ x).ne'

/-- (2) Detailed balance (holds for any `π`, positivity not needed). -/
theorem detailed_balance (π : Ω → ℝ) (key : Ω → K) (x y : Ω) :
    π x * kernel π key x y = π y * kernel π key y x := by
  unfold kernel
  split_ifs with h1 h2 h2
  · have hM : fiberMass π key x = fiberMass π key y := by
      unfold fiberMass; rw [h1]
    rw [hM]
    ring
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · ring

/-- (3) Stationarity of `π`. -/
theorem stationary (π : Ω → ℝ) (key : Ω → K) (hπ : ∀ x, 0 < π x) (y : Ω) :
    ∑ x, π x * kernel π key x y = π y := by
  simp_rw [detailed_balance π key _ y]
  rw [← Finset.mul_sum, row_sum π key hπ y, mul_one]

/-! ## Going up: sweeps (compositions of heat-bath updates) preserve `π`.
Each single-site kernel is reversible; a sweep `K₁ K₂ ⋯ Kₘ` is in general *not* reversible
(only palindromic sweeps are), but it is still a stochastic matrix with `π` stationary. -/

/-- Matrix product of two kernels. -/
noncomputable def comp (P Q : Ω → Ω → ℝ) (x z : Ω) : ℝ := ∑ y, P x y * Q y z

/-- Identity kernel. -/
noncomputable def idK [DecidableEq Ω] (x y : Ω) : ℝ := if x = y then 1 else 0

/-- The sweep kernel `P₁ P₂ ⋯ Pₘ` (applied left to right). -/
noncomputable def sweep [DecidableEq Ω] (Ps : List (Ω → Ω → ℝ)) : Ω → Ω → ℝ :=
  Ps.foldr comp idK

/-- If every kernel in the list is stochastic and leaves `π` stationary, so does the sweep. -/
theorem sweep_stochastic_stationary [DecidableEq Ω] (π : Ω → ℝ) (Ps : List (Ω → Ω → ℝ))
    (hrow : ∀ P ∈ Ps, ∀ x, ∑ y, P x y = 1)
    (hstat : ∀ P ∈ Ps, ∀ y, ∑ x, π x * P x y = π y) :
    (∀ x, ∑ y, sweep Ps x y = 1) ∧ (∀ y, ∑ x, π x * sweep Ps x y = π y) := by
  induction Ps with
  | nil => exact ⟨fun x => by simp [sweep, idK], fun y => by simp [sweep, idK]⟩
  | cons P Ps ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun Q hQ => hrow Q (List.mem_cons_of_mem _ hQ))
      (fun Q hQ => hstat Q (List.mem_cons_of_mem _ hQ))
    have hP1 := hrow P List.mem_cons_self
    have hP2 := hstat P List.mem_cons_self
    have hs : sweep (P :: Ps) = comp P (sweep Ps) := rfl
    rw [hs]
    refine ⟨fun x => ?_, fun z => ?_⟩
    · calc ∑ y, comp P (sweep Ps) x y = ∑ w, P x w * ∑ y, sweep Ps w y := by
            unfold comp; rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
        _ = 1 := by simp_rw [ih1, mul_one]; exact hP1 x
    · calc ∑ x, π x * comp P (sweep Ps) x z = ∑ w, (∑ x, π x * P x w) * sweep Ps w z := by
            unfold comp; simp_rw [Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
            exact Finset.sum_comm
        _ = π z := by simp_rw [hP2]; exact ih2 z

/-- For `π > 0`, any heat-bath sweep (a list of keys on a common key type) leaves `π` stationary. -/
theorem heatbath_sweep_stationary [DecidableEq Ω] (π : Ω → ℝ) (hπ : ∀ x, 0 < π x)
    (keys : List (Ω → K)) (y : Ω) :
    ∑ x, π x * sweep (keys.map (kernel π)) x y = π y := by
  refine (sweep_stochastic_stationary π _ ?_ ?_).2 y
  · intro P hP; obtain ⟨k, -, rfl⟩ := List.mem_map.1 hP; exact row_sum π k hπ
  · intro P hP; obtain ⟨k, -, rfl⟩ := List.mem_map.1 hP; exact stationary π k hπ

/-! ## Ising instantiation: spins `Fin n → Bool`, arbitrary energy `E`, inverse temperature `β`. -/

section Ising

variable {n : ℕ}

/-- Partition function. -/
noncomputable def partition (β : ℝ) (E : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ σ, Real.exp (-β * E σ)

/-- Normalized Gibbs distribution `π ∝ exp(-β E)`. -/
noncomputable def gibbs (β : ℝ) (E : (Fin n → Bool) → ℝ) (σ : Fin n → Bool) : ℝ :=
  Real.exp (-β * E σ) / partition β E

/-- Key for the single-site update at `i`: the configuration restricted to sites `≠ i`. -/
def siteKey (i : Fin n) (σ : Fin n → Bool) : {j : Fin n // j ≠ i} → Bool :=
  fun j => σ j.1

theorem gibbs_pos (β : ℝ) (E : (Fin n → Bool) → ℝ) (σ : Fin n → Bool) :
    0 < gibbs β E σ := by
  unfold gibbs partition
  exact div_pos (Real.exp_pos _)
    (Finset.sum_pos (fun τ _ => Real.exp_pos _) Finset.univ_nonempty)

theorem gibbs_sum (β : ℝ) (E : (Fin n → Bool) → ℝ) :
    ∑ σ, gibbs β E σ = 1 := by
  unfold gibbs
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun τ _ => Real.exp_pos _) Finset.univ_nonempty).ne'

/-- The fiber of `siteKey i` through `σ` is exactly `{σ[i↦true], σ[i↦false]}`. -/
theorem siteKey_eq_iff (i : Fin n) (σ τ : Fin n → Bool) :
    siteKey i τ = siteKey i σ ↔ ∃ b : Bool, τ = Function.update σ i b := by
  constructor
  · intro h
    refine ⟨τ i, ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj]
      exact congrFun h ⟨j, hj⟩
  · rintro ⟨b, rfl⟩
    funext j
    simp [siteKey, Function.update_of_ne j.2]

/-- Explicit single-site heat-bath (Glauber) probabilities. -/
theorem ising_kernel_update (β : ℝ) (E : (Fin n → Bool) → ℝ) (i : Fin n)
    (σ : Fin n → Bool) (b : Bool) :
    kernel (gibbs β E) (siteKey i) σ (Function.update σ i b) =
      Real.exp (-β * E (Function.update σ i b)) /
        (Real.exp (-β * E (Function.update σ i true)) +
          Real.exp (-β * E (Function.update σ i false))) := by
  have hkey : siteKey i (Function.update σ i b) = siteKey i σ :=
    (siteKey_eq_iff i σ _).2 ⟨b, rfl⟩
  have hne : Function.update σ i true ≠ Function.update σ i false := by
    intro h
    have := congrFun h i
    simp at this
  have hfib : univ.filter (fun z => siteKey i z = siteKey i σ) =
      {Function.update σ i true, Function.update σ i false} := by
    ext τ
    simp only [mem_filter, mem_univ, true_and, siteKey_eq_iff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      cases c <;> simp
    · rintro (h | h)
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
  have hZ : partition β E ≠ 0 :=
    (Finset.sum_pos (fun τ _ => Real.exp_pos _) Finset.univ_nonempty).ne'
  unfold kernel fiberMass
  simp only [hkey, ↓reduceIte]
  rw [hfib, Finset.sum_pair hne]
  unfold gibbs
  rw [← add_div, div_div_div_cancel_right₀ hZ]

theorem ising_row_sum (β : ℝ) (E : (Fin n → Bool) → ℝ) (i : Fin n) (σ : Fin n → Bool) :
    ∑ τ, kernel (gibbs β E) (siteKey i) σ τ = 1 :=
  row_sum _ _ (gibbs_pos β E) σ

theorem ising_detailed_balance (β : ℝ) (E : (Fin n → Bool) → ℝ) (i : Fin n)
    (σ τ : Fin n → Bool) :
    gibbs β E σ * kernel (gibbs β E) (siteKey i) σ τ =
      gibbs β E τ * kernel (gibbs β E) (siteKey i) τ σ :=
  detailed_balance _ _ σ τ

theorem ising_stationary (β : ℝ) (E : (Fin n → Bool) → ℝ) (i : Fin n) (τ : Fin n → Bool) :
    ∑ σ, gibbs β E σ * kernel (gibbs β E) (siteKey i) σ τ = gibbs β E τ :=
  stationary _ _ (gibbs_pos β E) τ

/-- Going up, Ising: a systematic-scan sweep over any list of sites (repeats allowed; site keys
live in different types, so this goes through `sweep_stochastic_stationary`) preserves Gibbs. -/
theorem ising_sweep_stationary (β : ℝ) (E : (Fin n → Bool) → ℝ) (sites : List (Fin n))
    (τ : Fin n → Bool) :
    ∑ σ, gibbs β E σ * sweep (sites.map fun i => kernel (gibbs β E) (siteKey i)) σ τ =
      gibbs β E τ := by
  refine (sweep_stochastic_stationary (gibbs β E) _ ?_ ?_).2 τ
  · intro P hP; obtain ⟨i, -, rfl⟩ := List.mem_map.1 hP; exact ising_row_sum β E i
  · intro P hP; obtain ⟨i, -, rfl⟩ := List.mem_map.1 hP; exact ising_stationary β E i

end Ising

/-! ## Concrete sanity checks (non-vacuity). -/

/-- Two states, one fiber, `π = (1, 3)`: the heat-bath kernel jumps to `true` w.p. `1/4`. -/
example : kernel (fun b : Bool => if b then (1:ℝ) else 3) (fun _ => ()) false true = 1/4 := by
  simp [kernel, fiberMass]; norm_num

/-- Concrete detailed balance instance: `3 · K(false,true) = 1 · K(true,false)` (= 3/4). -/
example : (3:ℝ) * kernel (fun b : Bool => if b then (1:ℝ) else 3) (fun _ => ()) false true
    = 1 * kernel (fun b : Bool => if b then (1:ℝ) else 3) (fun _ => ()) true false :=
  detailed_balance (fun b : Bool => if b then (1:ℝ) else 3) (fun _ => ()) false true

/-- Different keys never mix: with `key = id` the kernel is the identity. -/
example : kernel (fun b : Bool => if b then (1:ℝ) else 3) id false true = 0 := by
  simp [kernel]

/-- One-spin Ising at `β = 0` with any `E`: the probability of landing on `true` is exactly `1/2`. -/
example (E : (Fin 1 → Bool) → ℝ) (σ : Fin 1 → Bool) :
    kernel (gibbs 0 E) (siteKey 0) σ (Function.update σ 0 true) = 1/2 := by
  rw [ising_kernel_update]; simp; norm_num

end HeatBath
