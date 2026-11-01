import BoundaryTheorem.Causal
open BoundaryTheorem.Causal BoundaryTheorem.Potential

/-! Critic sanity checks: instantiate the main theorems on concrete types so none is vacuous. -/

-- dim (Fin 2 → ℝ) = 2
theorem two_le : 2 ≤ Module.finrank ℝ (Fin 2 → ℝ) := by simp

-- (3) linear_iff on N = Fin 2 slots, K = Unit, V = ℝ², r = (1, 1/2) (self + a partial reader).
example (b : Fin 2 → Fin 2 → ℝ) (a : Fin 2 → Unit → ℝ) :
    (∀ R : Unit → (Fin 2 → Fin 2 → ℝ) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) →
        Conservative (causalField (linResp ![1, 1/2] b) (scalarA a) R)) ↔
      ∃ c : Unit → ℝ, ∀ j k, a j k = c k * (![1, 1/2] : Fin 2 → ℝ) j :=
  linear_iff two_le _ ⟨0, by simp⟩ b a

-- Kantian side satisfied: credits (c, c/2) pass the universal conservativity for every C² family.
example (b : Fin 2 → Fin 2 → ℝ) (c : ℝ) :
    ∀ R : Unit → (Fin 2 → Fin 2 → ℝ) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) →
        Conservative (causalField (linResp ![1, 1/2] b) (scalarA fun j _ => c * (![1, 1/2] : Fin 2 → ℝ) j) R) :=
  (linear_iff two_le _ ⟨0, by simp⟩ b _).2 ⟨fun _ => c, fun _ _ => rfl⟩

-- Homo moralis falsified: r = (1,1), credits (1, κ) with κ ≠ 1, explicit reward x_{0,0} x_{1,1}.
example (b : Fin 2 → Fin 2 → ℝ) (κ : ℝ) (hκ : κ ≠ 1) :
    ¬ Conservative (causalField (linResp ![1, 1] b) (scalarA fun j _ => (![1, κ] : Fin 2 → ℝ) j)
      (testFamily () 0 1 (ContinuousLinearMap.proj 0) (ContinuousLinearMap.proj 1))) :=
  homoMoralis_not_conservative_fin2 (s := 0) (t := 1) _ b _ () (by simp) (by simp) (by simpa using hκ)

-- Hence homo moralis fails the LHS of linear_iff, and so (by the iff) is not of the form c k * r j.
example (b : Fin 2 → Fin 2 → ℝ) (κ : ℝ) (hκ : κ ≠ 1) :
    ¬ ∃ c : Unit → ℝ, ∀ j k, (fun j _ => (![1, κ] : Fin 2 → ℝ) j) j k = c k * (![1, 1] : Fin 2 → ℝ) j := by
  intro h
  have := (linear_iff two_le ![1, 1] ⟨0, by simp⟩ b (fun j _ => (![1, κ] : Fin 2 → ℝ) j)).2 h
    _ (contDiff_testFamily () 0 1 (ContinuousLinearMap.proj 0) (ContinuousLinearMap.proj 1))
  exact homoMoralis_not_conservative_fin2 (s := 0) (t := 1) _ b _ () (by simp) (by simp) (by simpa using hκ) this

-- Necessity of dim ≥ 2 with `∃ j, r j ≠ 0` HOLDING: V = ℝ, r = (1, 0), credit 1 on the non-responding slot.
example (b : Fin 2 → ℝ) :
    (∃ j, (![1, 0] : Fin 2 → ℝ) j ≠ 0) ∧
    ¬ (∃ c : Unit → ℝ, ∀ j k, (fun _ _ => (1 : ℝ)) j k = c k * (![1, 0] : Fin 2 → ℝ) j) ∧
      ∀ R : Unit → (Fin 2 → ℝ) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) →
        Conservative (causalField (linResp ![1, 0] b) (scalarA fun _ _ => (1 : ℝ)) R) :=
  ⟨⟨0, by simp⟩, not_kantian_but_conservative_dim_one (k := ()) ![1, 0] b (fun _ _ => 1) (e := 1) (by simp) one_ne_zero⟩

-- Necessity of ∃ j, r j ≠ 0 with dim ≥ 2 HOLDING: V = ℝ², r ≡ 0, credit 1.
example (b : Fin 1 → Fin 2 → ℝ) :
    ¬ (∃ c : Unit → ℝ, ∀ j k, (fun _ _ => (1 : ℝ)) j k = c k * (fun _ : Fin 1 => (0 : ℝ)) j) ∧
      ∀ R : Unit → (Fin 1 → Fin 2 → ℝ) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) →
        Conservative (causalField (linResp (fun _ => 0) b) (scalarA fun _ _ => (1 : ℝ)) R) :=
  not_kantian_but_conservative_r_zero (k := ()) b (fun _ _ => 1) (e := 0) one_ne_zero

-- (4a) potential_iff_of_causal has literally the statement of potential_iff.
example [Fintype N] [DecidableEq N] [Fintype K] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (S : Finset N) (hS : S.Nonempty) (h2 : 2 ≤ Module.finrank ℝ V)
    (ξ : N → V) (W : N → K → ℝ) :
    ((∀ R : K → (N → V) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) → Conservative (field S ξ W R)) ↔
      ∃ c : K → ℝ, ∀ j k, W j k = if j ∈ S then c k else 0) :=
  potential_iff_of_causal S hS h2 ξ W

example [Fintype N] [DecidableEq N] [Fintype K] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (S : Finset N) (hS : S.Nonempty) (h2 : 2 ≤ Module.finrank ℝ V)
    (ξ : N → V) (W : N → K → ℝ) :
    potential_iff_of_causal S hS h2 ξ W = potential_iff S hS h2 ξ W := rfl  -- proof irrelevance: same Prop

-- (2) sufficiency with a genuinely nonlinear g: g 0 θ = θ, g 1 θ = ‖θ‖² • θ  (V = ℝ² as EuclideanSpace is overkill; use a smooth map)
noncomputable def gNL : Fin 2 → (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
  ![fun θ => θ, fun θ => (θ 0 * θ 1) • θ]

theorem gNL_diff : ∀ j, Differentiable ℝ (gNL j) := by
  intro j
  fin_cases j
  · simp [gNL]
  · show Differentiable ℝ (fun θ : Fin 2 → ℝ => (θ 0 * θ 1) • θ)
    fun_prop

example (R : Unit → (Fin 2 → Fin 2 → ℝ) → ℝ) (hR : ∀ k, Differentiable ℝ (R k)) (c : Unit → ℝ) (θ : Fin 2 → ℝ) :
    HasFDerivAt (fun θ => ∑ k, c k * R k (state gNL θ))
      (causalField gNL (fun j k θ => c k • fderiv ℝ (gNL j) θ) R θ) θ :=
  hasFDerivAt_causal_potential gNL _ R c (fun _ _ _ => rfl) gNL_diff hR θ
