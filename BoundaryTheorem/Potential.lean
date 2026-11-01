import Mathlib

/-!
# Part (C) of the Boundary Theorem: the potential theorem ("the complete self")

Source: `notes/BOOK_THEOREM.md` §1 box (C) and §2 proof of (C), as corrected in
`notes/BOOK_THEOREM_VERIFICATION.md` §2.3 and §4 (S ≠ ∅, d ≥ 2); detailed proof in
`notes/BOOK_THEOREM/fixed_points_dt.md` §4 (Theorem 2, (i) ⇔ (iv), and Theorem 2(d) for several rewards).

Notation, matching the note:
* `N` — the finite set of slots, `S : Finset N` the instances of the policy, `Sᶜ = E` the externals;
* `K` — the finite index set of rewards `R k` (the note's `k ≤ m`);
* `V` — policy space (the note's `ℝᵈ`), any finite-dimensional real normed space with `2 ≤ finrank ℝ V`;
* `embed S ξ θ` — the diagonal embedding `ι_ξ(θ)`: `θ` in every slot of `S`, the base state `ξ e` in each external;
* `field S ξ W R θ` — the mean field `F_W[R](θ) = Σ_{j,k} W_{jk} ∇_j R_k(ι_ξ(θ))`, written as a continuous linear
  functional (`fderiv` composed with the inclusion of slot `j`), so that no inner product is needed;
* `Conservative F` — `F` is a gradient field: `F θ` is the derivative of one function `φ : V → ℝ` at every `θ`.

Main results:
* `potential_iff` — for `S ≠ ∅` and `finrank ℝ V ≥ 2`, and any fixed external base states `ξ`:
  `F_W[R]` is conservative for every C² family `R` iff `W = (1_S, 0_E) cᵀ` for some `c : K → ℝ`.
* `potential_iff_forall_xi` — the same with `∀ ξ` on the left (the formulation in the task statement).
* `hasFDerivAt_kantian_potential` — under `W = (1_S, 0_E) cᵀ` the potential is `Σ_k c_k R_k ∘ ι_ξ`.
* `cdt_not_conservative` — non-vacuity: CDT (`W` = indicator of the actor slot) with a second instance has an
  explicit bilinear reward whose field is not conservative.
* `conservative_of_S_empty` — the hypothesis `S ≠ ∅` cannot be dropped (verifier's correction).
-/

open Finset

namespace BoundaryTheorem.Potential

set_option linter.unusedSectionVars false

variable {N K V : Type*} [Fintype N] [DecidableEq N] [Fintype K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## Definitions -/

/-- The diagonal embedding `ι_ξ(θ)`: slot `j ∈ S` (an instance) receives the policy `θ`, an external slot
`e ∉ S` receives its fixed base state `ξ e`. (The values of `ξ` on `S` are ignored.) -/
def embed (S : Finset N) (ξ : N → V) (θ : V) : N → V :=
  fun j => if j ∈ S then θ else ξ j

/-- Inclusion of slot `j`: `h ↦ (0, …, 0, h, 0, …, 0)` with `h` in slot `j`. Composing the derivative of a reward
with it gives the slot-`j` partial derivative `∇_j R`. -/
noncomputable abbrev slot (j : N) : V →L[ℝ] (N → V) :=
  ContinuousLinearMap.single ℝ (fun _ : N => V) j

/-- The mean field `F_W[R](θ) := Σ_{j,k} W_{jk} ∇_j R_k(ι_ξ(θ))` of the boundary `W : N → K → ℝ` on the reward
family `R`, as a continuous linear functional on `V` (the covector of the update direction). -/
noncomputable def field (S : Finset N) (ξ : N → V) (W : N → K → ℝ) (R : K → (N → V) → ℝ) (θ : V) :
    V →L[ℝ] ℝ :=
  ∑ j, ∑ k, W j k • (fderiv ℝ (R k) (embed S ξ θ)).comp (slot j)

/-- `F` is a gradient (conservative) field on all of `V`: there is a potential `φ` with `dφ(θ) = F θ` for all
`θ`. This is the note's "F_W[R] is a gradient field on ℝᵈ". -/
def Conservative (F : V → V →L[ℝ] ℝ) : Prop :=
  ∃ φ : V → ℝ, ∀ θ, HasFDerivAt φ (F θ) θ

/-- The Kantian (complete-self) form `W = (1_S, 0_E) cᵀ`: every instance weighted equally (per reward `k`), every
external weighted zero. -/
def IsKantian (S : Finset N) (W : N → K → ℝ) : Prop :=
  ∃ c : K → ℝ, ∀ j k, W j k = if j ∈ S then c k else 0

/-! ## Sufficiency: the chain rule -/

/-- The derivative of the embedding: `θ` is copied into each instance slot. -/
noncomputable def embedDeriv (S : Finset N) : V →L[ℝ] (N → V) :=
  ContinuousLinearMap.pi fun j => if j ∈ S then ContinuousLinearMap.id ℝ V else 0

theorem hasFDerivAt_embed (S : Finset N) (ξ : N → V) (θ : V) :
    HasFDerivAt (embed S ξ) (embedDeriv S : V →L[ℝ] (N → V)) θ := by
  rw [hasFDerivAt_pi']
  intro j
  by_cases hj : j ∈ S
  · simp only [embed, embedDeriv, hj, ite_true, ContinuousLinearMap.proj_pi]
    exact hasFDerivAt_id θ
  · simpa [embed, embedDeriv, hj] using hasFDerivAt_const (ξ j) θ

theorem comp_embedDeriv (S : Finset N) (D : (N → V) →L[ℝ] ℝ) :
    D.comp (embedDeriv S) = ∑ j ∈ S, D.comp (slot j) := by
  ext h
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, _root_.sum_apply]
  rw [← map_sum]
  congr 1
  ext i
  by_cases hi : i ∈ S <;> simp [embedDeriv, Finset.sum_apply, Pi.single_apply, hi]

/-- **(ii) ⇒ (i), with the potential.** If `W j k = (if j ∈ S then c k else 0)` and every `R k` is differentiable,
then `F_W[R]` is the derivative of `θ ↦ Σ_k c_k R_k(ι_ξ(θ))` at every `θ`. -/
theorem hasFDerivAt_kantian_potential (S : Finset N) (ξ : N → V) (c : K → ℝ) (R : K → (N → V) → ℝ)
    (hR : ∀ k, Differentiable ℝ (R k)) (θ : V) :
    HasFDerivAt (fun θ => ∑ k, c k * R k (embed S ξ θ))
      (field S ξ (fun j k => if j ∈ S then c k else 0) R θ) θ := by
  have h : HasFDerivAt (fun θ => ∑ k, c k * R k (embed S ξ θ))
      (∑ k, c k • (fderiv ℝ (R k) (embed S ξ θ)).comp (embedDeriv S)) θ := by
    apply HasFDerivAt.fun_sum
    intro k _
    exact ((hR k _).hasFDerivAt.comp θ (hasFDerivAt_embed S ξ θ)).const_mul (c k)
  convert h using 1
  simp only [field, comp_embedDeriv, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.smul_sum]

theorem conservative_of_isKantian (S : Finset N) (ξ : N → V) (W : N → K → ℝ) (hW : IsKantian S W)
    (R : K → (N → V) → ℝ) (hR : ∀ k, Differentiable ℝ (R k)) : Conservative (field S ξ W R) := by
  obtain ⟨c, hc⟩ := hW
  have : W = fun j k => if j ∈ S then c k else 0 := funext fun j => funext fun k => hc j k
  subst this
  exact ⟨_, hasFDerivAt_kantian_potential S ξ c R hR⟩

/-! ## Necessity: bilinear test rewards and symmetry of second derivatives -/

/-- The bilinear test reward `R(x) = α(x_i) · β(x_j)`: the coordinate form of the note's quadratic reward with the
single off-diagonal block `H_{ij} = B` (a rank-one, non-symmetric `B = α ⊗ β` when `α, β` are independent). -/
def bilin (i j : N) (α β : V →L[ℝ] ℝ) (x : N → V) : ℝ :=
  α (x i) * β (x j)

theorem contDiff_bilin (i j : N) (α β : V →L[ℝ] ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (bilin i j α β) :=
  ((α.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N => V) i)).contDiff).mul
    ((β.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N => V) j)).contDiff)

/-- The derivative of the bilinear test reward (product rule). -/
noncomputable def bilinDeriv (i j : N) (α β : V →L[ℝ] ℝ) (x : N → V) : (N → V) →L[ℝ] ℝ :=
  α (x i) • β.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N => V) j) +
    β (x j) • α.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N => V) i)

theorem hasFDerivAt_bilin (i j : N) (α β : V →L[ℝ] ℝ) (x : N → V) :
    HasFDerivAt (bilin i j α β) (bilinDeriv i j α β x) x := by
  have hi : HasFDerivAt (fun y : N → V => α (y i))
      (α.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N => V) i)) x :=
    (α.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N => V) i)).hasFDerivAt
  have hj : HasFDerivAt (fun y : N → V => β (y j))
      (β.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N => V) j)) x :=
    (β.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N => V) j)).hasFDerivAt
  exact hi.fun_mul hj

/-- The test family: the bilinear reward in reward slot `k₀`, all other rewards zero. -/
def testFamily [DecidableEq K] (k₀ : K) (i j : N) (α β : V →L[ℝ] ℝ) : K → (N → V) → ℝ :=
  fun k => if k = k₀ then bilin i j α β else 0

theorem contDiff_testFamily [DecidableEq K] (k₀ : K) (i j : N) (α β : V →L[ℝ] ℝ) {n : WithTop ℕ∞} (k : K) :
    ContDiff ℝ n (testFamily k₀ i j α β k) := by
  unfold testFamily
  split_ifs
  · exact contDiff_bilin i j α β
  · exact contDiff_const

/-- The field of the test family is explicit:
`F_W(θ) = W_{i k₀} β(ι(θ)_j) α + W_{j k₀} α(ι(θ)_i) β`. -/
theorem field_testFamily [DecidableEq K] (S : Finset N) (ξ : N → V) (W : N → K → ℝ) (k₀ : K) (i j : N)
    (α β : V →L[ℝ] ℝ) (θ : V) :
    field S ξ W (testFamily k₀ i j α β) θ =
      (W i k₀ * β (embed S ξ θ j)) • α + (W j k₀ * α (embed S ξ θ i)) • β := by
  have hD : ∀ k, fderiv ℝ (testFamily k₀ i j α β k) (embed S ξ θ) =
      if k = k₀ then bilinDeriv i j α β (embed S ξ θ) else 0 := by
    intro k
    by_cases hk : k = k₀
    · simp [testFamily, hk, (hasFDerivAt_bilin i j α β _).fderiv]
    · simp [testFamily, hk]
  have hk : ∀ j' : N, ∑ k, W j' k • (fderiv ℝ (testFamily k₀ i j α β k) (embed S ξ θ)).comp (slot j') =
      W j' k₀ • (bilinDeriv i j α β (embed S ξ θ)).comp (slot j') := by
    intro j'
    rw [Finset.sum_eq_single k₀]
    · simp [hD]
    · intro k _ hk
      simp [hD, hk]
    · simp
  simp only [field, hk]
  ext h
  simp [bilinDeriv, Pi.single_apply, apply_ite, Finset.sum_add_distrib]
  ring

/-- A gradient field has a symmetric derivative wherever it is differentiable (Mathlib's
`second_derivative_symmetric`, which needs only first derivatives of the potential). -/
theorem symm_of_conservative {F : V → V →L[ℝ] ℝ} (hF : Conservative F) {F' : V →L[ℝ] V →L[ℝ] ℝ} {θ : V}
    (h : HasFDerivAt F F' θ) (v w : V) : F' v w = F' w v := by
  obtain ⟨φ, hφ⟩ := hF
  exact second_derivative_symmetric hφ h v w

/-- In dimension `≥ 2` there are two functionals and two vectors in duality: `α u = 1, α v = 0, β u = 0, β v = 1`.
(The bilinear form `α ⊗ β` is then not symmetric.) -/
theorem exists_dualPair [FiniteDimensional ℝ V] (h2 : 2 ≤ Module.finrank ℝ V) :
    ∃ (α β : V →L[ℝ] ℝ) (u v : V), α u = 1 ∧ α v = 0 ∧ β u = 0 ∧ β v = 1 := by
  let b := Module.finBasis ℝ V
  let i0 : Fin (Module.finrank ℝ V) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank ℝ V) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  refine ⟨LinearMap.toContinuousLinearMap (b.coord i0), LinearMap.toContinuousLinearMap (b.coord i1),
    b i0, b i1, ?_, ?_, ?_, ?_⟩ <;>
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, h01, h01.symm]

/-- **Externals get zero weight.** If the field is conservative for the bilinear reward coupling an external slot
`e ∉ S` to an instance `s ∈ S` (in reward `k₀`), then `W e k₀ = 0`. -/
theorem weight_external_eq_zero [DecidableEq K] (S : Finset N) (ξ : N → V) (W : N → K → ℝ) (k₀ : K)
    {e s : N} (he : e ∉ S) (hs : s ∈ S) {α β : V →L[ℝ] ℝ} {u v : V}
    (hαu : α u = 1) (_hαv : α v = 0) (hβu : β u = 0) (hβv : β v = 1)
    (hC : Conservative (field S ξ W (testFamily k₀ e s α β))) : W e k₀ = 0 := by
  have hF : (field S ξ W (testFamily k₀ e s α β)) =
      fun θ => (W e k₀ • β.smulRight α) θ + (W s k₀ * α (ξ e)) • β := by
    funext θ
    rw [field_testFamily]
    ext w
    simp [embed, he, hs]
    ring
  have hder : ∀ θ, HasFDerivAt (field S ξ W (testFamily k₀ e s α β)) (W e k₀ • β.smulRight α) θ := by
    intro θ
    rw [hF]
    exact (W e k₀ • β.smulRight α).hasFDerivAt.add_const _
  have := symm_of_conservative hC (hder 0) v u
  simpa [hαu, hβu, hβv] using this

/-- **Instances get equal weight.** If the field is conservative for the bilinear reward coupling two instance
slots `s, t ∈ S` (in reward `k₀`), then `W s k₀ = W t k₀`. -/
theorem weight_instances_eq [DecidableEq K] (S : Finset N) (ξ : N → V) (W : N → K → ℝ) (k₀ : K)
    {s t : N} (hs : s ∈ S) (ht : t ∈ S) {α β : V →L[ℝ] ℝ} {u v : V}
    (hαu : α u = 1) (hαv : α v = 0) (hβu : β u = 0) (hβv : β v = 1)
    (hC : Conservative (field S ξ W (testFamily k₀ s t α β))) : W s k₀ = W t k₀ := by
  set F' : V →L[ℝ] V →L[ℝ] ℝ := W s k₀ • β.smulRight α + W t k₀ • α.smulRight β
  have hF : (field S ξ W (testFamily k₀ s t α β)) = fun θ => F' θ := by
    funext θ
    rw [field_testFamily]
    ext w
    simp [F', embed, hs, ht]
    ring
  have hder : HasFDerivAt (field S ξ W (testFamily k₀ s t α β)) F' 0 := by
    rw [hF]
    exact F'.hasFDerivAt
  have := symm_of_conservative hC hder v u
  simpa [F', hαu, hαv, hβu, hβv] using this

/-! ## The potential theorem -/

/-- **(i) ⇒ (ii).** If `S ≠ ∅`, `dim V ≥ 2`, and the field is conservative for every C² family, then `W` is
Kantian. Only bilinear (hence C^∞) test rewards are used. -/
theorem isKantian_of_forall_conservative [FiniteDimensional ℝ V] (S : Finset N) (hS : S.Nonempty)
    (h2 : 2 ≤ Module.finrank ℝ V) (ξ : N → V) (W : N → K → ℝ)
    (h : ∀ R : K → (N → V) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) → Conservative (field S ξ W R)) :
    IsKantian S W := by
  classical
  obtain ⟨α, β, u, v, hαu, hαv, hβu, hβv⟩ := exists_dualPair (V := V) h2
  obtain ⟨s₀, hs₀⟩ := hS
  refine ⟨fun k => W s₀ k, fun j k => ?_⟩
  by_cases hj : j ∈ S
  · simp only [hj, ite_true]
    exact weight_instances_eq S ξ W k hj hs₀ hαu hαv hβu hβv
      (h _ (contDiff_testFamily k j s₀ α β))
  · simp only [hj, ite_false]
    exact weight_external_eq_zero S ξ W k hj hs₀ hαu hαv hβu hβv
      (h _ (contDiff_testFamily k j s₀ α β))

/-- **Part (C), the potential theorem** (`BOOK_THEOREM.md` §1(C), corrected per `BOOK_THEOREM_VERIFICATION.md`
§4: `S ≠ ∅`, `d ≥ 2`). For a fixed choice of external base states `ξ`:
`F_W[R]` is a gradient field on `V` for every C² reward family `R` iff `W = (1_S, 0_E) cᵀ` for some `c`. -/
theorem potential_iff [FiniteDimensional ℝ V] (S : Finset N) (hS : S.Nonempty)
    (h2 : 2 ≤ Module.finrank ℝ V) (ξ : N → V) (W : N → K → ℝ) :
    (∀ R : K → (N → V) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) → Conservative (field S ξ W R)) ↔
      ∃ c : K → ℝ, ∀ j k, W j k = if j ∈ S then c k else 0 :=
  ⟨isKantian_of_forall_conservative S hS h2 ξ W, fun hW R hR =>
    conservative_of_isKantian S ξ W hW R fun k => (hR k).differentiable (by norm_num)⟩

/-- **Part (C)**, with the external base states also universally quantified (the formulation of the task brief).
-/
theorem potential_iff_forall_xi [FiniteDimensional ℝ V] (S : Finset N) (hS : S.Nonempty)
    (h2 : 2 ≤ Module.finrank ℝ V) (W : N → K → ℝ) :
    (∀ ξ : N → V, ∀ R : K → (N → V) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) → Conservative (field S ξ W R)) ↔
      ∃ c : K → ℝ, ∀ j k, W j k = if j ∈ S then c k else 0 :=
  ⟨fun h => (potential_iff S hS h2 0 W).1 (h 0), fun hW ξ => (potential_iff S hS h2 ξ W).2 hW⟩

/-! ## Sanity checks: non-vacuity and necessity of the hypotheses -/

/-- **Non-vacuity (CDT).** Let the actor `a` and a second instance `t ≠ a` both lie in `S`, and let `W` be the CDT
boundary (weight 1 on the actor slot, 0 elsewhere, in reward `k₀`). For the explicit reward
`R_{k₀}(x) = α(x_a) β(x_t)` (other rewards zero) with `α, β, u, v` in duality, the CDT field
`θ ↦ β(θ) α` is not conservative. For `V = ℝ²`, `α, β` the coordinates: `R(x) = x_{a,1} x_{t,2}` and
`F(θ) = (θ₂, 0)`, which has curl `−1`. -/
theorem cdt_not_conservative [DecidableEq K] (S : Finset N) (ξ : N → V) (k₀ : K) {a t : N}
    (ha : a ∈ S) (ht : t ∈ S) (hat : a ≠ t) {α β : V →L[ℝ] ℝ} {u v : V}
    (hαu : α u = 1) (hαv : α v = 0) (hβu : β u = 0) (hβv : β v = 1) :
    ¬ Conservative (field S ξ (fun j k => if j = a ∧ k = k₀ then 1 else 0) (testFamily k₀ a t α β)) := by
  intro hC
  have := weight_instances_eq S ξ _ k₀ ha ht hαu hαv hβu hβv hC
  simp [hat.symm] at this

/-- The CDT counterexample's field, written out: `F(θ) = β(θ) • α` (only the actor's partial derivative counts). -/
theorem cdt_field_eq [DecidableEq K] (S : Finset N) (ξ : N → V) (k₀ : K) {a t : N}
    (ht : t ∈ S) (hat : a ≠ t) (α β : V →L[ℝ] ℝ) (θ : V) :
    field S ξ (fun j k => if j = a ∧ k = k₀ then 1 else 0) (testFamily k₀ a t α β) θ = β θ • α := by
  rw [field_testFamily]
  simp [embed, ht, hat.symm]

/-- The CDT counterexample in coordinates, `V = Fin 2 → ℝ`, `R(x) = x_{a,0} · x_{t,1}`. -/
theorem cdt_not_conservative_fin2 [DecidableEq K] (S : Finset N) (ξ : N → (Fin 2 → ℝ)) (k₀ : K) {a t : N}
    (ha : a ∈ S) (ht : t ∈ S) (hat : a ≠ t) :
    ¬ Conservative (field S ξ (fun j k => if j = a ∧ k = k₀ then 1 else 0)
      (testFamily k₀ a t (ContinuousLinearMap.proj 0) (ContinuousLinearMap.proj 1))) :=
  cdt_not_conservative S ξ k₀ ha ht hat (u := Pi.single 0 1) (v := Pi.single 1 1)
    (by simp) (by simp) (by simp) (by simp)

/-- **The hypothesis `S ≠ ∅` is needed** (verifier's correction to the box). With no instance slot the field does not
depend on `θ`, so it is conservative for every `W` and every differentiable family — including non-Kantian `W`
(any nonzero weight on an external). -/
theorem conservative_of_S_empty (ξ : N → V) (W : N → K → ℝ) (R : K → (N → V) → ℝ) :
    Conservative (field (∅ : Finset N) ξ W R) := by
  have hconst : ∀ θ, field (∅ : Finset N) ξ W R θ = field (∅ : Finset N) ξ W R 0 := by
    intro θ
    have : embed (∅ : Finset N) ξ θ = embed (∅ : Finset N) ξ 0 := by funext j; simp [embed]
    simp [field, this]
  exact ⟨fun θ => field (∅ : Finset N) ξ W R 0 θ, fun θ => by
    rw [hconst θ]; exact (field (∅ : Finset N) ξ W R 0).hasFDerivAt⟩

/-- Continuity of the field in `θ` for a C¹ family. -/
theorem continuous_field (S : Finset N) (ξ : N → V) (W : N → K → ℝ) (R : K → (N → V) → ℝ)
    (hR : ∀ k, ContDiff ℝ 1 (R k)) : Continuous (field S ξ W R) := by
  have hemb : Continuous (embed S ξ) := by
    refine continuous_pi fun j => ?_
    by_cases hj : j ∈ S
    · simp only [embed, hj, ite_true]
      exact continuous_id
    · simpa [embed, hj] using continuous_const
  unfold field
  refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
  exact (((((hR k).continuous_fderiv (by norm_num)).comp hemb).clm_comp
    (continuous_const (y := slot j))).const_smul (W j k) :)

/-- **The hypothesis `d ≥ 2` is needed.** On a line (`V = ℝ`) every continuous field is a gradient (fundamental
theorem of calculus), so `F_W[R]` is conservative for every `W` and every C¹ family. -/
theorem conservative_dim_one (S : Finset N) (ξ : N → ℝ) (W : N → K → ℝ) (R : K → (N → ℝ) → ℝ)
    (hR : ∀ k, ContDiff ℝ 1 (R k)) : Conservative (field S ξ W R) := by
  have hc : Continuous fun θ => field S ξ W R θ 1 :=
    (continuous_field S ξ W R hR).clm_apply continuous_const
  refine ⟨fun θ => ∫ t in (0 : ℝ)..θ, field S ξ W R t 1, fun θ => ?_⟩
  have h := (hc.integral_hasStrictDerivAt 0 θ).hasDerivAt.hasFDerivAt
  convert h using 1
  ext
  simp

/-- Consequently, for `d = 1` the "only if" of `potential_iff` fails as soon as there is an external slot: weight 1
on an external `e ∉ S` (not Kantian) still gives a conservative field for every C² family. -/
theorem not_isKantian_but_conservative_dim_one [Nonempty K] (S : Finset N) {e : N} (he : e ∉ S) (ξ : N → ℝ) :
    ¬ IsKantian S (fun j (_ : K) => if j = e then (1 : ℝ) else 0) ∧
      ∀ R : K → (N → ℝ) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) →
        Conservative (field S ξ (fun j (_ : K) => if j = e then (1 : ℝ) else 0) R) := by
  refine ⟨fun ⟨c, hc⟩ => ?_, fun R hR => conservative_dim_one S ξ _ R fun k => (hR k).of_le (by norm_num)⟩
  obtain ⟨k⟩ := ‹Nonempty K›
  have := hc e k
  simp [he] at this

end BoundaryTheorem.Potential
