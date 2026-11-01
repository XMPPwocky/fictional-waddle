import Mathlib

/-!
# Part (A) of the Boundary Theorem: the pairing identity

Formalises `notes/BOOK_THEOREM.md` §1 (A) / §2 (A), in the corrected form of
`notes/BOOK_THEOREM_VERIFICATION.md` §4, on a **finite probability space with strictly positive
weights**.  (Discarding null atoms loses nothing for the quantities involved — expectations,
covariances, conditional expectations given `g` — so "a.s." in the note becomes "everywhere" here.)
See `lean/FIDELITY_pairing.md` for the statement-by-statement comparison.

Notation of the note ↔ Lean:

* dice `(Ω, P)`                       ↔ `Ω` with `[Fintype Ω]`, `μ : FinProb Ω` (weights `μ.p`)
* `E f`, `Cov(f, h)`                  ↔ `μ.E f`, `μ.cov f h`
* `E[f | g]` (conditional expectation given the σ-field of `g`) ↔ `μ.condE g f`
* "`f` is `g`-measurable"             ↔ `Function.FactorsThrough f g`
* regressors `H_k ∈ L²(Ω; ℝᵈ)`         ↔ `H : K → Ω → D → ℝ`
* genotypes `g_j ∈ L²(Ω; ℝ^q)`         ↔ `g : I → Ω → ℝ` with `I = J × Q` flattened
  (the note's `Γ_{jk} β_{jk}` with `Γ_{jk} ∈ ℝ^{d×q}`, `β_{jk} ∈ ℝ^q` is the sum over the
  `q` components, so a flat index `I` is the same object); the vector genotype is `vec g : Ω → I → ℝ`
* rewards `R_k ∈ L²(Ω)`, baselines `b_k` ↔ `R b : K → Ω → ℝ`
* the scheme `ĝ = Σ_k H_k (R_k − b_k)` ↔ `update H R b`
* effective regressors `H̃_l = H_l − Σ_k B_{kl} H_k` ↔ `Htilde H B`
* design `Γ_{jk} = Cov(H̃_k, g_j)`       ↔ `Gamma μ H g k i α`
* normal equations `Cov(g) β_{·k} = Cov(g, R_k)` ↔ `IsLSQ μ g R β`
* `R_k = α_k + β_{·k}ᵀ g + e_k`           ↔ `e_k = resid μ g R β`
* `ζ_k = E[H̃_k | g] − P H̃_k`             ↔ `zeta μ g H Λ`
-/

namespace BoundaryTheorem.Pairing

open Finset

/-- A finite probability space on the finite type `Ω` with strictly positive weights `p`
(the dice `(Ω, P)` of the note, with null atoms discarded). -/
structure FinProb (Ω : Type*) [Fintype Ω] where
  /-- the probability of the atom `ω` -/
  p : Ω → ℝ
  pos : ∀ ω, 0 < p ω
  sum_one : ∑ ω, p ω = 1

namespace FinProb

variable {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)

/-- Expectation `E f = Σ_ω P(ω) f(ω)`. -/
def E (f : Ω → ℝ) : ℝ := ∑ ω, μ.p ω * f ω

/-- Covariance `Cov(f, h) = E[f h] − E f · E h`. -/
def cov (f h : Ω → ℝ) : ℝ := μ.E (fun ω => f ω * h ω) - μ.E f * μ.E h

/-! ### Elementary facts about `E` and `cov` -/

lemma E_const (c : ℝ) : μ.E (fun _ => c) = c := by
  simp [E, ← Finset.sum_mul, μ.sum_one]

lemma E_add (f h : Ω → ℝ) : μ.E (fun ω => f ω + h ω) = μ.E f + μ.E h := by
  simp [E, mul_add, Finset.sum_add_distrib]

lemma E_sub (f h : Ω → ℝ) : μ.E (fun ω => f ω - h ω) = μ.E f - μ.E h := by
  simp [E, mul_sub, Finset.sum_sub_distrib]

lemma E_const_mul (c : ℝ) (f : Ω → ℝ) : μ.E (fun ω => c * f ω) = c * μ.E f := by
  simp [E, Finset.mul_sum, mul_left_comm]

lemma E_mul_const (c : ℝ) (f : Ω → ℝ) : μ.E (fun ω => f ω * c) = μ.E f * c := by
  simp [E, Finset.sum_mul, mul_assoc]

lemma E_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.E (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, μ.E (f i) := by
  simp only [E, Finset.mul_sum]
  exact Finset.sum_comm

lemma E_neg (f : Ω → ℝ) : μ.E (fun ω => -f ω) = -μ.E f := by
  simp [E, Finset.sum_neg_distrib]

lemma E_zero : μ.E (fun _ => 0) = 0 := by simp [E]

/-- `E[(f − E f)(h − E h)] = Cov(f, h)`. -/
lemma cov_eq_E_centered (f h : Ω → ℝ) :
    μ.cov f h = μ.E (fun ω => (f ω - μ.E f) * (h ω - μ.E h)) := by
  have : (fun ω => (f ω - μ.E f) * (h ω - μ.E h)) =
      fun ω => f ω * h ω - μ.E f * h ω - (f ω * μ.E h - μ.E f * μ.E h) := by
    funext ω; ring
  rw [this]
  simp only [E_sub, E_const_mul, E_mul_const, E_const, cov]; ring

lemma cov_comm (f h : Ω → ℝ) : μ.cov f h = μ.cov h f := by
  simp [cov, mul_comm]

lemma cov_add_right (f h₁ h₂ : Ω → ℝ) :
    μ.cov f (fun ω => h₁ ω + h₂ ω) = μ.cov f h₁ + μ.cov f h₂ := by
  simp only [cov, mul_add, E_add]; ring

lemma cov_sub_right (f h₁ h₂ : Ω → ℝ) :
    μ.cov f (fun ω => h₁ ω - h₂ ω) = μ.cov f h₁ - μ.cov f h₂ := by
  simp only [cov, mul_sub, E_sub]; ring

lemma cov_const_right (f : Ω → ℝ) (c : ℝ) : μ.cov f (fun _ => c) = 0 := by
  simp [cov, E_mul_const, E_const]

lemma cov_const_mul_right (f h : Ω → ℝ) (c : ℝ) :
    μ.cov f (fun ω => c * h ω) = c * μ.cov f h := by
  have : (fun ω => f ω * (c * h ω)) = fun ω => c * (f ω * h ω) := by funext ω; ring
  simp only [cov, this, E_const_mul]; ring

lemma cov_sum_right {ι : Type*} (s : Finset ι) (f : Ω → ℝ) (h : ι → Ω → ℝ) :
    μ.cov f (fun ω => ∑ i ∈ s, h i ω) = ∑ i ∈ s, μ.cov f (h i) := by
  simp only [cov, Finset.mul_sum, E_sum, Finset.sum_sub_distrib]

lemma cov_add_left (f₁ f₂ h : Ω → ℝ) :
    μ.cov (fun ω => f₁ ω + f₂ ω) h = μ.cov f₁ h + μ.cov f₂ h := by
  rw [cov_comm, cov_add_right, cov_comm, cov_comm μ f₂]

lemma cov_sub_left (f₁ f₂ h : Ω → ℝ) :
    μ.cov (fun ω => f₁ ω - f₂ ω) h = μ.cov f₁ h - μ.cov f₂ h := by
  rw [cov_comm, cov_sub_right, cov_comm, cov_comm μ f₂]

lemma cov_const_left (c : ℝ) (h : Ω → ℝ) : μ.cov (fun _ => c) h = 0 := by
  rw [cov_comm, cov_const_right]

lemma cov_const_mul_left (c : ℝ) (f h : Ω → ℝ) :
    μ.cov (fun ω => c * f ω) h = c * μ.cov f h := by
  rw [cov_comm, cov_const_mul_right, cov_comm]

lemma cov_sum_left {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) (h : Ω → ℝ) :
    μ.cov (fun ω => ∑ i ∈ s, f i ω) h = ∑ i ∈ s, μ.cov (f i) h := by
  rw [cov_comm, cov_sum_right]; simp_rw [cov_comm μ h]

/-- `E[f h] = Cov(f, h)` when `E f = 0`. -/
lemma E_mul_eq_cov_of_E_eq_zero (f h : Ω → ℝ) (hf : μ.E f = 0) :
    μ.E (fun ω => f ω * h ω) = μ.cov f h := by
  simp [cov, hf]

/-- Zero variance forces constancy (this is where strict positivity of the weights is used). -/
lemma eq_E_of_cov_self_eq_zero (f : Ω → ℝ) (h : μ.cov f f = 0) : ∀ ω, f ω = μ.E f := by
  rw [cov_eq_E_centered] at h
  unfold E at h
  have hnn : ∀ ω ∈ (Finset.univ : Finset Ω),
      0 ≤ μ.p ω * ((f ω - μ.E f) * (f ω - μ.E f)) := fun ω _ =>
    mul_nonneg (μ.pos ω).le (mul_self_nonneg _)
  intro ω
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h ω (Finset.mem_univ _)
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 (μ.pos ω).ne'
  · exact sub_eq_zero.1 (mul_self_eq_zero.1 h1)

/-! ### Conditional expectation given a statistic `g`

On a finite space, `E[f | g](ω)` is the `P`-average of `f` over the fibre `{ω' : g ω' = g ω}`. -/

section condE

variable {T : Type*} [DecidableEq T]

/-- The weight of the `g`-fibre through `ω`. -/
def fibreMass (g : Ω → T) (ω : Ω) : ℝ := ∑ ω', if g ω' = g ω then μ.p ω' else 0

/-- Conditional expectation `E[f | g]` given the statistic `g` (the σ-field generated by `g`). -/
noncomputable def condE (g : Ω → T) (f : Ω → ℝ) : Ω → ℝ := fun ω =>
  (∑ ω', if g ω' = g ω then μ.p ω' * f ω' else 0) / μ.fibreMass g ω

lemma fibreMass_pos (g : Ω → T) (ω : Ω) : 0 < μ.fibreMass g ω := by
  unfold fibreMass
  apply Finset.sum_pos'
  · intro ω' _
    split_ifs
    · exact (μ.pos ω').le
    · exact le_rfl
  · exact ⟨ω, Finset.mem_univ _, by simp [μ.pos ω]⟩

lemma fibreMass_congr (g : Ω → T) {ω₁ ω₂ : Ω} (h : g ω₁ = g ω₂) :
    μ.fibreMass g ω₁ = μ.fibreMass g ω₂ := by
  simp [fibreMass, h]

/-- `E[f | g]` is `g`-measurable: it factors through `g`. -/
lemma condE_factorsThrough (g : Ω → T) (f : Ω → ℝ) :
    Function.FactorsThrough (μ.condE g f) g := by
  intro ω₁ ω₂ h
  simp [condE, fibreMass, h]

/-- The defining property of conditional expectation ("pull-out"): for every `g`-measurable `φ`,
`E[φ · E[f | g]] = E[φ f]`. -/
lemma E_mul_condE (g : Ω → T) (f φ : Ω → ℝ) (hφ : Function.FactorsThrough φ g) :
    μ.E (fun ω => φ ω * μ.condE g f ω) = μ.E (fun ω => φ ω * f ω) := by
  unfold E condE
  -- expand the inner sum, swap the two sums
  have step1 : ∀ ω, μ.p ω * (φ ω * ((∑ ω', if g ω' = g ω then μ.p ω' * f ω' else 0) /
      μ.fibreMass g ω)) =
      ∑ ω', if g ω' = g ω then (μ.p ω * φ ω / μ.fibreMass g ω) * (μ.p ω' * f ω') else 0 := by
    intro ω
    rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    split_ifs <;> ring
  simp_rw [step1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  -- inside the fibre of ω', replace φ ω and fibreMass ω by their values at ω'
  have step2 : ∀ ω, (if g ω' = g ω then (μ.p ω * φ ω / μ.fibreMass g ω) * (μ.p ω' * f ω') else 0)
      = (φ ω' / μ.fibreMass g ω' * (μ.p ω' * f ω')) * (if g ω = g ω' then μ.p ω else 0) := by
    intro ω
    by_cases h : g ω' = g ω
    · rw [ite_eq_left h, ite_eq_left h.symm, hφ h.symm, μ.fibreMass_congr g h.symm]; ring
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), mul_zero]
  simp_rw [step2]
  rw [← Finset.mul_sum]
  change φ ω' / μ.fibreMass g ω' * (μ.p ω' * f ω') * μ.fibreMass g ω' = _
  have := (μ.fibreMass_pos g ω').ne'
  field_simp

/-- `E[E[f | g]] = E f`. -/
lemma E_condE (g : Ω → T) (f : Ω → ℝ) : μ.E (μ.condE g f) = μ.E f := by
  have h := μ.E_mul_condE g f (fun _ => 1) (fun _ _ _ => rfl)
  simpa using h

/-- A `g`-measurable function is its own conditional expectation. -/
lemma condE_of_factorsThrough (g : Ω → T) (f : Ω → ℝ) (hf : Function.FactorsThrough f g) :
    μ.condE g f = f := by
  funext ω
  unfold condE
  have : (∑ ω', if g ω' = g ω then μ.p ω' * f ω' else 0) = f ω * μ.fibreMass g ω := by
    unfold fibreMass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    by_cases h : g ω' = g ω
    · rw [ite_eq_left h, ite_eq_left h, hf h]; ring
    · simp [h]
  rw [this, mul_div_assoc, div_self (μ.fibreMass_pos g ω).ne', mul_one]

lemma condE_add (g : Ω → T) (f₁ f₂ : Ω → ℝ) :
    μ.condE g (fun ω => f₁ ω + f₂ ω) = fun ω => μ.condE g f₁ ω + μ.condE g f₂ ω := by
  funext ω
  unfold condE
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ω' _ => ?_
  split_ifs <;> ring

lemma condE_const_mul (g : Ω → T) (c : ℝ) (f : Ω → ℝ) :
    μ.condE g (fun ω => c * f ω) = fun ω => c * μ.condE g f ω := by
  funext ω
  unfold condE
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ω' _ => ?_
  split_ifs <;> ring

/-- `Cov(f, E[h | g]) = Cov(f, h)` whenever `f` is `g`-measurable (tower property in covariance
form). -/
lemma cov_condE_right (g : Ω → T) (f h : Ω → ℝ) (hf : Function.FactorsThrough f g) :
    μ.cov f (μ.condE g h) = μ.cov f h := by
  simp only [cov, μ.E_mul_condE g h f hf, E_condE]

/-- `Cov(E[f | g], h) = Cov(f, h)` whenever `h` is `g`-measurable. -/
lemma cov_condE_left (g : Ω → T) (f h : Ω → ℝ) (hh : Function.FactorsThrough h g) :
    μ.cov (μ.condE g f) h = μ.cov f h := by
  rw [cov_comm, cov_condE_right μ g h f hh, cov_comm]

end condE

end FinProb

/-! ### Measurability helpers: `g`-measurable = factors through `g` -/

namespace FactorsThrough

variable {Ω T : Type*} {g : Ω → T}

lemma const (c : ℝ) : Function.FactorsThrough (fun _ : Ω => c) g := fun _ _ _ => rfl

lemma add {f₁ f₂ : Ω → ℝ} (h₁ : Function.FactorsThrough f₁ g) (h₂ : Function.FactorsThrough f₂ g) :
    Function.FactorsThrough (fun ω => f₁ ω + f₂ ω) g := fun _ _ h => by simp [h₁ h, h₂ h]

lemma sub {f₁ f₂ : Ω → ℝ} (h₁ : Function.FactorsThrough f₁ g) (h₂ : Function.FactorsThrough f₂ g) :
    Function.FactorsThrough (fun ω => f₁ ω - f₂ ω) g := fun _ _ h => by simp [h₁ h, h₂ h]

lemma const_mul {f : Ω → ℝ} (c : ℝ) (hf : Function.FactorsThrough f g) :
    Function.FactorsThrough (fun ω => c * f ω) g := fun _ _ h => by simp [hf h]

lemma sum {ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ} (hf : ∀ i, Function.FactorsThrough (f i) g) :
    Function.FactorsThrough (fun ω => ∑ i ∈ s, f i ω) g := fun _ _ h => by
  simp only; exact Finset.sum_congr rfl fun i _ => hf i h

end FactorsThrough

/-- The vector genotype `ω ↦ (g_i(ω))_i`; "`g`-measurable" in the note means measurable w.r.t.
`vec g`. -/
def vec {Ω I : Type*} (g : I → Ω → ℝ) : Ω → I → ℝ := fun ω i => g i ω

/-- Each coordinate `g_i` is measurable w.r.t. the vector genotype. -/
lemma factorsThrough_vec {Ω I : Type*} (g : I → Ω → ℝ) (i : I) :
    Function.FactorsThrough (g i) (vec g) := fun _ _ h => congrFun h i

/-- Affine functions of the genotype are genotype-measurable. -/
lemma factorsThrough_affine {Ω I : Type*} [Fintype I] (g : I → Ω → ℝ) (A : I → ℝ) (c : ℝ) :
    Function.FactorsThrough (fun ω => ∑ i, A i * g i ω + c) (vec g) :=
  FactorsThrough.add (FactorsThrough.sum _ fun i => FactorsThrough.const_mul _ (factorsThrough_vec g i))
    (FactorsThrough.const c)

/-! ### The scheme, the design, the world -/

namespace FinProb

section Scheme

variable {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
variable {K D I : Type*} [Fintype K] [Fintype I]

/-- The scheme `ĝ = Σ_k H_k (R_k − b_k)` (a random vector in `ℝᴰ`). -/
def update (H : K → Ω → D → ℝ) (R b : K → Ω → ℝ) : Ω → D → ℝ :=
  fun ω α => ∑ k, H k ω α * (R k ω - b k ω)

/-- Effective regressors after absorbing a linear-in-reward baseline `b_k = Σ_l B_{kl} R_l`:
`H̃_l = H_l − Σ_k B_{kl} H_k`. -/
def Htilde (H : K → Ω → D → ℝ) (B : K → K → ℝ) : K → Ω → D → ℝ :=
  fun l ω α => H l ω α - ∑ k, B k l * H k ω α

/-- The design `Γ_{ki} = Cov(H̃_k, g_i) ∈ ℝᴰ` (the note's `Γ_{jk}`, with `i` the flattened
`(j, component)` index), computable from the dice before any reward is seen. -/
def Gamma (H : K → Ω → D → ℝ) (g : I → Ω → ℝ) (k : K) (i : I) (α : D) : ℝ :=
  μ.cov (fun ω => H k ω α) (g i)

/-- `β` is a least-squares solution of the normal equations `Cov(g) β = Cov(g, R)`:
the world, the partial regression of the reward `R` on the genotypes. -/
def IsLSQ (g : I → Ω → ℝ) (R : Ω → ℝ) (β : I → ℝ) : Prop :=
  ∀ i, ∑ i', μ.cov (g i) (g i') * β i' = μ.cov (g i) R

/-- The linear least-squares projection `α + βᵀ g` of `R` on `span{1, g}` (with the intercept
`α = E R − βᵀ E g` making the residual mean zero). -/
def proj (g : I → Ω → ℝ) (R : Ω → ℝ) (β : I → ℝ) : Ω → ℝ :=
  fun ω => (μ.E R - ∑ i, β i * μ.E (g i)) + ∑ i, β i * g i ω

/-- The residual `e = R − α − βᵀ g` of `R` after linear regression on `span{1, g}`. -/
def resid (g : I → Ω → ℝ) (R : Ω → ℝ) (β : I → ℝ) : Ω → ℝ :=
  fun ω => R ω - μ.proj g R β ω

/-- `ζ = E[H | g] − P H` for a scalar regressor `H` with least-squares coefficients `Λ`. -/
noncomputable def zeta [DecidableEq (I → ℝ)] (g : I → Ω → ℝ) (H : Ω → ℝ) (Λ : I → ℝ) : Ω → ℝ :=
  fun ω => μ.condE (vec g) H ω - μ.proj g H Λ ω

/-- The remainder `Σ_k Cov(H̃_k, e_k)` of the pairing, coordinate `α`. -/
def remainder (H : K → Ω → D → ℝ) (g : I → Ω → ℝ) (R : K → Ω → ℝ) (β : K → I → ℝ) (α : D) : ℝ :=
  ∑ k, μ.cov (fun ω => H k ω α) (μ.resid g (R k) (β k))

/-- The pairing `Σ_{k,i} Γ_{ki} β_{ik}`, coordinate `α`. -/
def pairing (H : K → Ω → D → ℝ) (g : I → Ω → ℝ) (β : K → I → ℝ) (α : D) : ℝ :=
  ∑ k, ∑ i, μ.Gamma H g k i α * β k i

lemma cov_proj_right (g : I → Ω → ℝ) (R : Ω → ℝ) (β : I → ℝ) (f : Ω → ℝ) :
    μ.cov f (μ.proj g R β) = ∑ i, μ.cov f (g i) * β i := by
  unfold proj
  rw [cov_add_right, cov_const_right, zero_add, cov_sum_right]
  simp_rw [cov_const_mul_right]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma cov_resid_right (g : I → Ω → ℝ) (R : Ω → ℝ) (β : I → ℝ) (f : Ω → ℝ) :
    μ.cov f (μ.resid g R β) = μ.cov f R - ∑ i, μ.cov f (g i) * β i := by
  unfold resid
  rw [cov_sub_right, cov_proj_right]

lemma E_proj (g : I → Ω → ℝ) (R : Ω → ℝ) (β : I → ℝ) : μ.E (μ.proj g R β) = μ.E R := by
  unfold proj
  rw [E_add, E_const, E_sum]
  simp_rw [E_const_mul]
  ring

/-- The residual has mean zero: `e_k ⊥ 1`. -/
lemma E_resid (g : I → Ω → ℝ) (R : Ω → ℝ) (β : I → ℝ) : μ.E (μ.resid g R β) = 0 := by
  unfold resid
  rw [E_sub, E_proj, sub_self]

/-- Under the normal equations the residual is uncorrelated with every genotype: `e_k ⊥ g`. -/
lemma cov_resid_of_isLSQ (g : I → Ω → ℝ) (R : Ω → ℝ) (β : I → ℝ) (hβ : μ.IsLSQ g R β) (i : I) :
    μ.cov (g i) (μ.resid g R β) = 0 := by
  rw [cov_resid_right, hβ i, sub_self]

lemma proj_factorsThrough (g : I → Ω → ℝ) (R : Ω → ℝ) (β : I → ℝ) :
    Function.FactorsThrough (μ.proj g R β) (vec g) :=
  FactorsThrough.add (FactorsThrough.const _)
    (FactorsThrough.sum _ fun i => FactorsThrough.const_mul _ (factorsThrough_vec g i))

/-- `E H̃ = 0` is preserved: the effective regressors have mean zero when the `H_k` do. -/
lemma E_Htilde (H : K → Ω → D → ℝ) (B : K → K → ℝ) (hH : ∀ k α, μ.E (fun ω => H k ω α) = 0)
    (l : K) (α : D) : μ.E (fun ω => Htilde H B l ω α) = 0 := by
  unfold Htilde
  rw [E_sub, hH, E_sum]
  simp [E_const_mul, hH]

/-! ### Theorem A, first display: `E[ĝ] = Σ_k Cov(H̃_k, R_k)` -/

/-- **(A), first display.** For a scheme `ĝ = Σ_k H_k (R_k − b_k)` with mean-zero regressors and
baselines `b_k = b⁰_k + Σ_l B_{kl} R_l`, where the "dice-independent" part `b⁰_k` is uncorrelated
with `H_k` (true for constants and for `b⁰_k ⊥ H_k`), the expected update is
`E[ĝ] = Σ_l Cov(H̃_l, R_l)` with the effective regressors `H̃_l = H_l − Σ_k B_{kl} H_k`. -/
theorem expected_update_eq_sum_cov (H : K → Ω → D → ℝ) (R b b₀ : K → Ω → ℝ) (B : K → K → ℝ)
    (hH : ∀ k α, μ.E (fun ω => H k ω α) = 0)
    (hb : ∀ k ω, b k ω = b₀ k ω + ∑ l, B k l * R l ω)
    (hb₀ : ∀ k α, μ.cov (fun ω => H k ω α) (b₀ k) = 0) (α : D) :
    μ.E (fun ω => update H R b ω α) = ∑ l, μ.cov (fun ω => Htilde H B l ω α) (R l) := by
  unfold update Htilde
  simp_rw [hb]
  rw [E_sum]
  simp_rw [cov_sub_left, cov_sum_left, cov_const_mul_left]
  have h1 : ∀ k, μ.E (fun ω => H k ω α * (R k ω - (b₀ k ω + ∑ l, B k l * R l ω))) =
      μ.cov (fun ω => H k ω α) (R k) - ∑ l, B k l * μ.cov (fun ω => H k ω α) (R l) := by
    intro k
    rw [E_mul_eq_cov_of_E_eq_zero _ _ _ (hH k α), cov_sub_right, cov_add_right, hb₀, zero_add,
      cov_sum_right]
    simp_rw [cov_const_mul_right]
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_comm]

/-! ### Theorem A, second display: `E[ĝ] = Σ_{k,i} Γ_{ki} β_{ik} + Σ_k Cov(H̃_k, e_k)` -/

/-- **(A), second display, as an identity.** For *any* coefficient family `β` (in particular any
least-squares solution), `Σ_k Cov(H̃_k, R_k) = pairing + remainder`, with the residual
`e_k = R_k − α_k − β_{·k}ᵀ g`. -/
theorem sum_cov_eq_pairing_add_remainder (H : K → Ω → D → ℝ) (g : I → Ω → ℝ) (R : K → Ω → ℝ)
    (β : K → I → ℝ) (α : D) :
    ∑ k, μ.cov (fun ω => H k ω α) (R k) = μ.pairing H g β α + μ.remainder H g R β α := by
  unfold pairing remainder Gamma
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cov_resid_right]; ring

/-- **(A), both displays combined** for the scheme with baselines. -/
theorem expected_update_eq_pairing_add_remainder (H : K → Ω → D → ℝ) (g : I → Ω → ℝ)
    (R b b₀ : K → Ω → ℝ) (B : K → K → ℝ) (β : K → I → ℝ)
    (hH : ∀ k α, μ.E (fun ω => H k ω α) = 0)
    (hb : ∀ k ω, b k ω = b₀ k ω + ∑ l, B k l * R l ω)
    (hb₀ : ∀ k α, μ.cov (fun ω => H k ω α) (b₀ k) = 0) (α : D) :
    μ.E (fun ω => update H R b ω α) =
      μ.pairing (Htilde H B) g β α + μ.remainder (Htilde H B) g R β α := by
  rw [expected_update_eq_sum_cov μ H R b b₀ B hH hb hb₀,
    sum_cov_eq_pairing_add_remainder μ (Htilde H B) g R β α]

/-! ### Existence and well-definedness of the least-squares world `β` -/

/-- The centred, `√P`-weighted embedding of a random variable into `EuclideanSpace ℝ Ω`, under
which the Euclidean inner product is the covariance. -/
noncomputable def emb (f : Ω → ℝ) : EuclideanSpace ℝ Ω :=
  WithLp.toLp 2 (fun ω => Real.sqrt (μ.p ω) * (f ω - μ.E f))

lemma inner_emb (f h : Ω → ℝ) : inner ℝ (μ.emb f) (μ.emb h) = μ.cov f h := by
  rw [cov_eq_E_centered]
  simp only [emb, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  unfold E
  refine Finset.sum_congr rfl fun ω _ => ?_
  have := Real.mul_self_sqrt (μ.pos ω).le
  linear_combination (f ω - ∑ x, μ.p x * f x) * (h ω - ∑ x, μ.p x * h x) * this

/-- **Existence of the world.** The normal equations `Cov(g) β = Cov(g, R)` always have a solution
(the orthogonal projection of `R` onto `span{1, g}` in `L²(Ω)`), even when `Cov(g)` is singular. -/
theorem exists_isLSQ (g : I → Ω → ℝ) (R : Ω → ℝ) : ∃ β : I → ℝ, μ.IsLSQ g R β := by
  classical
  let v : I → EuclideanSpace ℝ Ω := fun i => μ.emb (g i)
  let S : Submodule ℝ (EuclideanSpace ℝ Ω) := Submodule.span ℝ (Set.range v)
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (S.starProjection_apply_mem (μ.emb R))
  refine ⟨β, fun i => ?_⟩
  have horth := S.starProjection_inner_eq_zero (μ.emb R) (v i)
    (Submodule.subset_span (Set.mem_range_self i))
  rw [← hβ, inner_sub_left, sum_inner] at horth
  simp only [inner_smul_left, conj_trivial] at horth
  simp only [v, inner_emb] at horth
  rw [sub_eq_zero] at horth
  rw [cov_comm μ (g i) R, horth]
  exact Finset.sum_congr rfl fun i' _ => by rw [cov_comm, mul_comm]

/-- **The pairing is well defined.** Any two least-squares solutions give the same linear
combination `βᵀ g` up to a constant (`Cov(g)(β − β') = 0` forces `Var((β − β')ᵀ g) = 0`), hence the
same `Σ_i Cov(f, g_i) β_i` for every `f`. -/
theorem sum_cov_mul_eq_of_isLSQ (g : I → Ω → ℝ) (R : Ω → ℝ) (β β' : I → ℝ)
    (hβ : μ.IsLSQ g R β) (hβ' : μ.IsLSQ g R β') (f : Ω → ℝ) :
    ∑ i, μ.cov f (g i) * β i = ∑ i, μ.cov f (g i) * β' i := by
  -- X := Σ (β − β')_i g_i has Cov(g_i, X) = 0 for all i, hence Var X = 0, hence X is constant
  set X : Ω → ℝ := fun ω => ∑ i, (β i - β' i) * g i ω with hX
  have hcovg : ∀ i, μ.cov (g i) X = 0 := by
    intro i
    have e : μ.cov (g i) X =
        ∑ i', μ.cov (g i) (g i') * β i' - ∑ i', μ.cov (g i) (g i') * β' i' := by
      rw [hX, cov_sum_right, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [cov_const_mul_right]; ring
    rw [e, hβ i, hβ' i, sub_self]
  have hvar : μ.cov X X = 0 := by
    conv_lhs => rw [hX]
    rw [cov_sum_left]
    simp_rw [cov_const_mul_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hcovg, mul_zero]
  have hconst := μ.eq_E_of_cov_self_eq_zero X hvar
  have hX' : X = fun _ => μ.E X := funext hconst
  have hcovf : μ.cov f X = 0 := by rw [hX', cov_const_right]
  have : μ.cov f X = ∑ i, μ.cov f (g i) * β i - ∑ i, μ.cov f (g i) * β' i := by
    rw [hX, cov_sum_right, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cov_const_mul_right]; ring
  linarith

/-- The pairing does not depend on the choice of least-squares solution. -/
theorem pairing_wellDefined (H : K → Ω → D → ℝ) (g : I → Ω → ℝ) (R : K → Ω → ℝ)
    (β β' : K → I → ℝ) (hβ : ∀ k, μ.IsLSQ g (R k) (β k)) (hβ' : ∀ k, μ.IsLSQ g (R k) (β' k)) (α : D) :
    μ.pairing H g β α = μ.pairing H g β' α := by
  unfold pairing Gamma
  exact Finset.sum_congr rfl fun k _ => μ.sum_cov_mul_eq_of_isLSQ g (R k) (β k) (β' k) (hβ k) (hβ' k) _

/-! ### The remainder for genotype-measurable rewards: `Cov(H̃_k, e_k) = Cov(ζ_k, R_k)` -/

section Zeta

variable [DecidableEq (I → ℝ)]

/-- `ζ` is genotype-measurable. -/
lemma zeta_factorsThrough (g : I → Ω → ℝ) (H : Ω → ℝ) (Λ : I → ℝ) :
    Function.FactorsThrough (μ.zeta g H Λ) (vec g) :=
  FactorsThrough.sub (μ.condE_factorsThrough _ _) (μ.proj_factorsThrough g H Λ)

/-- `ζ` has mean zero. -/
lemma E_zeta (g : I → Ω → ℝ) (H : Ω → ℝ) (Λ : I → ℝ) : μ.E (μ.zeta g H Λ) = 0 := by
  unfold zeta
  rw [E_sub, E_condE, E_proj, sub_self]

/-- `ζ ⊥ g` when `Λ` solves the normal equations for `H`: `Cov(g_i, ζ) = 0`. -/
lemma cov_zeta_of_isLSQ (g : I → Ω → ℝ) (H : Ω → ℝ) (Λ : I → ℝ) (hΛ : μ.IsLSQ g H Λ) (i : I) :
    μ.cov (g i) (μ.zeta g H Λ) = 0 := by
  unfold zeta
  rw [cov_sub_right, cov_condE_right μ (vec g) (g i) H (factorsThrough_vec g i), cov_proj_right,
    hΛ i, sub_self]

/-- **Remainder identity (verifier's corrected form).** If the reward `R` is genotype-measurable
and `β`, `Λ` solve the normal equations for `R` and for the (scalar) regressor `H`, then
`Cov(H, e) = Cov(ζ, R)` with `e` the residual of `R` and `ζ = E[H | g] − P H`. -/
theorem cov_resid_eq_cov_zeta (g : I → Ω → ℝ) (H R : Ω → ℝ) (β Λ : I → ℝ)
    (hR : Function.FactorsThrough R (vec g)) (hβ : μ.IsLSQ g R β) (hΛ : μ.IsLSQ g H Λ) :
    μ.cov H (μ.resid g R β) = μ.cov (μ.zeta g H Λ) R := by
  have he : Function.FactorsThrough (μ.resid g R β) (vec g) :=
    FactorsThrough.sub hR (μ.proj_factorsThrough g R β)
  -- Cov(H, e) = Cov(E[H|g], e) = Cov(ζ + PH, e) = Cov(ζ, e) + Σ Λ_i Cov(g_i, e) = Cov(ζ, e)
  have h1 : μ.cov H (μ.resid g R β) = μ.cov (μ.zeta g H Λ) (μ.resid g R β) := by
    rw [← cov_condE_left μ (vec g) H _ he]
    have : μ.condE (vec g) H = fun ω => μ.zeta g H Λ ω + μ.proj g H Λ ω := by
      funext ω; simp [zeta]
    rw [this, cov_add_left, cov_comm μ (μ.proj g H Λ), cov_proj_right]
    simp_rw [cov_comm μ (μ.resid g R β), cov_resid_of_isLSQ μ g R β hβ, zero_mul,
      Finset.sum_const_zero, add_zero]
  -- Cov(ζ, e) = Cov(ζ, R) − Σ_i Cov(ζ, g_i) β_i = Cov(ζ, R)
  rw [h1, cov_resid_right]
  simp_rw [cov_comm μ (μ.zeta g H Λ) (g _), cov_zeta_of_isLSQ μ g H Λ hΛ, zero_mul,
    Finset.sum_const_zero, sub_zero]

/-- The remainder of the pairing, for genotype-measurable rewards, is `Σ_k Cov(ζ_k, R_k)`
(coordinatewise in `α`). -/
theorem remainder_eq_sum_cov_zeta (H : K → Ω → D → ℝ) (g : I → Ω → ℝ) (R : K → Ω → ℝ)
    (β : K → I → ℝ) (Λ : K → D → I → ℝ)
    (hR : ∀ k, Function.FactorsThrough (R k) (vec g)) (hβ : ∀ k, μ.IsLSQ g (R k) (β k))
    (hΛ : ∀ k α, μ.IsLSQ g (fun ω => H k ω α) (Λ k α)) (α : D) :
    μ.remainder H g R β α = ∑ k, μ.cov (μ.zeta g (fun ω => H k ω α) (Λ k α)) (R k) := by
  unfold remainder
  exact Finset.sum_congr rfl fun k _ =>
    μ.cov_resid_eq_cov_zeta g _ (R k) (β k) (Λ k α) (hR k) (hβ k) (hΛ k α)

/-! ### The iff: the remainder vanishes on all genotype-measurable rewards iff `E[H̃ | g]` is affine -/

/-- `E[H | g]` is affine in the genotype: `E[H | g] = Σ_i A_i g_i + c` (everywhere). -/
def CondAffine (g : I → Ω → ℝ) (H : Ω → ℝ) : Prop :=
  ∃ (A : I → ℝ) (c : ℝ), ∀ ω, μ.condE (vec g) H ω = ∑ i, A i * g i ω + c

/-- If `E[H | g]` is affine then `Cov(H, e) = 0` for every genotype-measurable `R` with `e` its
least-squares residual (`⇐` of the iff, one regressor at a time). -/
theorem cov_resid_eq_zero_of_condAffine (g : I → Ω → ℝ) (H R : Ω → ℝ) (β : I → ℝ)
    (hR : Function.FactorsThrough R (vec g)) (hβ : μ.IsLSQ g R β) (hA : μ.CondAffine g H) :
    μ.cov H (μ.resid g R β) = 0 := by
  obtain ⟨A, c, hAc⟩ := hA
  have he : Function.FactorsThrough (μ.resid g R β) (vec g) :=
    FactorsThrough.sub hR (μ.proj_factorsThrough g R β)
  rw [← cov_condE_left μ (vec g) H _ he]
  have : μ.condE (vec g) H = fun ω => ∑ i, A i * g i ω + c := funext hAc
  rw [this, cov_add_left, cov_const_left, add_zero, cov_sum_left]
  simp_rw [cov_const_mul_left, cov_resid_of_isLSQ μ g R β hβ, mul_zero, Finset.sum_const_zero]

/-- If `Cov(H, e) = 0` for *every* genotype-measurable reward `R` and every least-squares `β`
for it, then `E[H | g]` is affine in `g` (`⇒` of the iff, one regressor at a time). The witness
reward is `R := ζ` itself, which is genotype-measurable with `β = 0` least-squares. -/
theorem condAffine_of_forall_cov_resid_eq_zero (g : I → Ω → ℝ) (H : Ω → ℝ)
    (h : ∀ R : Ω → ℝ, Function.FactorsThrough R (vec g) →
      ∀ β : I → ℝ, μ.IsLSQ g R β → μ.cov H (μ.resid g R β) = 0) :
    μ.CondAffine g H := by
  obtain ⟨Λ, hΛ⟩ := μ.exists_isLSQ g H
  set ζ := μ.zeta g H Λ with hζ
  -- β = 0 solves the normal equations for R = ζ since Cov(g_i, ζ) = 0
  have h0 : μ.IsLSQ g ζ (fun _ => 0) := by
    intro i
    simp only [mul_zero, Finset.sum_const_zero]
    rw [hζ, cov_zeta_of_isLSQ μ g H Λ hΛ i]
  have hrem := h ζ (μ.zeta_factorsThrough g H Λ) _ h0
  -- Cov(H, e_ζ) = Cov(ζ, ζ) = Var ζ, so Var ζ = 0 and ζ is constant (= E ζ = 0)
  rw [cov_resid_eq_cov_zeta μ g H ζ _ Λ (μ.zeta_factorsThrough g H Λ) h0 hΛ] at hrem
  have hc := μ.eq_E_of_cov_self_eq_zero ζ hrem
  rw [E_zeta] at hc
  refine ⟨Λ, μ.E H - ∑ i, Λ i * μ.E (g i), fun ω => ?_⟩
  have := hc ω
  simp only [hζ, zeta, proj] at this
  linarith

/-- **(A), the iff.** For a family of regressors `H_k ∈ ℝᴰ`: the remainder `Σ_k Cov(H̃_k, e_k)`
vanishes (in every coordinate) for every family of genotype-measurable rewards and every
least-squares `β` **iff** `E[H_k | g]` is affine in `g` for every `k` (and every coordinate). -/
theorem remainder_eq_zero_iff_condAffine (H : K → Ω → D → ℝ) (g : I → Ω → ℝ) :
    (∀ R : K → Ω → ℝ, (∀ k, Function.FactorsThrough (R k) (vec g)) →
      ∀ β : K → I → ℝ, (∀ k, μ.IsLSQ g (R k) (β k)) → ∀ α, μ.remainder H g R β α = 0) ↔
    (∀ k α, μ.CondAffine g (fun ω => H k ω α)) := by
  classical
  constructor
  · intro h k₀ α
    apply μ.condAffine_of_forall_cov_resid_eq_zero
    intro R hR β hβ
    -- the family with reward R in slot k₀ and 0 elsewhere, coefficients β in slot k₀ and 0 elsewhere
    let Rf : K → Ω → ℝ := fun k => if k = k₀ then R else fun _ => 0
    let βf : K → I → ℝ := fun k => if k = k₀ then β else fun _ => 0
    have hRf : ∀ k, Function.FactorsThrough (Rf k) (vec g) := by
      intro k; simp only [Rf]; split_ifs
      · exact hR
      · exact FactorsThrough.const 0
    have hβf : ∀ k, μ.IsLSQ g (Rf k) (βf k) := by
      intro k; simp only [Rf, βf]; split_ifs
      · exact hβ
      · intro i; simp [cov_const_right]
    have := h Rf hRf βf hβf α
    unfold remainder at this
    rw [Finset.sum_eq_single k₀] at this
    · simpa [Rf, βf] using this
    · intro k _ hk
      simp only [Rf, βf, ite_eq_right hk]
      have : μ.resid g (fun _ => (0:ℝ)) (fun _ => 0) = fun _ => 0 := by
        funext ω; simp [resid, proj, E_const]
      rw [this, cov_const_right]
    · intro hk; exact absurd (Finset.mem_univ k₀) hk
  · intro h R hR β hβ α
    unfold remainder
    exact Finset.sum_eq_zero fun k _ =>
      μ.cov_resid_eq_zero_of_condAffine g _ (R k) (β k) (hR k) (hβ k) (h k α)

end Zeta

end Scheme

/-! ### Instances of the affine condition (so the iff is not vacuous) -/

section Instances

variable {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
variable {K D I : Type*} [Fintype K] [Fintype I] [DecidableEq (I → ℝ)]

/-- **Instance 1 (ES with `H` linear in `δ`; single-context exponential-family score with
genotype the centred sufficient statistic; `genotype := score`).** If the regressor is itself an
affine function of the genotype, `E[H | g] = H` is affine in `g`. -/
theorem condAffine_of_affine (g : I → Ω → ℝ) (H : Ω → ℝ) (A : I → ℝ) (c : ℝ)
    (hH : ∀ ω, H ω = ∑ i, A i * g i ω + c) : μ.CondAffine g H := by
  refine ⟨A, c, fun ω => ?_⟩
  have hfac : Function.FactorsThrough H (vec g) := by
    have : H = fun ω => ∑ i, A i * g i ω + c := funext hH
    rw [this]; exact factorsThrough_affine g A c
  rw [μ.condE_of_factorsThrough (vec g) H hfac, hH]

omit [Fintype Ω] [DecidableEq (I → ℝ)] in
/-- **Instance 2 (group / linear-in-reward baselines).** Absorbing a linear baseline keeps the
effective regressors affine in the genotype: if every `H_k` is affine in `g`, so is every `H̃_l`. -/
theorem Htilde_affine (H : K → Ω → D → ℝ) (g : I → Ω → ℝ) (B : K → K → ℝ)
    (hH : ∀ k α, ∃ (A : I → ℝ) (c : ℝ), ∀ ω, H k ω α = ∑ i, A i * g i ω + c) (l : K) (α : D) :
    ∃ (A : I → ℝ) (c : ℝ), ∀ ω, Htilde H B l ω α = ∑ i, A i * g i ω + c := by
  choose A c hAc using hH
  refine ⟨fun i => A l α i - ∑ k, B k l * A k α i, c l α - ∑ k, B k l * c k α, fun ω => ?_⟩
  have e : ∀ ω, (∑ k, B k l * (∑ i, A k α i * g i ω + c k α)) =
      ∑ i, (∑ k, B k l * A k α i) * g i ω + ∑ k, B k l * c k α := by
    intro ω
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  simp only [Htilde, hAc, e, sub_mul, Finset.sum_sub_distrib]
  ring

/-- Hence the remainder of the pairing vanishes for every genotype-measurable reward family when
the regressors (with any linear baseline absorbed) are affine in the genotype. -/
theorem remainder_eq_zero_of_affine (H : K → Ω → D → ℝ) (g : I → Ω → ℝ) (B : K → K → ℝ)
    (hH : ∀ k α, ∃ (A : I → ℝ) (c : ℝ), ∀ ω, H k ω α = ∑ i, A i * g i ω + c)
    (R : K → Ω → ℝ) (hR : ∀ k, Function.FactorsThrough (R k) (vec g))
    (β : K → I → ℝ) (hβ : ∀ k, μ.IsLSQ g (R k) (β k)) (α : D) :
    μ.remainder (Htilde H B) g R β α = 0 := by
  have hall := (μ.remainder_eq_zero_iff_condAffine (Htilde H B) g).2 (fun k α' => by
    obtain ⟨A, c, hAc⟩ := Htilde_affine H g B hH k α'
    exact μ.condAffine_of_affine g _ A c hAc)
  exact hall R hR β hβ α

end Instances

/-! #### Instance 3: regressor = affine(genotype) + independent noise (`H̃ ∉ span{1, g}` but
`E[H̃ | g]` affine) -/

/-- The product of two finite probability spaces (independent dice). -/
def prod {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] (μ₁ : FinProb Ω₁) (μ₂ : FinProb Ω₂) :
    FinProb (Ω₁ × Ω₂) where
  p := fun ω => μ₁.p ω.1 * μ₂.p ω.2
  pos := fun ω => mul_pos (μ₁.pos _) (μ₂.pos _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, μ₂.sum_one, mul_one, μ₁.sum_one]

section Product

variable {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] (μ₁ : FinProb Ω₁) (μ₂ : FinProb Ω₂)
variable {T : Type*} [DecidableEq T]

/-- On a product space, the conditional expectation of a function of the second coordinate given
a statistic of the first coordinate is its (unconditional) mean. -/
theorem condE_snd_of_fst (G : Ω₁ → T) (Ξ : Ω₂ → ℝ) (g : Ω₁ × Ω₂ → T) (hg : ∀ ω, g ω = G ω.1)
    (ξ : Ω₁ × Ω₂ → ℝ) (hξ : ∀ ω, ξ ω = Ξ ω.2) :
    (μ₁.prod μ₂).condE g ξ = fun _ => μ₂.E Ξ := by
  funext ω
  unfold condE fibreMass
  simp only [prod, hg, hξ, Fintype.sum_prod_type]
  have h1 : ∀ a : Ω₁, (∑ b : Ω₂, if G a = G ω.1 then μ₁.p a * μ₂.p b * Ξ b else 0) =
      (if G a = G ω.1 then μ₁.p a else 0) * μ₂.E Ξ := by
    intro a
    split_ifs
    · unfold E; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
    · simp
  have h2 : ∀ a : Ω₁, (∑ b : Ω₂, if G a = G ω.1 then μ₁.p a * μ₂.p b else 0) =
      (if G a = G ω.1 then μ₁.p a else 0) := by
    intro a
    split_ifs
    · rw [← Finset.mul_sum, μ₂.sum_one, mul_one]
    · simp
  simp_rw [h1, h2]
  rw [← Finset.sum_mul]
  have hpos : 0 < ∑ a : Ω₁, (if G a = G ω.1 then μ₁.p a else 0) := by
    apply Finset.sum_pos'
    · intro a _; split_ifs
      · exact (μ₁.pos a).le
      · exact le_rfl
    · exact ⟨ω.1, Finset.mem_univ _, by simp [μ₁.pos]⟩
  rw [mul_comm, mul_div_assoc, div_self hpos.ne', mul_one]

variable {I : Type*} [Fintype I] [DecidableEq (I → ℝ)]

/-- **Instance 3.** Independent dice `(Ω₁, Ω₂)`; genotype `g_i = G_i ∘ fst`; regressor
`H = Σ_i A_i g_i + c + Ξ ∘ snd` with `Ξ` any function of the second die. Then
`E[H | g] = Σ_i A_i g_i + (c + E Ξ)` is affine in `g` although `H` itself is not a function of `g`
(e.g. ES with a regressor `δ + private noise`, or a shared die plus a private die). -/
theorem condAffine_affine_add_indep (G : I → Ω₁ → ℝ) (Ξ : Ω₂ → ℝ) (A : I → ℝ) (c : ℝ)
    (g : I → Ω₁ × Ω₂ → ℝ) (hg : ∀ i ω, g i ω = G i ω.1)
    (H : Ω₁ × Ω₂ → ℝ) (hH : ∀ ω, H ω = (∑ i, A i * g i ω + c) + Ξ ω.2) :
    (μ₁.prod μ₂).CondAffine g H := by
  refine ⟨A, c + μ₂.E Ξ, fun ω => ?_⟩
  have hH' : H = fun ω => (∑ i, A i * g i ω + c) + Ξ ω.2 := funext hH
  rw [hH', condE_add, condE_of_factorsThrough _ _ _ (factorsThrough_affine g A c),
    condE_snd_of_fst μ₁ μ₂ (fun a i => G i a) Ξ (vec g) (fun ω => by funext i; exact hg i ω)
      (fun ω => Ξ ω.2) (fun _ => rfl)]
  ring

end Product

/-! ### The causal-order (innovation) form of the covariance

For dice revealed in the order `x_0, x_1, …, x_{n-1}`, write `x_{<m} = (x_0, …, x_{m−1})` and
`D_v f := E[f | x_{≤v}] − E[f | x_{<v}]`.  Then, for `f` measurable w.r.t. all the dice,
`Cov(f, h) = Σ_{v<n} E[D_v f · D_v h]`. -/

section Causal

variable {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
variable {X : Type*} [DecidableEq X]

/-- The prefix statistic `x_{<m} = (x_0, …, x_{m−1})`. -/
def prefixStat (x : ℕ → Ω → X) (m : ℕ) : Ω → Fin m → X := fun ω i => x i ω

/-- The innovation `D_v f = E[f | x_{≤v}] − E[f | x_{<v}]`. -/
noncomputable def innov (x : ℕ → Ω → X) (v : ℕ) (f : Ω → ℝ) : Ω → ℝ :=
  fun ω => μ.condE (prefixStat x (v + 1)) f ω - μ.condE (prefixStat x v) f ω

omit [Fintype Ω] [DecidableEq X] in
lemma prefixStat_factorsThrough_of_le (x : ℕ → Ω → X) {m m' : ℕ} (h : m ≤ m') :
    Function.FactorsThrough (prefixStat x m) (prefixStat x m') := by
  intro ω ω' he
  funext i
  exact congrFun he ⟨i, lt_of_lt_of_le i.2 h⟩

omit [Fintype Ω] in
lemma factorsThrough_trans {T₁ T₂ : Type*} {f : Ω → ℝ} {g₁ : Ω → T₁} {g₂ : Ω → T₂}
    (h₁ : Function.FactorsThrough f g₁) (h₂ : Function.FactorsThrough g₁ g₂) :
    Function.FactorsThrough f g₂ := fun _ _ h => h₁ (h₂ h)

/-- Conditioning on a constant statistic gives the plain expectation. -/
lemma condE_of_const_stat {T : Type*} [DecidableEq T] (g : Ω → T) (hg : ∀ ω ω', g ω = g ω')
    (f : Ω → ℝ) : μ.condE g f = fun _ => μ.E f := by
  funext ω
  unfold condE fibreMass
  simp only [hg _ ω, ite_true, μ.sum_one, div_one]
  rfl

lemma condE_prefixStat_zero (x : ℕ → Ω → X) (f : Ω → ℝ) :
    μ.condE (prefixStat x 0) f = fun _ => μ.E f :=
  μ.condE_of_const_stat _ (fun _ _ => funext fun i => i.elim0) f

/-- `E[d²] = 0` forces `d = 0` everywhere. -/
lemma eq_zero_of_E_mul_self_eq_zero (d : Ω → ℝ) (h : μ.E (fun ω => d ω * d ω) = 0) : ∀ ω, d ω = 0 := by
  unfold E at h
  have hnn : ∀ ω ∈ (Finset.univ : Finset Ω), 0 ≤ μ.p ω * (d ω * d ω) := fun ω _ =>
    mul_nonneg (μ.pos ω).le (mul_self_nonneg _)
  intro ω
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h ω (Finset.mem_univ _)
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 (μ.pos ω).ne'
  · exact mul_self_eq_zero.1 h1

/-- Uniqueness of conditional expectation: a `g`-measurable `ψ` with `E[φ ψ] = E[φ f]` for all
`g`-measurable `φ` is `E[f | g]`. -/
theorem condE_unique {T : Type*} [DecidableEq T] (g : Ω → T) (f ψ : Ω → ℝ)
    (hψ : Function.FactorsThrough ψ g)
    (h : ∀ φ : Ω → ℝ, Function.FactorsThrough φ g →
      μ.E (fun ω => φ ω * ψ ω) = μ.E (fun ω => φ ω * f ω)) :
    ψ = μ.condE g f := by
  set d : Ω → ℝ := fun ω => ψ ω - μ.condE g f ω with hd
  have hdf : Function.FactorsThrough d g := FactorsThrough.sub hψ (μ.condE_factorsThrough g f)
  have h0 : μ.E (fun ω => d ω * d ω) = 0 := by
    have e1 : μ.E (fun ω => d ω * d ω) =
        μ.E (fun ω => d ω * ψ ω) - μ.E (fun ω => d ω * μ.condE g f ω) := by
      rw [← E_sub]; congr 1; funext ω; simp only [hd]; ring
    rw [e1, h d hdf, μ.E_mul_condE g f d hdf, sub_self]
  have := μ.eq_zero_of_E_mul_self_eq_zero d h0
  funext ω
  have hω := this ω
  simp only [hd] at hω
  linarith

/-- Tower property: `E[E[f | g₂] | g₁] = E[f | g₁]` when `g₁` is a function of `g₂`. -/
theorem condE_condE {T₁ T₂ : Type*} [DecidableEq T₁] [DecidableEq T₂] (g₁ : Ω → T₁) (g₂ : Ω → T₂)
    (h₁₂ : Function.FactorsThrough g₁ g₂) (f : Ω → ℝ) :
    μ.condE g₁ (μ.condE g₂ f) = μ.condE g₁ f := by
  symm
  apply μ.condE_unique g₁ (μ.condE g₂ f) (μ.condE g₁ f) (μ.condE_factorsThrough g₁ f)
  intro φ hφ
  rw [μ.E_mul_condE g₁ f φ hφ, μ.E_mul_condE g₂ f φ (factorsThrough_trans hφ h₁₂)]

lemma innov_factorsThrough (x : ℕ → Ω → X) (v : ℕ) (f : Ω → ℝ) :
    Function.FactorsThrough (μ.innov x v f) (prefixStat x (v + 1)) :=
  FactorsThrough.sub (μ.condE_factorsThrough _ _)
    (factorsThrough_trans (μ.condE_factorsThrough _ _)
      (prefixStat_factorsThrough_of_le x (Nat.le_succ v)))

/-- `E[φ · D_v h] = 0` for every `φ` measurable w.r.t. `x_{<v}`. -/
lemma E_mul_innov_eq_zero (x : ℕ → Ω → X) (v : ℕ) (h φ : Ω → ℝ)
    (hφ : Function.FactorsThrough φ (prefixStat x v)) :
    μ.E (fun ω => φ ω * μ.innov x v h ω) = 0 := by
  unfold innov
  have e : (fun ω => φ ω * (μ.condE (prefixStat x (v + 1)) h ω - μ.condE (prefixStat x v) h ω)) =
      fun ω => φ ω * μ.condE (prefixStat x (v + 1)) h ω - φ ω * μ.condE (prefixStat x v) h ω := by
    funext ω; ring
  rw [e, E_sub, μ.E_mul_condE _ h φ hφ,
    μ.E_mul_condE _ h φ (factorsThrough_trans hφ (prefixStat_factorsThrough_of_le x (Nat.le_succ v))),
    sub_self]

/-- Innovations at different times are orthogonal: `⟨D_v f, D_w h⟩ = 0` for `v < w`. -/
lemma E_innov_mul_innov_of_lt (x : ℕ → Ω → X) {v w : ℕ} (hvw : v < w) (f h : Ω → ℝ) :
    μ.E (fun ω => μ.innov x v f ω * μ.innov x w h ω) = 0 :=
  μ.E_mul_innov_eq_zero x w h _
    (factorsThrough_trans (μ.innov_factorsThrough x v f) (prefixStat_factorsThrough_of_le x hvw))

/-- Innovations have mean zero: `D_v f ⊥ 1`. -/
lemma E_innov (x : ℕ → Ω → X) (v : ℕ) (f : Ω → ℝ) : μ.E (μ.innov x v f) = 0 := by
  have := μ.E_mul_innov_eq_zero x v f (fun _ => 1) (fun _ _ _ => rfl)
  simpa using this

/-- Telescoping: `Σ_{v<n} D_v f = E[f | x_{<n}] − E f`. -/
lemma sum_innov (x : ℕ → Ω → X) (n : ℕ) (f : Ω → ℝ) (ω : Ω) :
    ∑ v ∈ Finset.range n, μ.innov x v f ω = μ.condE (prefixStat x n) f ω - μ.E f := by
  unfold innov
  rw [Finset.sum_range_sub (fun v => μ.condE (prefixStat x v) f ω) n, condE_prefixStat_zero]

/-- `D_v E[h | x_{<n}] = D_v h` for `v < n`. -/
lemma innov_condE (x : ℕ → Ω → X) {v n : ℕ} (hv : v < n) (h : Ω → ℝ) :
    μ.innov x v (μ.condE (prefixStat x n) h) = μ.innov x v h := by
  unfold innov
  rw [μ.condE_condE _ _ (prefixStat_factorsThrough_of_le x hv) h,
    μ.condE_condE _ _ (prefixStat_factorsThrough_of_le x hv.le) h]

/-- **(A), causal-order form.** For dice `x_0, …, x_{n−1}` and `f` a function of the dice
(`H̃_k` in the note; the verifier's caveat), for every `h ∈ L²(Ω)` (the reward `R_k`),
`Cov(f, h) = Σ_{v<n} ⟨D_v f, D_v h⟩`, `⟨a, b⟩ := E[a b]`. -/
theorem cov_eq_sum_E_innov_mul (x : ℕ → Ω → X) (n : ℕ) (f h : Ω → ℝ)
    (hf : Function.FactorsThrough f (prefixStat x n)) :
    μ.cov f h = ∑ v ∈ Finset.range n, μ.E (fun ω => μ.innov x v f ω * μ.innov x v h ω) := by
  -- replace h by h' = E[h | x_{<n}]; it has the same covariance with f and the same innovations
  set h' := μ.condE (prefixStat x n) h with hh'
  have hcov : μ.cov f h = μ.cov f h' := (μ.cov_condE_right _ f h hf).symm
  have hf' : μ.condE (prefixStat x n) f = f := μ.condE_of_factorsThrough _ f hf
  have hh'' : μ.condE (prefixStat x n) h' = h' :=
    μ.condE_of_factorsThrough _ h' (μ.condE_factorsThrough _ h)
  have hEh' : μ.E h' = μ.E h := μ.E_condE _ h
  -- centred variables are the sums of their innovations
  have hfsum : ∀ ω, f ω - μ.E f = ∑ v ∈ Finset.range n, μ.innov x v f ω := by
    intro ω; rw [sum_innov, hf']
  have hhsum : ∀ ω, h' ω - μ.E h' = ∑ v ∈ Finset.range n, μ.innov x v h' ω := by
    intro ω; rw [sum_innov, hh'']
  rw [hcov, cov_eq_E_centered]
  simp_rw [hfsum, hhsum, Finset.sum_mul_sum]
  rw [E_sum]
  simp_rw [E_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.sum_eq_single v]
  · rw [innov_condE μ x (Finset.mem_range.1 hv) h]
  · intro w _ hwv
    rcases lt_or_gt_of_ne hwv with hlt | hgt
    · have := μ.E_innov_mul_innov_of_lt x hlt h' f
      simpa only [mul_comm] using this
    · exact μ.E_innov_mul_innov_of_lt x hgt f h'
  · intro hv'; exact absurd hv hv'

end Causal

/-! ### A concrete check that the affine condition is genuinely restrictive

Three-point symmetric die `δ ∈ {−1, 0, 1}` (uniform). The first-order ES regressor `H = δ` satisfies
the affine condition; the second-order regressor `H = δ²` (the note's §4 item 3, `(ε² − σ²)/σ⁴` up
to affine rescaling) does not, so by the iff there is a `δ`-measurable reward with nonzero
remainder. -/

section Example3

/-- The uniform law on three points. -/
noncomputable def uniform3 : FinProb (Fin 3) where
  p := fun _ => 1 / 3
  pos := fun _ => by norm_num
  sum_one := by simp

/-- The die `δ(ω) = ω − 1 ∈ {−1, 0, 1}`. -/
def delta3 : Fin 3 → ℝ := fun ω => ((ω : ℕ) : ℝ) - 1

/-- `H = δ`: the affine condition holds (instance 1). -/
theorem condAffine_delta3 : uniform3.CondAffine (fun _ : Unit => delta3) delta3 :=
  uniform3.condAffine_of_affine _ delta3 (fun _ => 1) 0 (fun ω => by simp)

/-- `H = δ²`: the affine condition fails. -/
theorem not_condAffine_delta3_sq :
    ¬ uniform3.CondAffine (fun _ : Unit => delta3) (fun ω => delta3 ω ^ 2) := by
  rintro ⟨A, c, hAc⟩
  have hfac : Function.FactorsThrough (fun ω => delta3 ω ^ 2) (vec fun _ : Unit => delta3) :=
    fun _ _ h => by
      have := congrFun h ()
      simp only [vec] at this
      simp only [this]
  rw [uniform3.condE_of_factorsThrough _ _ hfac] at hAc
  have h0 := hAc 0
  have h1 := hAc 1
  have h2 := hAc 2
  simp [delta3] at h0 h1 h2
  linarith

/-- Consequently some `δ`-measurable reward has a nonzero remainder for the regressor `δ²`
(the iff is not vacuous in either direction). -/
theorem exists_remainder_ne_zero_delta3_sq :
    ∃ (R : Unit → Fin 3 → ℝ), (∀ k, Function.FactorsThrough (R k) (vec fun _ : Unit => delta3)) ∧
      ∃ (β : Unit → Unit → ℝ), (∀ k, uniform3.IsLSQ (fun _ : Unit => delta3) (R k) (β k)) ∧
        ∃ α : Unit, uniform3.remainder (fun _ ω _ => delta3 ω ^ 2) (fun _ : Unit => delta3) R β α ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have := (uniform3.remainder_eq_zero_iff_condAffine (K := Unit) (D := Unit)
    (fun _ ω _ => delta3 ω ^ 2) (fun _ : Unit => delta3)).1
    (fun R hR β hβ α => hcon R hR β hβ α) () ()
  exact not_condAffine_delta3_sq this

end Example3

end FinProb

end BoundaryTheorem.Pairing

#print axioms BoundaryTheorem.Pairing.FinProb.expected_update_eq_sum_cov
#print axioms BoundaryTheorem.Pairing.FinProb.sum_cov_eq_pairing_add_remainder
#print axioms BoundaryTheorem.Pairing.FinProb.expected_update_eq_pairing_add_remainder
#print axioms BoundaryTheorem.Pairing.FinProb.exists_isLSQ
#print axioms BoundaryTheorem.Pairing.FinProb.pairing_wellDefined
#print axioms BoundaryTheorem.Pairing.FinProb.cov_resid_eq_cov_zeta
#print axioms BoundaryTheorem.Pairing.FinProb.remainder_eq_sum_cov_zeta
#print axioms BoundaryTheorem.Pairing.FinProb.cov_resid_eq_zero_of_condAffine
#print axioms BoundaryTheorem.Pairing.FinProb.condAffine_of_forall_cov_resid_eq_zero
#print axioms BoundaryTheorem.Pairing.FinProb.remainder_eq_zero_iff_condAffine
#print axioms BoundaryTheorem.Pairing.FinProb.condAffine_of_affine
#print axioms BoundaryTheorem.Pairing.FinProb.Htilde_affine
#print axioms BoundaryTheorem.Pairing.FinProb.remainder_eq_zero_of_affine
#print axioms BoundaryTheorem.Pairing.FinProb.condE_snd_of_fst
#print axioms BoundaryTheorem.Pairing.FinProb.condAffine_affine_add_indep
#print axioms BoundaryTheorem.Pairing.FinProb.condE_unique
#print axioms BoundaryTheorem.Pairing.FinProb.condE_condE
#print axioms BoundaryTheorem.Pairing.FinProb.cov_eq_sum_E_innov_mul
#print axioms BoundaryTheorem.Pairing.FinProb.condAffine_delta3
#print axioms BoundaryTheorem.Pairing.FinProb.not_condAffine_delta3_sq
#print axioms BoundaryTheorem.Pairing.FinProb.exists_remainder_ne_zero_delta3_sq
