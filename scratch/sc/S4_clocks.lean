import Mathlib

/-!
# S4_clocks: why the update clock matters (synchronous vs checkerboard)

Fully proved (no `sorry`, no extra axioms).  Statements are identical to
`S4_clocks.statements.lean`; helper lemmas are added between them.

**What is proved.**
* Part 1 (two spins, `π ∝ exp (J s₁ s₂)`): the fully synchronous heat-bath kernel
  (both spins resampled at the same instant from their conditionals given the OLD value
  of the other) is computed exactly; at `exp (2J) = 3` it is the explicit 4×4 matrix
  `K(x,y) = (3/4 or 1/4)·(3/4 or 1/4)`, and `(πK)(++) = 9/32 ≠ 3/8 = π(++)`.  For every
  `J ≠ 0`, `π` is not stationary; the uniform law is stationary instead (for every `J`).
* Part 1, generalised (`sync_samples_marginal_product`, added by the second agent): for
  ANY strictly positive joint law of two sites over ANY finite alphabets, the synchronous
  heat-bath chain keeps the product of the two marginals stationary.  The uniform law of
  the Ising pair is the special case where both marginals are uniform.
* Part 2 (path `s₁ - s₂ - s₃`, any positive law of the form `f(s₁,s₂) g(s₂,s₃)`, hence
  the Ising chain with arbitrary couplings `J₁₂, J₂₃`): updating the two end sites at the
  same instant is *equal as a kernel* to updating site 1 then site 3 (and to site 3 then
  site 1), and therefore preserves the law.

**Interpretation (not formalised).**  A probabilistic computer built from p-bits must
never let two *coupled* p-bits update at the same instant: the synchronous update
samples a different distribution (here: it forgets the coupling entirely).  Sites that
form an independent set of the coupling graph (one colour of a checkerboard / bipartite
colouring) are conditionally independent given the rest, so they may update together
with no error.  Only the two-site and three-site path cases are proved here; the general
graph-colouring statement is the evident extrapolation, not a theorem in this file.
That the synchronous chain samples *exactly* `π₁ ⊗ π₂` (and not just has it as one
stationary law) needs uniqueness of the stationary law of a strictly positive kernel
(Perron–Frobenius); that uniqueness is not proved here.
-/

open Finset BigOperators

namespace S4Clocks

/-- Ising spin value of a Boolean: `true ↦ +1`, `false ↦ -1`. -/
def spin : Bool → ℝ
  | true => 1
  | false => -1

/-! ## Part 1: two coupled spins, fully synchronous heat-bath -/

/-- Boltzmann weight `exp (J s₁ s₂)` of a two-spin state. -/
noncomputable def w2 (J : ℝ) (s : Bool × Bool) : ℝ := Real.exp (J * spin s.1 * spin s.2)

/-- Partition function. -/
noncomputable def Z2 (J : ℝ) : ℝ := ∑ s, w2 J s

/-- Normalised Boltzmann distribution `π ∝ exp (J s₁ s₂)`. -/
noncomputable def pi2 (J : ℝ) (s : Bool × Bool) : ℝ := w2 J s / Z2 J

/-- Fully synchronous heat-bath kernel built from a joint law `π` on two spins:
both spins are resampled at the same instant, each from its exact conditional
given the OLD value of the other.  `syncK π x y = π(y₁ | x₂) · π(y₂ | x₁)`. -/
noncomputable def syncK (π : Bool × Bool → ℝ) (x y : Bool × Bool) : ℝ :=
  (π (y.1, x.2) / ∑ z, π (z, x.2)) * (π (x.1, y.2) / ∑ z, π (x.1, z))

/-- One step of the chain: `(μ K)(y) = ∑ₓ μ(x) K(x,y)`. -/
noncomputable def step {S : Type*} [Fintype S] (μ : S → ℝ) (K : S → S → ℝ) (y : S) : ℝ :=
  ∑ x, μ x * K x y

/-- The explicit 4×4 synchronous kernel at `exp (2J) = 3`
(conditional "agree" probability `3/4`). -/
noncomputable def Kconcrete (x y : Bool × Bool) : ℝ :=
  (if y.1 = x.2 then 3 / 4 else 1 / 4) * (if y.2 = x.1 then 3 / 4 else 1 / 4)

/-- Conditional probability that a spin agrees with its neighbour: `e^J/(e^J+e^{-J})`. -/
noncomputable def pp (J : ℝ) : ℝ := Real.exp J / (Real.exp J + Real.exp (-J))

lemma Z2_eq (J : ℝ) : Z2 J = 2 * (Real.exp J + Real.exp (-J)) := by
  simp [Z2, w2, spin, Fintype.sum_prod_type]; ring

lemma cond1 (J : ℝ) (y x : Bool) :
    pi2 J (y, x) / ∑ z, pi2 J (z, x) = if y = x then pp J else 1 - pp J := by
  have h1 := Real.exp_pos J
  have h2 := Real.exp_pos (-J)
  cases y <;> cases x <;> simp [pi2, w2, Z2, spin, pp, Fintype.sum_prod_type] <;> field_simp <;> ring

lemma cond2 (J : ℝ) (x y : Bool) :
    pi2 J (x, y) / ∑ z, pi2 J (x, z) = if y = x then pp J else 1 - pp J := by
  have h1 := Real.exp_pos J
  have h2 := Real.exp_pos (-J)
  cases y <;> cases x <;> simp [pi2, w2, Z2, spin, pp, Fintype.sum_prod_type] <;> field_simp <;> ring

lemma pi2_eq (J : ℝ) (s : Bool × Bool) :
    pi2 J s = if s.1 = s.2 then pp J / 2 else (1 - pp J) / 2 := by
  have h1 := Real.exp_pos J
  have h2 := Real.exp_pos (-J)
  obtain ⟨a, b⟩ := s
  cases a <;> cases b <;> simp [pi2, w2, Z2, spin, pp, Fintype.sum_prod_type] <;> field_simp <;> ring

lemma syncK_eq (J : ℝ) (x y : Bool × Bool) :
    syncK (pi2 J) x y = (if y.1 = x.2 then pp J else 1 - pp J) * (if y.2 = x.1 then pp J else 1 - pp J) := by
  unfold syncK; rw [cond1, cond2]

lemma pp_pos (J : ℝ) : 0 < pp J := by unfold pp; positivity
lemma pp_lt_one (J : ℝ) : pp J < 1 := by
  unfold pp; rw [div_lt_one (by positivity)]; linarith [Real.exp_pos (-J)]

lemma pp_concrete (J : ℝ) (hJ : Real.exp (2 * J) = 3) : pp J = 3 / 4 := by
  have h1 := Real.exp_pos J
  have h2 : Real.exp J * Real.exp J = 3 := by rw [← Real.exp_add]; rw [← hJ]; ring_nf
  have h3 : Real.exp (-J) = (Real.exp J)⁻¹ := Real.exp_neg J
  unfold pp; rw [h3]; field_simp; nlinarith

lemma pp_half (J : ℝ) (hJ : J ≠ 0) : pp J ≠ 1 / 2 := by
  intro h
  have h1 := Real.exp_pos J
  have h2 := Real.exp_pos (-J)
  unfold pp at h
  field_simp at h
  have : Real.exp J = Real.exp (-J) := by linarith
  have := Real.exp_injective this
  exact hJ (by linarith)

/-- (1a) Concrete kernel: at `exp (2J) = 3`, the synchronous heat-bath kernel is
exactly `Kconcrete`. -/
theorem syncK_concrete (J : ℝ) (hJ : Real.exp (2 * J) = 3) :
    syncK (pi2 J) = Kconcrete := by
  funext x y
  rw [syncK_eq, pp_concrete J hJ]; unfold Kconcrete; norm_num

/-- (1b) Concrete failure: at `exp (2J) = 3`, `π(++) = 3/8` but `(π K)(++) = 9/32`. -/
theorem sync_concrete_fail (J : ℝ) (hJ : Real.exp (2 * J) = 3) :
    pi2 J (true, true) = 3 / 8 ∧ step (pi2 J) (syncK (pi2 J)) (true, true) = 9 / 32 := by
  constructor
  · rw [pi2_eq, pp_concrete J hJ]; norm_num
  · simp only [step, syncK_eq, pi2_eq, pp_concrete J hJ, Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num

/-- (1c) General failure: for every coupling `J ≠ 0`, the Boltzmann law is NOT
stationary for the fully synchronous heat-bath update. -/
theorem sync_not_stationary (J : ℝ) (hJ : J ≠ 0) :
    step (pi2 J) (syncK (pi2 J)) (true, true) ≠ pi2 J (true, true) := by
  simp only [step, syncK_eq, pi2_eq, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false]
  intro h
  have hp := pp_pos J
  have hq := pp_lt_one J
  have hh := pp_half J hJ
  have key : pp J * (2 * pp J - 1) * (pp J - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 key with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · linarith
    · exact hh (by linarith)
  · linarith

/-- (1d) What the synchronous chain preserves instead: the uniform law
(all correlation between the two spins is lost), for every `J`. -/
theorem sync_uniform_stationary (J : ℝ) (y : Bool × Bool) :
    step (fun _ => (1 / 4 : ℝ)) (syncK (pi2 J)) y = 1 / 4 := by
  obtain ⟨a, b⟩ := y
  simp only [step, syncK_eq, Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b <;> simp <;> ring

/-! ## Going up: what the synchronous clock actually samples (any finite two-site system) -/

/-- Synchronous heat-bath kernel on an arbitrary finite two-site state space `α × β`
(the same formula as `syncK`, which is its `Bool × Bool` instance, see `syncK_eq_syncKG`). -/
noncomputable def syncKG {α β : Type*} [Fintype α] [Fintype β] (π : α × β → ℝ)
    (x y : α × β) : ℝ :=
  (π (y.1, x.2) / ∑ z, π (z, x.2)) * (π (x.1, y.2) / ∑ z, π (x.1, z))

/-- Product of the two one-site marginals of `π` (unnormalised: total mass `(∑ π)²`;
for a normalised `π` it is exactly the law `π₁ ⊗ π₂`). -/
noncomputable def margProd {α β : Type*} [Fintype α] [Fintype β] (π : α × β → ℝ)
    (s : α × β) : ℝ :=
  (∑ b, π (s.1, b)) * (∑ a, π (a, s.2))

lemma syncK_eq_syncKG (π : Bool × Bool → ℝ) : syncK π = syncKG π := rfl

/-- (1e, generalises `sync_uniform_stationary`) For ANY strictly positive joint law `π` of
two sites with ANY finite alphabets, the fully synchronous heat-bath chain built from `π`
has the product of `π`'s marginals as a stationary law.  So the synchronous clock keeps
each one-site marginal and forgets the correlation between the sites.

Interpretation (not formalised here): when `π > 0` the kernel is strictly positive, so its
stationary law is unique (Perron–Frobenius).  The synchronous chain therefore samples
`π₁ ⊗ π₂`, and it samples `π` correctly only when `π` is already a product law, i.e. the
two sites are not coupled. -/
theorem sync_samples_marginal_product {α β : Type*} [Fintype α] [Fintype β]
    (π : α × β → ℝ) (hπ : ∀ s, 0 < π s) (y : α × β) :
    step (margProd π) (syncKG π) y = margProd π y := by
  have hm1 : ∀ a : α, (∑ b, π (a, b)) ≠ 0 := fun a =>
    (Finset.sum_pos (fun b _ => hπ (a, b)) ⟨y.2, Finset.mem_univ _⟩).ne'
  have hm2 : ∀ b : β, (∑ a, π (a, b)) ≠ 0 := fun b =>
    (Finset.sum_pos (fun a _ => hπ (a, b)) ⟨y.1, Finset.mem_univ _⟩).ne'
  have hterm : ∀ x : α × β, margProd π x * syncKG π x y = π (x.1, y.2) * π (y.1, x.2) := by
    intro x
    unfold margProd syncKG
    field_simp [hm1 x.1, hm2 x.2]
  simp only [step, hterm]
  rw [Fintype.sum_prod_type]
  unfold margProd
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _

/-! ## Part 2: three-spin path `s₁ - s₂ - s₃`, checkerboard update -/

/-- States of the 3-spin path, written `(s₁, s₂, s₃)`. -/
abbrev S3 := Bool × Bool × Bool

/-- Heat-bath update of site 1 alone (sites 2, 3 kept). -/
noncomputable def heat1 (π : S3 → ℝ) (x y : S3) : ℝ :=
  if y.2 = x.2 then π y / ∑ z, π (z, x.2) else 0

/-- Heat-bath update of site 3 alone (sites 1, 2 kept). -/
noncomputable def heat3 (π : S3 → ℝ) (x y : S3) : ℝ :=
  if y.1 = x.1 ∧ y.2.1 = x.2.1 then π y / ∑ z, π (x.1, x.2.1, z) else 0

/-- Simultaneous (same-instant) heat-bath update of sites 1 and 3: each resampled from
its conditional given the OLD values of all other sites; site 2 kept. -/
noncomputable def sim13 (π : S3 → ℝ) (x y : S3) : ℝ :=
  if y.2.1 = x.2.1 then
    (π (y.1, x.2.1, x.2.2) / ∑ z, π (z, x.2.1, x.2.2)) *
      (π (x.1, x.2.1, y.2.2) / ∑ z, π (x.1, x.2.1, z))
  else 0

/-- Kernel composition (first `K`, then `L`). -/
def comp {S : Type*} [Fintype S] (K L : S → S → ℝ) (x y : S) : ℝ := ∑ m, K x m * L m y

/-- Path-factorised weight `f(s₁,s₂) · g(s₂,s₃)` (any nearest-neighbour Gibbs law on the path). -/
def w3 (f g : Bool → Bool → ℝ) (s : S3) : ℝ := f s.1 s.2.1 * g s.2.1 s.2.2

/-- Ising chain on the path with couplings `J₁₂, J₂₃`, normalised. -/
noncomputable def pi3 (J₁ J₂ : ℝ) (s : S3) : ℝ :=
  w3 (fun a b => Real.exp (J₁ * spin a * spin b)) (fun b c => Real.exp (J₂ * spin b * spin c)) s /
    ∑ t, w3 (fun a b => Real.exp (J₁ * spin a * spin b))
      (fun b c => Real.exp (J₂ * spin b * spin c)) t

/-- `step` along a composed kernel is two steps. -/
lemma step_comp {S : Type*} [Fintype S] (μ : S → ℝ) (K L : S → S → ℝ) (y : S) :
    step μ (comp K L) y = step (step μ K) L y := by
  simp only [step, comp, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x _ => by ring

/-- (2a) Any single-site heat-bath update preserves any positive law. -/
theorem heat1_stationary (π : S3 → ℝ) (hπ : ∀ s, 0 < π s) (y : S3) :
    step π (heat1 π) y = π y := by
  have hs : ∀ b c, π (true, b, c) + π (false, b, c) ≠ 0 := fun b c =>
    (add_pos (hπ _) (hπ _)).ne'
  obtain ⟨a, b, c⟩ := y
  cases a <;> cases b <;> cases c <;>
    simp [step, heat1, Fintype.sum_prod_type] <;> field_simp [hs]

theorem heat3_stationary (π : S3 → ℝ) (hπ : ∀ s, 0 < π s) (y : S3) :
    step π (heat3 π) y = π y := by
  have hs : ∀ a b, π (a, b, true) + π (a, b, false) ≠ 0 := fun a b =>
    (add_pos (hπ _) (hπ _)).ne'
  obtain ⟨a, b, c⟩ := y
  cases a <;> cases b <;> cases c <;>
    simp [step, heat3, Fintype.sum_prod_type] <;> field_simp [hs]

/-- Conditional of site 1 under the path law: depends only on `s₂` (the `g` factor cancels). -/
noncomputable def F (f : Bool → Bool → ℝ) (a b : Bool) : ℝ := f a b / (f true b + f false b)
/-- Conditional of site 3 under the path law: depends only on `s₂` (the `f` factor cancels). -/
noncomputable def G (g : Bool → Bool → ℝ) (b c : Bool) : ℝ := g b c / (g b true + g b false)

lemma condA (f g : Bool → Bool → ℝ) (hf : ∀ a b, 0 < f a b) (hg : ∀ a b, 0 < g a b)
    (a b c : Bool) : w3 f g (a, b, c) / ∑ z, w3 f g (z, b, c) = F f a b := by
  have h1 := hg b c
  have h2 : f true b + f false b ≠ 0 := (add_pos (hf _ _) (hf _ _)).ne'
  simp only [w3, F, Fintype.sum_bool]
  rw [← add_mul]; field_simp

lemma condB (f g : Bool → Bool → ℝ) (hf : ∀ a b, 0 < f a b) (hg : ∀ a b, 0 < g a b)
    (a b c : Bool) : w3 f g (a, b, c) / ∑ z, w3 f g (a, b, z) = G g b c := by
  have h1 := hf a b
  have h2 : g b true + g b false ≠ 0 := (add_pos (hg _ _) (hg _ _)).ne'
  simp only [w3, G, Fintype.sum_bool]
  rw [← mul_add]; field_simp

lemma heat1_w3 (f g : Bool → Bool → ℝ) (hf : ∀ a b, 0 < f a b) (hg : ∀ a b, 0 < g a b)
    (x y : S3) : heat1 (w3 f g) x y = if y.2 = x.2 then F f y.1 x.2.1 else 0 := by
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  unfold heat1
  split_ifs with h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact condA f g hf hg _ _ _
  · rfl

lemma heat3_w3 (f g : Bool → Bool → ℝ) (hf : ∀ a b, 0 < f a b) (hg : ∀ a b, 0 < g a b)
    (x y : S3) : heat3 (w3 f g) x y =
      if y.1 = x.1 ∧ y.2.1 = x.2.1 then G g x.2.1 y.2.2 else 0 := by
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  unfold heat3
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    simp only at h1 h2
    subst h1 h2
    exact condB f g hf hg _ _ _
  · rfl

lemma sim13_w3 (f g : Bool → Bool → ℝ) (hf : ∀ a b, 0 < f a b) (hg : ∀ a b, 0 < g a b)
    (x y : S3) : sim13 (w3 f g) x y =
      if y.2.1 = x.2.1 then F f y.1 x.2.1 * G g x.2.1 y.2.2 else 0 := by
  unfold sim13
  rw [condA f g hf hg, condB f g hf hg]

/-- (2b) Checkerboard = sequential: for a path-factorised law, updating the two
end sites at the same instant equals updating site 1 then site 3. -/
theorem sim13_eq_comp13 (f g : Bool → Bool → ℝ) (hf : ∀ a b, 0 < f a b)
    (hg : ∀ a b, 0 < g a b) :
    sim13 (w3 f g) = comp (heat1 (w3 f g)) (heat3 (w3 f g)) := by
  funext x y
  simp only [comp, sim13_w3 f g hf hg, heat1_w3 f g hf hg, heat3_w3 f g hf hg]
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  cases x1 <;> cases x2 <;> cases x3 <;> cases y1 <;> cases y2 <;> cases y3 <;>
    simp [Fintype.sum_prod_type]

/-- (2b') ... and equally site 3 then site 1 (the order is irrelevant). -/
theorem sim13_eq_comp31 (f g : Bool → Bool → ℝ) (hf : ∀ a b, 0 < f a b)
    (hg : ∀ a b, 0 < g a b) :
    sim13 (w3 f g) = comp (heat3 (w3 f g)) (heat1 (w3 f g)) := by
  funext x y
  simp only [comp, sim13_w3 f g hf hg, heat1_w3 f g hf hg, heat3_w3 f g hf hg]
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  cases x1 <;> cases x2 <;> cases x3 <;> cases y1 <;> cases y2 <;> cases y3 <;>
    simp [Fintype.sum_prod_type] <;> ring

/-- (2c) Hence the simultaneous end-site update preserves the path law. -/
theorem sim13_stationary (f g : Bool → Bool → ℝ) (hf : ∀ a b, 0 < f a b)
    (hg : ∀ a b, 0 < g a b) (y : S3) :
    step (w3 f g) (sim13 (w3 f g)) y = w3 f g y := by
  have hw : ∀ s, 0 < w3 f g s := fun s => mul_pos (hf _ _) (hg _ _)
  rw [sim13_eq_comp13 f g hf hg, step_comp]
  have : step (w3 f g) (heat1 (w3 f g)) = w3 f g := funext (heat1_stationary _ hw)
  rw [this, heat3_stationary _ hw]

/-- (2d) Ising instance, arbitrary couplings: the normalised Boltzmann law of the
3-spin path is stationary for the checkerboard (end-sites-together) update. -/
theorem sim13_stationary_ising (J₁ J₂ : ℝ) (y : S3) :
    step (pi3 J₁ J₂) (sim13 (pi3 J₁ J₂)) y = pi3 J₁ J₂ y := by
  set Z := ∑ t, w3 (fun a b => Real.exp (J₁ * spin a * spin b))
      (fun b c => Real.exp (J₂ * spin b * spin c)) t with hZ
  have hZpos : 0 < Z := Finset.sum_pos (fun t _ => mul_pos (Real.exp_pos _) (Real.exp_pos _))
    Finset.univ_nonempty
  have hpi : pi3 J₁ J₂ = w3 (fun a b => Real.exp (J₁ * spin a * spin b) / Z)
      (fun b c => Real.exp (J₂ * spin b * spin c)) := by
    funext s
    change w3 _ _ s / Z = _
    simp only [w3]; ring
  rw [hpi]
  exact sim13_stationary _ _ (fun a b => div_pos (Real.exp_pos _) hZpos)
    (fun a b => Real.exp_pos _) y

/-! ## Sanity checks: the main theorems at concrete numbers -/

/-- `J = log 3 / 2` really satisfies `exp (2J) = 3`, so the concrete hypothesis is not vacuous. -/
lemma exp_two_logthree_half : Real.exp (2 * (Real.log 3 / 2)) = 3 := by
  rw [show 2 * (Real.log 3 / 2) = Real.log 3 by ring, Real.exp_log (by norm_num)]

example : pi2 (Real.log 3 / 2) (true, true) = 3 / 8 ∧
    step (pi2 (Real.log 3 / 2)) (syncK (pi2 (Real.log 3 / 2))) (true, true) = 9 / 32 :=
  sync_concrete_fail _ exp_two_logthree_half

/-- One kernel entry: from `(+,+)` both spins flip to `(-,-)` with probability `1/16`. -/
example : syncK (pi2 (Real.log 3 / 2)) (true, true) (false, false) = 1 / 16 := by
  rw [syncK_concrete _ exp_two_logthree_half]; simp [Kconcrete]; norm_num

example : step (pi2 1) (syncK (pi2 1)) (true, true) ≠ pi2 1 (true, true) :=
  sync_not_stationary 1 one_ne_zero

example (y : S3) : step (pi3 1 (-2)) (sim13 (pi3 1 (-2))) y = pi3 1 (-2) y :=
  sim13_stationary_ising 1 (-2) y

/-- For the Ising pair the marginal product is uniform (`1/4` everywhere), so
`sync_samples_marginal_product` recovers `sync_uniform_stationary`. -/
example (J : ℝ) (s : Bool × Bool) : margProd (pi2 J) s = 1 / 4 := by
  obtain ⟨a, b⟩ := s
  cases a <;> cases b <;> simp [margProd, pi2_eq] <;> ring

/-- The generalisation at a lopsided 3×2 alphabet (correlated, non-uniform marginals). -/
example (y : Fin 3 × Bool) :
    let π : Fin 3 × Bool → ℝ := fun s => (s.1.val + 1 : ℝ) + (if s.2 then 2 * s.1.val else 0)
    step (margProd π) (syncKG π) y = margProd π y :=
  sync_samples_marginal_product _ (fun s => by positivity) y

end S4Clocks
