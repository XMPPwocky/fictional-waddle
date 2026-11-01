import Mathlib

/-!
# A01 — Curie's principle (symmetry of causes is inherited by effects)

## What is proved (pure mathematics)

Throughout, `K` is a field and `V` a `K`-vector space; `R : V →ₗ[K] V` is an involution
(`R ∘ₗ R = id`). Where a factor `1/2` matters for the decomposition `x = e x + o x` we assume
`(2 : K) ≠ 0` (true for `ℝ`; the commuting identities themselves need no such hypothesis).

(a) Linear case, `M ∘ₗ R = R ∘ₗ M`:
* `even_preserved`, `odd_preserved`: `M` maps the `+1` eigenspace (`R x = x`) and the `-1`
  eigenspace (`R x = -x`) into themselves.
* `evenPart`, `oddPart`: `e x = ½(x + R x)`, `o x = ½(x - R x)`;
  `evenPart_isEven`, `oddPart_isOdd`, `even_add_odd` (the decomposition, needs `2 ≠ 0`),
  `evenPart_of_even`, `oddPart_of_even`.
* `evenPart_comm`, `oddPart_comm`: `e (M x) = M (e x)`, `o (M x) = M (o x)`.
* `pow_comm_R`, `evenPart_pow`, `oddPart_pow`: the same for every power `M ^ k`.
* `even_stays_even`, `odd_part_stays_zero`: an even initial state stays even for all `k`, and its
  odd part stays exactly `0`.
* `matrix_even_stays_even`: the `Matrix (Fin n) (Fin n) ℝ` / `mulVec` form (only commuting
  is assumed; `R * R = 1` is not needed). A concrete `example` instantiates it with the swap
  `R = !![0,1;1,0]`, `M = !![2,1;1,2]`, `v = (1,1)`.

(d) Generalization to a symmetry group (Curie's principle in its usual form):
* `stabilizer_le_iterate`: if `f` is `G`-equivariant for a group action, then the symmetry group
  (stabilizer) of the initial state `x` is contained in the symmetry group of every iterate
  `f^[k] x`. The involution case (b) is the special case `G = ℤ/2`.

(b) Nonlinear equivariant case, on any type `α`, `f : α → α`, `R : α → α`, `f ∘ R = R ∘ f`:
* `equivariant_fixed`: `R x = x → R (f x) = f x`.
* `equivariant_iterate_comm`: `f^[k] (R x) = R (f^[k] x)` (no fixedness needed).
* `equivariant_iterate_fixed`: `R x = x → ∀ k, R (f^[k] x) = f^[k] x`.

(c) Converse:
* `commute_iff_preserves`: (with `2 ≠ 0`) `M` preserves BOTH the even and the odd subspace iff
  `M ∘ₗ R = R ∘ₗ M`.
* `not_commute_breaks_parity`: if `M` does not commute with `R`, there is an even `x` with `M x`
  not even, OR an odd `x` with `M x` not odd.
* `preserving_even_alone_insufficient`: the stronger "there is an even `x` with `M x` not even"
  is FALSE in general: on `ℝ × ℝ` with `R (a,b) = (a,-b)` and `M (a,b) = (a+b, b)`, `M` preserves
  the even subspace yet does not commute with `R` (it is the odd subspace that breaks). This is
  why (c) must be stated as the disjunction / iff above.

## Interpretation (not proved; physics reading)

Read `R` as a symmetry operation (mirror, parity, time reversal on states) and `M` / `f` as the
dynamics. "Effects are at least as symmetric as their causes": symmetric dynamics acting on a
symmetric initial state can never produce an asymmetric state, and a symmetry-breaking
component (odd part) can never appear from nothing. The converse says that the ONLY way to
create parity mixing is dynamics that fail to commute with the symmetry. Nothing here models
spontaneous symmetry breaking, which in physics arises via instability + noise/selection of a
branch, or in the limit of infinitely many degrees of freedom; those are outside these statements.
-/

namespace A01Curie

section Linear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Even part `e x = ½ (x + R x)`. -/
def evenPart (R : V →ₗ[K] V) (x : V) : V := (2 : K)⁻¹ • (x + R x)

/-- Odd part `o x = ½ (x - R x)`. -/
def oddPart (R : V →ₗ[K] V) (x : V) : V := (2 : K)⁻¹ • (x - R x)

/-- **(a1)** A commuting `M` preserves the `+1` eigenspace. -/
theorem even_preserved (R M : V →ₗ[K] V) (hcomm : M ∘ₗ R = R ∘ₗ M) (x : V) (hx : R x = x) :
    R (M x) = M x := by
  have h := LinearMap.congr_fun hcomm x
  simp only [LinearMap.comp_apply] at h
  rw [← h, hx]

/-- **(a2)** A commuting `M` preserves the `-1` eigenspace. -/
theorem odd_preserved (R M : V →ₗ[K] V) (hcomm : M ∘ₗ R = R ∘ₗ M) (x : V) (hx : R x = -x) :
    R (M x) = -(M x) := by
  have h := LinearMap.congr_fun hcomm x
  simp only [LinearMap.comp_apply] at h
  rw [← h, hx, map_neg]

/-- The even part is even (uses only `R ∘ R = id`). -/
theorem evenPart_isEven (R : V →ₗ[K] V) (hR : R ∘ₗ R = LinearMap.id) (x : V) :
    R (evenPart R x) = evenPart R x := by
  have h := LinearMap.congr_fun hR x
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  simp only [evenPart, map_smul, map_add, h, add_comm]

/-- The odd part is odd (uses only `R ∘ R = id`). -/
theorem oddPart_isOdd (R : V →ₗ[K] V) (hR : R ∘ₗ R = LinearMap.id) (x : V) :
    R (oddPart R x) = -(oddPart R x) := by
  have h := LinearMap.congr_fun hR x
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  simp only [oddPart, map_smul, map_sub, h, ← smul_neg, neg_sub]

/-- Decomposition `x = e x + o x` (needs `2 ≠ 0`). -/
theorem even_add_odd (R : V →ₗ[K] V) (h2 : (2 : K) ≠ 0) (x : V) :
    evenPart R x + oddPart R x = x := by
  simp only [evenPart, oddPart, ← smul_add]
  rw [show x + R x + (x - R x) = (2 : K) • x by rw [two_smul]; abel, smul_smul,
    inv_mul_cancel₀ h2, one_smul]

/-- An even vector is its own even part (needs `2 ≠ 0`). -/
theorem evenPart_of_even (R : V →ₗ[K] V) (h2 : (2 : K) ≠ 0) (x : V) (hx : R x = x) :
    evenPart R x = x := by
  have h0 : oddPart R x = 0 := by simp [oddPart, hx]
  have := even_add_odd R h2 x
  rwa [h0, add_zero] at this

/-- An even vector has zero odd part. -/
theorem oddPart_of_even (R : V →ₗ[K] V) (x : V) (hx : R x = x) :
    oddPart R x = 0 := by
  simp [oddPart, hx]

/-- **(a3)** `e (M x) = M (e x)`. -/
theorem evenPart_comm (R M : V →ₗ[K] V) (hcomm : M ∘ₗ R = R ∘ₗ M) (x : V) :
    evenPart R (M x) = M (evenPart R x) := by
  have h := LinearMap.congr_fun hcomm x
  simp only [LinearMap.comp_apply] at h
  simp only [evenPart, map_smul, map_add, h]

/-- **(a3')** `o (M x) = M (o x)`. -/
theorem oddPart_comm (R M : V →ₗ[K] V) (hcomm : M ∘ₗ R = R ∘ₗ M) (x : V) :
    oddPart R (M x) = M (oddPart R x) := by
  have h := LinearMap.congr_fun hcomm x
  simp only [LinearMap.comp_apply] at h
  simp only [oddPart, map_smul, map_sub, h]

/-- Powers of a commuting map commute. -/
theorem pow_comm_R (R M : Module.End K V) (hcomm : M ∘ₗ R = R ∘ₗ M) (k : ℕ) :
    (M ^ k) ∘ₗ R = R ∘ₗ (M ^ k) := by
  have hc : Commute M R := by
    rw [Commute, SemiconjBy]; exact hcomm
  exact (hc.pow_left k).eq

/-- **(a4)** Iterates conserve the even part. -/
theorem evenPart_pow (R M : Module.End K V) (hcomm : M ∘ₗ R = R ∘ₗ M) (k : ℕ) (x : V) :
    evenPart R ((M ^ k) x) = (M ^ k) (evenPart R x) := by
  exact evenPart_comm R (M ^ k) (pow_comm_R R M hcomm k) x

/-- **(a4')** Iterates conserve the odd part. -/
theorem oddPart_pow (R M : Module.End K V) (hcomm : M ∘ₗ R = R ∘ₗ M) (k : ℕ) (x : V) :
    oddPart R ((M ^ k) x) = (M ^ k) (oddPart R x) := by
  exact oddPart_comm R (M ^ k) (pow_comm_R R M hcomm k) x

/-- **(a5)** An even initial state stays even forever. -/
theorem even_stays_even (R M : Module.End K V) (hcomm : M ∘ₗ R = R ∘ₗ M) (x : V)
    (hx : R x = x) (k : ℕ) : R ((M ^ k) x) = (M ^ k) x := by
  exact even_preserved R (M ^ k) (pow_comm_R R M hcomm k) x hx

/-- **(a5')** The odd part of an even initial state stays exactly zero forever. -/
theorem odd_part_stays_zero (R M : Module.End K V) (hcomm : M ∘ₗ R = R ∘ₗ M) (x : V)
    (hx : R x = x) (k : ℕ) : oddPart R ((M ^ k) x) = 0 := by
  exact oddPart_of_even R _ (even_stays_even R M hcomm x hx k)

/-- **(c1)** With `2 ≠ 0` and `R` an involution: `M` preserves both parity subspaces iff it
commutes with `R`. -/
theorem commute_iff_preserves (R M : V →ₗ[K] V) (hR : R ∘ₗ R = LinearMap.id) (h2 : (2 : K) ≠ 0) :
    ((∀ x, R x = x → R (M x) = M x) ∧ (∀ x, R x = -x → R (M x) = -(M x))) ↔
      M ∘ₗ R = R ∘ₗ M := by
  constructor
  · rintro ⟨he, ho⟩
    ext x
    simp only [LinearMap.comp_apply]
    have hx := even_add_odd R h2 x
    have hE := he _ (evenPart_isEven R hR x)
    have hO := ho _ (oddPart_isOdd R hR x)
    have hEv := evenPart_isEven R hR x
    have hOd := oddPart_isOdd R hR x
    conv_lhs => rw [← hx]
    conv_rhs => rw [← hx]
    simp only [map_add, map_neg, hEv, hOd, hE, hO]
  · intro hc
    exact ⟨fun x hx => even_preserved R M hc x hx, fun x hx => odd_preserved R M hc x hx⟩

/-- **(c2)** Non-commuting dynamics breaks parity somewhere: some even state is sent off the even
subspace, or some odd state off the odd subspace. -/
theorem not_commute_breaks_parity (R M : V →ₗ[K] V) (hR : R ∘ₗ R = LinearMap.id)
    (h2 : (2 : K) ≠ 0) (hnc : M ∘ₗ R ≠ R ∘ₗ M) :
    (∃ x, R x = x ∧ R (M x) ≠ M x) ∨ (∃ x, R x = -x ∧ R (M x) ≠ -(M x)) := by
  by_contra hcon
  rw [not_or, not_exists, not_exists] at hcon
  apply hnc
  rw [← commute_iff_preserves R M hR h2]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · by_contra h; exact hcon.1 x ⟨hx, h⟩
  · by_contra h; exact hcon.2 x ⟨hx, h⟩

end Linear

/-- **(c3)** Preserving the even subspace alone does NOT force commuting: an explicit
counterexample on `ℝ × ℝ`, `R (a,b) = (a,-b)`, `M (a,b) = (a+b, b)`. -/
theorem preserving_even_alone_insufficient :
    ∃ R M : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ), R ∘ₗ R = LinearMap.id ∧
      (∀ x, R x = x → R (M x) = M x) ∧ M ∘ₗ R ≠ R ∘ₗ M := by
  refine ⟨LinearMap.prodMap LinearMap.id (-LinearMap.id),
    (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).prod (LinearMap.snd ℝ ℝ ℝ), ?_, ?_, ?_⟩
  · ext <;> simp
  · rintro ⟨a, b⟩ h
    simp only [LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.neg_apply,
      Prod.mk.injEq] at h
    have hb : b = 0 := by linarith [h.2]
    subst hb
    simp
  · intro h
    have := LinearMap.congr_fun h ((0 : ℝ), (1 : ℝ))
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.prod_apply,
      LinearMap.id_apply, LinearMap.neg_apply] at this
    norm_num at this

/-- **(a, matrix form)** On `ℝⁿ`: if `M * R = R * M` and `R v = v`, then
`R (Mᵏ v) = Mᵏ v` for all `k`. (No involution hypothesis `R * R = 1` is needed: the statement
holds for any commuting `R`, and in particular for a mirror/parity matrix.) -/
theorem matrix_even_stays_even {n : ℕ} (R M : Matrix (Fin n) (Fin n) ℝ) (hcomm : M * R = R * M)
    (v : Fin n → ℝ) (hv : R.mulVec v = v) (k : ℕ) :
    R.mulVec ((M ^ k).mulVec v) = (M ^ k).mulVec v := by
  have hc : Commute M R := hcomm
  rw [Matrix.mulVec_mulVec, ← (hc.pow_left k).eq, ← Matrix.mulVec_mulVec, hv]

/-- Concrete instance of `matrix_even_stays_even`: the swap `R = !![0,1;1,0]` commutes with
`M = !![2,1;1,2]`, and `v = (1,1)` is swap-symmetric, so every `Mᵏ v` stays swap-symmetric. -/
example : ∀ k : ℕ, (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVec
    ((!![2, 1; 1, 2] ^ k : Matrix (Fin 2) (Fin 2) ℝ).mulVec ![1, 1]) =
    (!![2, 1; 1, 2] ^ k : Matrix (Fin 2) (Fin 2) ℝ).mulVec ![1, 1] := by
  refine matrix_even_stays_even _ _ ?_ _ ?_
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **(d) Curie's principle, group form.** If `f` commutes with every symmetry `g • ·` of a group
action, the stabilizer (symmetry group) of `x` is contained in the stabilizer of every iterate
`f^[k] x`: effects are at least as symmetric as their causes, for all time. -/
theorem stabilizer_le_iterate {G α : Type*} [Group G] [MulAction G α] (f : α → α)
    (hf : ∀ (g : G) (y : α), f (g • y) = g • f y) (x : α) (k : ℕ) :
    MulAction.stabilizer G x ≤ MulAction.stabilizer G (f^[k] x) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  have hc : Function.Commute f (fun y => g • y) := fun y => hf g y
  have h := (hc.iterate_left k) x
  simp only [hg] at h
  exact h.symm

section Nonlinear

variable {α : Type*}

/-- **(b1)** Nonlinear equivariant dynamics maps a symmetric state to a symmetric state. -/
theorem equivariant_fixed (R f : α → α) (hf : f ∘ R = R ∘ f) (x : α) (hx : R x = x) :
    R (f x) = f x := by
  have h := congrFun hf x
  simp only [Function.comp_apply] at h
  rw [← h, hx]

/-- Iterates of an equivariant map are equivariant. -/
theorem equivariant_iterate_comm (R f : α → α) (hf : f ∘ R = R ∘ f) (k : ℕ) (x : α) :
    f^[k] (R x) = R (f^[k] x) := by
  have hc : Function.Commute f R := fun y => congrFun hf y
  exact (hc.iterate_left k) x

/-- **(b2)** A symmetric initial state stays symmetric along the whole orbit. -/
theorem equivariant_iterate_fixed (R f : α → α) (hf : f ∘ R = R ∘ f) (x : α) (hx : R x = x)
    (k : ℕ) : R (f^[k] x) = f^[k] x := by
  rw [← equivariant_iterate_comm R f hf k x, hx]

/-- Concrete nonlinear instance of `equivariant_iterate_fixed`: the swap on `ℝ × ℝ` commutes
with `f (a, b) = (a * b + a ^ 3, a * b + b ^ 3)`, so the diagonal state `(2, 2)` stays on the
diagonal along its whole orbit. -/
example (k : ℕ) :
    Prod.swap ((fun p : ℝ × ℝ => (p.1 * p.2 + p.1 ^ 3, p.1 * p.2 + p.2 ^ 3))^[k] (2, 2)) =
      (fun p : ℝ × ℝ => (p.1 * p.2 + p.1 ^ 3, p.1 * p.2 + p.2 ^ 3))^[k] (2, 2) := by
  refine equivariant_iterate_fixed Prod.swap _ ?_ (2, 2) rfl k
  funext p
  simp only [Function.comp_apply, Prod.swap_prod_mk, Prod.fst_swap, Prod.snd_swap]
  ext <;> ring

end Nonlinear

end A01Curie
