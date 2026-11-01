import Mathlib

/-!
# Boundary data and the bulk it pins 

A real linear system lives on `B ⊕ I`: boundary sites `B`, interior sites `I`. Its operator `A` is
split into blocks: `A₂₂ : I × I` (interior), `A₂₁ : I × B` (boundary drives interior),
`A₁₂ : B × I` (interior read at the boundary).
-/

open Matrix

namespace BoundaryPins

variable {B I : Type*} [Fintype B] [Fintype I] [DecidableEq B] [DecidableEq I]

/-! ### Dot-product orthogonality on `I → ℝ` -/

/-- The dot product as a bilinear form. -/
noncomputable def dotB : LinearMap.BilinForm ℝ (I → ℝ) := Matrix.toBilin' 1

omit [Fintype B] [DecidableEq B] in
lemma dotB_apply (x y : I → ℝ) : dotB x y = x ⬝ᵥ y := by
  simp [dotB, Matrix.toBilin'_apply']

omit [Fintype B] [DecidableEq B] in
lemma dotB_nondeg : (dotB : LinearMap.BilinForm ℝ (I → ℝ)).Nondegenerate := by
  unfold dotB
  rw [Matrix.nondegenerate_toBilin'_iff, Matrix.nondegenerate_iff_det_ne_zero, Matrix.det_one]
  exact one_ne_zero

omit [Fintype B] [DecidableEq B] in
lemma dotB_refl : (dotB : LinearMap.BilinForm ℝ (I → ℝ)).IsRefl := by
  intro x y h
  rw [dotB_apply] at h ⊢
  rwa [dotProduct_comm]

omit [Fintype B] [DecidableEq B] in
lemma mem_perp (W : Submodule ℝ (I → ℝ)) (v : I → ℝ) :
    v ∈ dotB.orthogonal W ↔ ∀ x ∈ W, x ⬝ᵥ v = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [dotB_apply]

omit [Fintype B] [DecidableEq B] in
lemma perp_perp (W : Submodule ℝ (I → ℝ)) : dotB.orthogonal (dotB.orthogonal W) = W :=
  LinearMap.BilinForm.orthogonal_orthogonal dotB_nondeg dotB_refl W

omit [DecidableEq B] [DecidableEq I] in
lemma eq_zero_of_dot (w : I → ℝ) (h : ∀ g : I → ℝ, g ⬝ᵥ w = 0) : w = 0 :=
  dotProduct_self_eq_zero.mp (h w)

omit [DecidableEq B] [DecidableEq I] in
lemma dot_mulVec_swap {J : Type*} [Fintype J] (M : Matrix I J ℝ) (g : J → ℝ) (v : I → ℝ) :
    (M *ᵥ g) ⬝ᵥ v = g ⬝ᵥ (Mᵀ *ᵥ v) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

omit [DecidableEq B] [DecidableEq I] in
/-- The orthogonal complement of a range is the kernel of the transpose. -/
lemma le_perp_iff {J : Type*} [Fintype J] (M : Matrix I J ℝ) (v : I → ℝ) :
    (∀ g : J → ℝ, (M *ᵥ g) ⬝ᵥ v = 0) ↔ Mᵀ *ᵥ v = 0 := by
  constructor
  · intro h
    apply eq_zero_of_dot
    intro g; rw [← dot_mulVec_swap]; exact h g
  · intro h g; rw [dot_mulVec_swap, h, dotProduct_zero]

omit [Fintype B] [DecidableEq B] in
lemma blocks_symm (A : Matrix (B ⊕ I) (B ⊕ I) ℝ) (hA : A.IsSymm) :
    (A.toBlocks₂₂)ᵀ = A.toBlocks₂₂ ∧ (A.toBlocks₂₁)ᵀ = A.toBlocks₁₂ := by
  constructor
  · ext i j; simp [Matrix.toBlocks₂₂, hA.apply]
  · ext i j; simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, hA.apply]


/-- The interior operator at frequency² `z`. -/
def Lz (A : Matrix (B ⊕ I) (B ⊕ I) ℝ) (z : ℝ) : Matrix I I ℝ := A.toBlocks₂₂ - z • 1

/-- **H1.** Dirichlet problem: every boundary value `g` and interior source `f` fix exactly one
interior state iff the interior operator is nonsingular. -/
theorem dirichlet_pinned_iff (A : Matrix (B ⊕ I) (B ⊕ I) ℝ) (z : ℝ) :
    (∀ (g : B → ℝ) (f : I → ℝ), ∃! u : I → ℝ, Lz A z *ᵥ u + A.toBlocks₂₁ *ᵥ g = f) ↔
      (Lz A z).det ≠ 0 := by
  constructor
  · intro h
    have h0 : ∀ f : I → ℝ, ∃! u : I → ℝ, Lz A z *ᵥ u = f := by
      intro f; simpa [Matrix.mulVec_zero] using h 0 f
    rw [← Function.bijective_iff_existsUnique] at h0
    rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
    exact Matrix.mulVec_injective_iff_isUnit.mp h0.1
  · intro hdet g f
    have hu : IsUnit (Lz A z) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hb : Function.Bijective (Lz A z).mulVec :=
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu, Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩
    obtain ⟨u, hu1, hu2⟩ := (Function.bijective_iff_existsUnique _).mp hb (f - A.toBlocks₂₁ *ᵥ g)
    refine ⟨u, ?_, fun y hy => hu2 y (eq_sub_of_add_eq hy)⟩
    have hu1' : Lz A z *ᵥ u = f - A.toBlocks₂₁ *ᵥ g := hu1
    show Lz A z *ᵥ u + A.toBlocks₂₁ *ᵥ g = f
    rw [hu1', sub_add_cancel]

/-- **H2.** The ambiguity when pinning fails: the solutions for fixed `(g, f)` are one solution plus
the kernel, whose dimension is `|I| - rank`, not necessarily 1. -/
theorem dirichlet_ambiguity (A : Matrix (B ⊕ I) (B ⊕ I) ℝ) (z : ℝ) (g : B → ℝ) (f u₀ : I → ℝ)
    (h₀ : Lz A z *ᵥ u₀ + A.toBlocks₂₁ *ᵥ g = f) :
    {u | Lz A z *ᵥ u + A.toBlocks₂₁ *ᵥ g = f} = {u | u - u₀ ∈ LinearMap.ker (Lz A z).mulVecLin} ∧
      Module.finrank ℝ (LinearMap.ker (Lz A z).mulVecLin) = Fintype.card I - (Lz A z).rank := by
  refine ⟨?_, ?_⟩
  · ext u
    change Lz A z *ᵥ u + A.toBlocks₂₁ *ᵥ g = f ↔ u - u₀ ∈ LinearMap.ker (Lz A z).mulVecLin
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, sub_eq_zero]
    constructor
    · intro h; exact add_right_cancel (h.trans h₀.symm)
    · intro h; rw [h]; exact h₀
  · have h := LinearMap.finrank_range_add_finrank_ker (Lz A z).mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at h
    have hr : (Lz A z).rank = Module.finrank ℝ (LinearMap.range (Lz A z).mulVecLin) := rfl
    omega

/-- **H3.** Fredholm alternative with a boundary (symmetric system): the boundary can drive the
interior with arbitrary data, even at a resonance, iff every resonant mode is invisible at the
boundary. -/
theorem boundary_drives_iff_resonance_invisible (A : Matrix (B ⊕ I) (B ⊕ I) ℝ) (hA : A.IsSymm)
    (z : ℝ) :
    (∀ g : B → ℝ, ∃ u : I → ℝ, Lz A z *ᵥ u = A.toBlocks₂₁ *ᵥ g) ↔
      ∀ v : I → ℝ, Lz A z *ᵥ v = 0 → A.toBlocks₁₂ *ᵥ v = 0 := by
  obtain ⟨h22, h21⟩ := blocks_symm A hA
  have hL : (Lz A z)ᵀ = Lz A z := by
    simp [Lz, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, h22]
  have hperp : dotB.orthogonal (LinearMap.range (Lz A z).mulVecLin) =
      LinearMap.ker (Lz A z).mulVecLin := by
    ext v
    rw [mem_perp, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · intro h
      rw [← hL]; exact (le_perp_iff _ v).mp (fun g => h _ ⟨g, rfl⟩)
    · rintro h x ⟨g, rfl⟩
      rw [Matrix.mulVecLin_apply]
      exact (le_perp_iff _ v).mpr (by rw [hL]; exact h) g
  have hpp := perp_perp (LinearMap.range (Lz A z).mulVecLin)
  rw [hperp] at hpp
  have hrange : ∀ x : I → ℝ, (∃ u, Lz A z *ᵥ u = x) ↔ ∀ v, Lz A z *ᵥ v = 0 → x ⬝ᵥ v = 0 := by
    intro x
    constructor
    · rintro ⟨u, rfl⟩ v hv
      have hmem : Lz A z *ᵥ u ∈ dotB.orthogonal (LinearMap.ker (Lz A z).mulVecLin) := by
        rw [hpp]; exact ⟨u, rfl⟩
      rw [mem_perp] at hmem
      rw [dotProduct_comm]
      exact hmem v (by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hv)
    · intro h
      have hmem : x ∈ dotB.orthogonal (LinearMap.ker (Lz A z).mulVecLin) := by
        rw [mem_perp]; intro y hy; rw [dotProduct_comm]
        exact h y (by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy; exact hy)
      rw [hpp] at hmem
      obtain ⟨u, hu⟩ := hmem
      exact ⟨u, hu⟩
  constructor
  · intro hd v hv
    rw [← h21, ← le_perp_iff]
    intro g
    exact (hrange _).mp (hd g) v hv
  · intro hv g
    refine (hrange _).mpr ?_
    intro v hv0
    exact (le_perp_iff _ v).mpr (by rw [h21]; exact hv v hv0) g

/-- The interior states the boundary can reach by driving. -/
def reach (A : Matrix (B ⊕ I) (B ⊕ I) ℝ) : Submodule ℝ (I → ℝ) :=
  ⨆ k : ℕ, LinearMap.range ((A.toBlocks₂₂ ^ k * A.toBlocks₂₁).mulVecLin)

/-- The interior states the boundary can never see: zero boundary reading at every time step. -/
def hidden (A : Matrix (B ⊕ I) (B ⊕ I) ℝ) : Submodule ℝ (I → ℝ) :=
  ⨅ k : ℕ, LinearMap.ker ((A.toBlocks₁₂ * A.toBlocks₂₂ ^ k).mulVecLin)

/-- **H4.** The count (symmetric system): the reachable interior is exactly the orthogonal
complement of the hidden interior, so `dim reachable + dim hidden = |I|`. -/
theorem reach_perp_hidden (A : Matrix (B ⊕ I) (B ⊕ I) ℝ) (hA : A.IsSymm) :
    (∀ x : I → ℝ, x ∈ reach A ↔ ∀ v ∈ hidden A, x ⬝ᵥ v = 0) ∧
      Module.finrank ℝ (reach A) + Module.finrank ℝ (hidden A) = Fintype.card I := by
  obtain ⟨h22, h21⟩ := blocks_symm A hA
  have hT : ∀ k : ℕ, (A.toBlocks₂₂ ^ k * A.toBlocks₂₁)ᵀ = A.toBlocks₁₂ * A.toBlocks₂₂ ^ k := by
    intro k; rw [Matrix.transpose_mul, Matrix.transpose_pow, h22, h21]
  have hperp : dotB.orthogonal (reach A) = hidden A := by
    ext v
    rw [mem_perp, hidden, Submodule.mem_iInf]
    constructor
    · intro h k
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← hT]
      exact (le_perp_iff _ v).mp (fun g => h _ (Submodule.mem_iSup_of_mem k ⟨g, rfl⟩))
    · intro h x hx
      have hle : reach A ≤ LinearMap.ker (dotB.flip v) := by
        apply iSup_le; intro k
        rintro _ ⟨g, rfl⟩
        rw [LinearMap.mem_ker]
        change dotB ((A.toBlocks₂₂ ^ k * A.toBlocks₂₁) *ᵥ g) v = 0
        rw [dotB_apply]
        have hk := h k
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← hT] at hk
        exact (le_perp_iff _ v).mpr hk g
      have h' : dotB x v = 0 := hle hx
      rwa [dotB_apply] at h'
  constructor
  · intro x
    rw [← hperp]
    constructor
    · intro hx v hv
      rw [mem_perp] at hv
      exact hv x hx
    · intro h
      rw [← perp_perp (reach A), mem_perp]
      intro y hy; rw [dotProduct_comm]; exact h y hy
  · rw [← hperp, LinearMap.BilinForm.finrank_orthogonal dotB_nondeg, Module.finrank_fintype_fun_eq_card]
    have := Submodule.finrank_le (reach A)
    rw [Module.finrank_fintype_fun_eq_card] at this
    omega

/-- **H5.** `|I|` steps suffice (Cayley–Hamilton): the reachable interior is the span of the first
`|I|` driving steps. -/
theorem reach_eq_finite (A : Matrix (B ⊕ I) (B ⊕ I) ℝ) :
    reach A = ⨆ k : Fin (Fintype.card I),
      LinearMap.range ((A.toBlocks₂₂ ^ (k : ℕ) * A.toBlocks₂₁).mulVecLin) := by
  apply le_antisymm
  · apply iSup_le; intro k
    rcases isEmpty_or_nonempty I with hI | hI
    · intro x _
      rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _
    · rintro _ ⟨g, rfl⟩
      have h1 : (A.toBlocks₂₂).charpoly ≠ 1 := by
        intro h
        have hd := (A.toBlocks₂₂).charpoly_natDegree_eq_dim
        rw [h, Polynomial.natDegree_one] at hd
        exact (Fintype.card_pos (α := I)).ne' hd.symm
      have hdeg : (Polynomial.X ^ k %ₘ (A.toBlocks₂₂).charpoly).natDegree < Fintype.card I := by
        have := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ k) (A.toBlocks₂₂).charpoly_monic h1
        rwa [(A.toBlocks₂₂).charpoly_natDegree_eq_dim] at this
      rw [Matrix.mulVecLin_apply, (A.toBlocks₂₂).pow_eq_aeval_mod_charpoly k,
        Polynomial.aeval_eq_sum_range' hdeg, Matrix.sum_mul, Matrix.sum_mulVec]
      apply Submodule.sum_mem
      intro i hi
      rw [Matrix.smul_mul, Matrix.smul_mulVec]
      apply Submodule.smul_mem
      exact Submodule.mem_iSup_of_mem (⟨i, Finset.mem_range.mp hi⟩ : Fin (Fintype.card I)) ⟨g, rfl⟩
  · apply iSup_le; intro k
    exact le_iSup (fun j : ℕ => LinearMap.range ((A.toBlocks₂₂ ^ j * A.toBlocks₂₁).mulVecLin)) (k : ℕ)

/-- **H6.** One-dimensional holography: a chain read at one end has no hidden interior. A tridiagonal
interior with nonzero couplings between neighbours, read through a single boundary functional `c`
that touches only site 0, is fully determined: a state with zero reading at every step is zero. -/
theorem chain_end_sees_all {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (htri : ∀ i j : Fin n, (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i → J i j = 0)
    (hnbr : ∀ i j : Fin n, (j : ℕ) = i + 1 → J i j ≠ 0)
    (hc : ∀ i : Fin n, c i ≠ 0 ↔ (i : ℕ) = 0) (v : Fin n → ℝ)
    (hv : ∀ k : ℕ, c ⬝ᵥ (J ^ k *ᵥ v) = 0) : v = 0 := by
  have key : ∀ k : ℕ, ∀ j : Fin n,
      (k < (j : ℕ) → (c ᵥ* J ^ k) j = 0) ∧ ((j : ℕ) = k → (c ᵥ* J ^ k) j ≠ 0) := by
    intro k
    induction k with
    | zero =>
      intro j
      rw [pow_zero, Matrix.vecMul_one]
      refine ⟨fun h => ?_, fun h => (hc j).mpr h⟩
      by_contra hne
      have := (hc j).mp hne
      omega
    | succ k ih =>
      intro j
      have hstep : (c ᵥ* J ^ (k + 1)) j = ∑ i, (c ᵥ* J ^ k) i * J i j := by
        rw [pow_succ, ← Matrix.vecMul_vecMul]; rfl
      rw [hstep]
      constructor
      · intro hj
        apply Finset.sum_eq_zero
        intro i _
        by_cases hik : k < (i : ℕ)
        · rw [(ih i).1 hik, zero_mul]
        · rw [htri i j (Or.inl (by omega)), mul_zero]
      · intro hj
        have hk : k < n := by have := j.isLt; omega
        rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin n)]
        · exact mul_ne_zero ((ih _).2 rfl) (hnbr _ _ (by simp only [Fin.val_mk]; exact hj))
        · intro i _ hi
          by_cases hik : k < (i : ℕ)
          · rw [(ih i).1 hik, zero_mul]
          · have hlt : (i : ℕ) < k := by
              rcases Nat.lt_or_ge (i : ℕ) k with h | h
              · exact h
              · exfalso; apply hi; ext; simp only [Fin.val_mk]; omega
            rw [htri i j (Or.inl (by omega)), mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
  have hv' : ∀ k : ℕ, (c ᵥ* J ^ k) ⬝ᵥ v = 0 := by
    intro k; rw [← Matrix.dotProduct_mulVec]; exact hv k
  have claim : ∀ m : ℕ, ∀ j : Fin n, (j : ℕ) = m → v j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
      intro j hj
      have h0 := hv' m
      rw [dotProduct, Finset.sum_eq_single j] at h0
      · exact (mul_eq_zero.mp h0).resolve_left ((key m j).2 hj)
      · intro i _ hij
        by_cases him : m < (i : ℕ)
        · rw [(key m i).1 him, zero_mul]
        · have hlt : (i : ℕ) < m := by
            rcases Nat.lt_or_ge (i : ℕ) m with h | h
            · exact h
            · exfalso; apply hij; ext; omega
          rw [ihm i hlt i rfl, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  funext j
  exact claim j j rfl

/-- **H7.** Symmetry hides bulk: if a relabelling `σ` of the interior commutes with the interior
operator and leaves the boundary reading unchanged, every state that `σ` flips in sign is invisible
at every step. -/
theorem odd_modes_hidden (A : Matrix (B ⊕ I) (B ⊕ I) ℝ) (σ : Equiv.Perm I)
    (hcomm : ∀ i j, A.toBlocks₂₂ (σ i) (σ j) = A.toBlocks₂₂ i j)
    (hread : ∀ b i, A.toBlocks₁₂ b (σ i) = A.toBlocks₁₂ b i)
    (v : I → ℝ) (hodd : ∀ i, v (σ i) = -v i) : v ∈ hidden A := by
  have step : ∀ w : I → ℝ, (∀ i, w (σ i) = -w i) →
      ∀ i, (A.toBlocks₂₂ *ᵥ w) (σ i) = -(A.toBlocks₂₂ *ᵥ w) i := by
    intro w hw i
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_neg_distrib]
    refine (Fintype.sum_equiv σ _ _ (fun x => ?_)).symm
    rw [hcomm, hw, mul_neg]
  have read0 : ∀ w : I → ℝ, (∀ i, w (σ i) = -w i) → A.toBlocks₁₂ *ᵥ w = 0 := by
    intro w hw
    funext b
    have h : (A.toBlocks₁₂ *ᵥ w) b = -(A.toBlocks₁₂ *ᵥ w) b := by
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_neg_distrib]
      exact Fintype.sum_equiv σ _ _ (fun x => by rw [hread, hw, mul_neg, neg_neg])
    rw [Pi.zero_apply]
    linarith
  have hall : ∀ k : ℕ, ∀ i, (A.toBlocks₂₂ ^ k *ᵥ v) (σ i) = -(A.toBlocks₂₂ ^ k *ᵥ v) i := by
    intro k
    induction k with
    | zero => intro i; rw [pow_zero, Matrix.one_mulVec]; exact hodd i
    | succ k ih => intro i; rw [pow_succ', ← Matrix.mulVec_mulVec]; exact step _ ih i
  rw [hidden, Submodule.mem_iInf]
  intro k
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
  exact read0 _ (hall k)

end BoundaryPins
