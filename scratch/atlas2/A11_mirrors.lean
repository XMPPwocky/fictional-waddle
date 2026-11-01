import Mathlib

/-!
# A11 — Mirrors and handedness

## What is proved (formal content)

(a) `refl3 = diag(1,1,-1)` is orthogonal with `det refl3 = -1`; for any `n`, a product of
    two real matrices of det `-1` has det `1`, and if both are orthogonal the product is
    orthogonal with det `1` (`two_reflections_orthogonal_det_one`).

(b) Every real orthogonal matrix has det `1` or `-1`. Consequently a preconnected set of
    orthogonal matrices cannot contain both a det `+1` and a det `-1` matrix
    (`preconnected_orthogonal_det_const`, via continuity of `det` and the fact that the
    image of a preconnected set in `ℝ` is order-convex, so it would contain `0`). Corollaries:
    `O(3)` is not preconnected; no map `[0,1] → Mat₃(ℝ)` continuous on `[0,1]` with orthogonal
    values joins det `1` to det `-1`; no `Path` in the subspace `O(n)` (any `n`) joins det `1`
    to det `-1`; in particular none joins `1` to `refl3` in `O(3)`.

(c) `rot4 θ` (rotation by `θ` in the `(z,w)` coordinate plane of `ℝ⁴`) lies in `SO(4)` for
    every `θ`; `rot4 0 = 1`, `rot4 π = diag(1,1,-1,-1)` (det `1`); `θ ↦ rot4 θ` is continuous;
    on vectors with `w = 0` the matrix `rot4 π` acts as `(x,y,z,0) ↦ (x,y,-z,0)`, i.e. it
    extends `refl3` along the embedding `ℝ³ ≅ {w = 0}`; and there is a `Path` in `SO(4)`
    from `1` to `diag(1,1,-1,-1)` given by `t ↦ rot4 (π t)`, every point of which has det `1`.

(d) (Generalisation, added in review.) For any `n` and any orthogonal `A`, the block matrix
    `[[A, 0], [0, det A]]` lies in `SO(n+1)` (`orthogonal_extend_SO`). So every mirror of
    `ℝⁿ` is the restriction of an element of `SO(n+1)`. That `SO(n+1)` is path-connected,
    so that this rotation can be reached from `1`, is *not* proved here except for `n = 3`
    via the explicit path in (c).

## Interpretation (not formalised)

"Handedness" in `ℝ³` is the sign of `det`: (b) says it is a topological invariant of
continuous motions through rigid (orthogonal) maps, so a mirror image cannot be reached
from the original by a continuous rigid motion within `ℝ³`. (c) says the obstruction
disappears one dimension up: the 3D mirror is the restriction to a hyperplane slice of a
4D rotation, reachable from the identity continuously. We do *not* formalise statements
about physical objects, chirality of shapes, or that `rot4 θ` maps the slice `w = 0` to
itself for intermediate `θ` (it does not; only `θ ∈ {0, π}` preserve the slice).

## Statement changes vs `A11_mirrors.statements.lean`

None: the 23 named declarations (21 theorems, 2 defs) are verbatim identical (checked mechanically).
The adversarial reviewer added `orthogonal_extend_SO` and the closing `example`s to both
files; no existing statement was changed. During proof
work `no_path_orthogonal` was moved before `no_path_one_to_refl3` (which uses it) in both
files; no statement text changed.
-/

open Matrix Real

namespace Atlas2.A11

/-- The mirror `diag(1, 1, -1)` on `ℝ³` (reflection in the plane `z = 0`). -/
noncomputable def refl3 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 1, -1]

/-! ## (a) determinants of reflections -/

theorem refl3_mem_orthogonalGroup : refl3 ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff, refl3, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem refl3_det : refl3.det = -1 := by
  simp [refl3, Matrix.det_diagonal, Fin.prod_univ_succ]

theorem det_mul_of_det_neg_one {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : A.det = -1) (hB : B.det = -1) : (A * B).det = 1 := by
  rw [Matrix.det_mul, hA, hB]; norm_num

theorem two_reflections_orthogonal_det_one {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hAo : A ∈ Matrix.orthogonalGroup n ℝ)
    (hBo : B ∈ Matrix.orthogonalGroup n ℝ) (hA : A.det = -1) (hB : B.det = -1) :
    A * B ∈ Matrix.orthogonalGroup n ℝ ∧ (A * B).det = 1 := by
  exact ⟨Submonoid.mul_mem _ hAo hBo, det_mul_of_det_neg_one A B hA hB⟩

/-! ## (b) no continuous path from det `+1` to det `-1` inside `O(n)` -/

theorem det_orthogonal_eq_one_or_neg_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A ∈ Matrix.orthogonalGroup n ℝ) :
    A.det = 1 ∨ A.det = -1 := by
  have h := congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff n ℝ).1 hA)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  exact mul_self_eq_one_iff.1 h

/-- A preconnected set of orthogonal matrices cannot contain both a det `+1` and a
det `-1` matrix. -/
theorem preconnected_orthogonal_det_const {n : Type*} [Fintype n] [DecidableEq n]
    (S : Set (Matrix n n ℝ)) (hS : IsPreconnected S)
    (hSo : S ⊆ (Matrix.orthogonalGroup n ℝ : Set (Matrix n n ℝ)))
    {A B : Matrix n n ℝ} (hA : A ∈ S) (hB : B ∈ S) (hA1 : A.det = 1) :
    B.det ≠ -1 := by
  intro hB1
  have hc : IsPreconnected (Matrix.det '' S) :=
    hS.image _ (continuous_id.matrix_det).continuousOn
  have h0 : (0 : ℝ) ∈ Matrix.det '' S := by
    have hsub := hc.Icc_subset (Set.mem_image_of_mem _ hB) (Set.mem_image_of_mem _ hA)
    rw [hB1, hA1] at hsub
    exact hsub ⟨by norm_num, by norm_num⟩
  obtain ⟨C, hC, hC0⟩ := h0
  rcases det_orthogonal_eq_one_or_neg_one C (hSo hC) with h | h <;> rw [h] at hC0 <;> norm_num at hC0

/-- The set of orthogonal `3 × 3` matrices is not preconnected. -/
theorem orthogonal3_not_isPreconnected :
    ¬ IsPreconnected (Matrix.orthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  intro h
  exact preconnected_orthogonal_det_const _ h le_rfl (Submonoid.one_mem _)
    refl3_mem_orthogonalGroup Matrix.det_one refl3_det

/-- No map `[0,1] → Mat₃(ℝ)`, continuous on `[0,1]` with orthogonal values, joins a
det `+1` matrix to a det `-1` matrix. -/
theorem no_orthogonal_path_det_one_to_neg_one (γ : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hγ : ContinuousOn γ (Set.Icc 0 1))
    (horth : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (h0 : (γ 0).det = 1) : (γ 1).det ≠ -1 := by
  have hS : IsPreconnected (γ '' Set.Icc 0 1) := isPreconnected_Icc.image γ hγ
  refine preconnected_orthogonal_det_const _ hS ?_
    (Set.mem_image_of_mem γ (Set.left_mem_Icc.2 zero_le_one))
    (Set.mem_image_of_mem γ (Set.right_mem_Icc.2 zero_le_one)) h0
  rintro _ ⟨t, ht, rfl⟩
  exact horth t ht

/-- General form: no `Path` in `O(n)` joins a det `+1` element to a det `-1` element. -/
theorem no_path_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix.orthogonalGroup n ℝ) (hA : (A : Matrix n n ℝ).det = 1)
    (hB : (B : Matrix n n ℝ).det = -1) : IsEmpty (Path A B) := by
  refine ⟨fun p => ?_⟩
  have hS : IsPreconnected (Set.range fun t => ((p t : Matrix.orthogonalGroup n ℝ) : Matrix n n ℝ)) :=
    isPreconnected_range (continuous_subtype_val.comp p.continuous)
  refine preconnected_orthogonal_det_const _ hS ?_ ⟨0, by simp⟩ ⟨1, by simp⟩ hA hB
  rintro _ ⟨t, rfl⟩
  exact (p t).2

/-- Same statement for a `Path` in the subspace `O(3)` itself: no path in `O(3)`
joins the identity to the mirror `refl3`. -/
theorem no_path_one_to_refl3 :
    IsEmpty (Path (1 : Matrix.orthogonalGroup (Fin 3) ℝ)
      ⟨refl3, refl3_mem_orthogonalGroup⟩) := by
  exact no_path_orthogonal _ _ Matrix.det_one refl3_det

/-! ## (c) in `ℝ⁴` the mirror becomes a rotation -/

/-- Rotation by angle `θ` in the `(z, w)` plane of `ℝ⁴` (coordinates `x, y, z, w`
indexed `0, 1, 2, 3`). -/
noncomputable def rot4 (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, cos θ, -sin θ;
     0, 0, sin θ, cos θ]

theorem rot4_pi : rot4 π = Matrix.diagonal ![1, 1, -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot4]

theorem rot4_zero : rot4 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot4]

theorem rot4_det (θ : ℝ) : (rot4 θ).det = 1 := by
  simp [rot4, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem rot4_mem_orthogonalGroup (θ : ℝ) : rot4 θ ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot4, Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith [Real.sin_sq_add_cos_sq θ]

theorem rot4_mem_specialOrthogonalGroup (θ : ℝ) :
    rot4 θ ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ := by
  exact ⟨rot4_mem_orthogonalGroup θ, rot4_det θ⟩

theorem diag_pi_det : (Matrix.diagonal ![(1 : ℝ), 1, -1, -1]).det = 1 := by
  simp [Matrix.det_diagonal, Fin.prod_univ_succ]

theorem continuous_rot4 : Continuous rot4 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [rot4] <;> fun_prop

/-- On the slice `w = 0`, the rotation by `π` acts as the mirror `z ↦ -z`. -/
theorem rot4_pi_on_slice (v : Fin 4 → ℝ) (hv : v 3 = 0) :
    rot4 π *ᵥ v = ![v 0, v 1, -v 2, 0] := by
  ext i
  fin_cases i <;> simp [rot4, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hv]

/-- The same, phrased via `refl3`: embedding `ℝ³ ↪ ℝ⁴` as the slice `w = 0`
intertwines `refl3` with `rot4 π`. -/
theorem rot4_pi_extends_refl3 (u : Fin 3 → ℝ) :
    rot4 π *ᵥ ![u 0, u 1, u 2, 0] = ![(refl3 *ᵥ u) 0, (refl3 *ᵥ u) 1, (refl3 *ᵥ u) 2, 0] := by
  ext i
  fin_cases i <;> simp [rot4, refl3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.diagonal]

/-- A `Path` in `SO(4)` from the identity to `diag(1,1,-1,-1)`, given by `θ ↦ rot4 (π θ)`,
`θ ∈ [0,1]`: every point has det `1`. -/
theorem exists_path_SO4_one_to_diag :
    ∃ p : Path (1 : Matrix.specialOrthogonalGroup (Fin 4) ℝ)
        ⟨Matrix.diagonal ![1, 1, -1, -1], by
          rw [← rot4_pi]; exact rot4_mem_specialOrthogonalGroup π⟩,
      ∀ t, (p t : Matrix (Fin 4) (Fin 4) ℝ) = rot4 (π * t) ∧
        (p t : Matrix (Fin 4) (Fin 4) ℝ).det = 1 := by
  refine ⟨{ toFun := fun t => ⟨rot4 (π * t), rot4_mem_specialOrthogonalGroup _⟩,
             continuous_toFun := ?_, source' := ?_, target' := ?_ },
    fun t => ⟨rfl, rot4_det _⟩⟩
  · exact Continuous.subtype_mk
      (continuous_rot4.comp (continuous_const.mul continuous_subtype_val)) _
  · apply Subtype.ext
    simp [rot4_zero]
  · apply Subtype.ext
    simp [rot4_pi]

/-! ## Going up: every orthogonal map of `ℝⁿ` extends to a rotation of `ℝⁿ⁺¹`
(added by the adversarial reviewer) -/

/-- Generalisation of (c). For any `n` and any orthogonal `A` on `ℝⁿ`, the block matrix
`[[A, 0], [0, det A]]` on `ℝⁿ ⊕ ℝ` lies in `SO(n+1)`. When `A` is a mirror (`det A = -1`)
this is a rotation of `ℝⁿ⁺¹` that acts as `A` on the slice where the last coordinate is `0`.
That slice statement is not formalised here; `rot4_pi_on_slice` proves it for `n = 3`. -/
theorem orthogonal_extend_SO {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A ∈ Matrix.orthogonalGroup n ℝ) :
    Matrix.fromBlocks A 0 0 (Matrix.of fun (_ _ : Unit) => A.det) ∈
      Matrix.specialOrthogonalGroup (n ⊕ Unit) ℝ := by
  have hA' := (Matrix.mem_orthogonalGroup_iff n ℝ).1 hA
  have hdet : A.det * A.det = 1 := by
    have h := congrArg Matrix.det hA'
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one]
    simp only [Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hA']
    congr 1
    ext i j
    simp [Matrix.mul_apply, hdet]
  · rw [Matrix.det_fromBlocks_zero₂₁]
    simp [hdet]

/-! ## Concrete instances (reviewer sanity checks) -/

/-- (a) on `refl3` itself: `refl3 * refl3` is orthogonal with det `1`. -/
example : refl3 * refl3 ∈ Matrix.orthogonalGroup (Fin 3) ℝ ∧ (refl3 * refl3).det = 1 :=
  two_reflections_orthogonal_det_one refl3 refl3 refl3_mem_orthogonalGroup
    refl3_mem_orthogonalGroup refl3_det refl3_det

/-- (b) on a concrete map: any `γ : ℝ → Mat₃(ℝ)` continuous on `[0,1]`, orthogonal there,
starting at `1`, cannot end at `refl3`. -/
example (γ : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (hγ : ContinuousOn γ (Set.Icc 0 1))
    (horth : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (h0 : γ 0 = 1) : γ 1 ≠ refl3 := by
  intro h1
  exact no_orthogonal_path_det_one_to_neg_one γ hγ horth (by rw [h0, Matrix.det_one])
    (by rw [h1, refl3_det])

/-- The hypotheses of the path theorem are satisfiable (not vacuous): the constant map at `1`. -/
example : ContinuousOn (fun _ : ℝ => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (Set.Icc 0 1) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun _ : ℝ => (1 : Matrix (Fin 3) (Fin 3) ℝ)) t ∈
      Matrix.orthogonalGroup (Fin 3) ℝ :=
  ⟨continuousOn_const, fun _ _ => Submonoid.one_mem _⟩

/-- The generalisation applied to `refl3`: `[[refl3, 0], [0, -1]]` is a rotation of `ℝ⁴`. -/
example : Matrix.fromBlocks refl3 0 0 (Matrix.of fun (_ _ : Unit) => refl3.det) ∈
    Matrix.specialOrthogonalGroup (Fin 3 ⊕ Unit) ℝ :=
  orthogonal_extend_SO refl3 refl3_mem_orthogonalGroup

end Atlas2.A11
