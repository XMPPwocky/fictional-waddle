import Mathlib

/-!
# Not-all theorem, infinite half: a counterexample in the open sets of `ℝ`

Work in the frame `TopologicalSpace.Opens ℝ`, whose pseudocomplement is
`Uᶜ = interior (U : Set ℝ)ᶜ`. For `q : ℚ` let `U q` be the open set `ℝ \ {(q : ℝ)}`.

PROVED
* `coe_compl`: in `Opens ℝ`, the pseudocomplement of `V` is the interior of its set complement.
* `coe_iInf`: the infimum of a family in `Opens ℝ` is the interior of the intersection.
* `coe_U`: the underlying set of `U q` is `{(q : ℝ)}ᶜ`.
* `open_subset_singleton`: an open subset of `ℝ` contained in a singleton is empty.
* `U_compl`: `(U q)ᶜ = ⊥` for every `q`, i.e. each `U q` is dense.
* `U_compl_compl`: `(U q)ᶜᶜ = ⊤` for every `q`.
* `iInf_compl_compl_U`: `⨅ q, (U q)ᶜᶜ = ⊤`.
* `iInter_U`: the set-theoretic intersection `⋂ q, U q` is the set of irrational numbers.
* `interior_irrational`: the set of irrational numbers has empty interior.
* `iInf_U`: `⨅ q, U q = ⊥` in `Opens ℝ`.
* `iInf_U_compl`: `(⨅ q, U q)ᶜ = ⊤`.
* `iInf_U_compl_compl`: `(⨅ q, U q)ᶜᶜ = ⊥`.
* `bot_ne_top`: `(⊥ : Opens ℝ) ≠ ⊤`.
* `not_all`: `(⨅ q, U q)ᶜᶜ ≠ ⨅ q, (U q)ᶜᶜ`, together with `(⨅ q, U q)ᶜᶜ = ⊥`,
  `⨅ q, (U q)ᶜᶜ = ⊤` and `⊥ ≠ ⊤`: double negation does not distribute over this countable
  meet, although every single `U q` has double negation `⊤`.

INTERPRETED (not formalized)
* Reading the failure of distributivity as a "not-all" without any single exception
  (each `U q` is `¬¬`-true, the meet is not).
-/

namespace NotAllInfiniteReals

open TopologicalSpace

/-- The open set `ℝ \ {q}`. -/
def U (q : ℚ) : Opens ℝ := ⟨({(q : ℝ)}ᶜ : Set ℝ), isOpen_compl_singleton⟩

@[simp] theorem coe_U (q : ℚ) : ((U q : Opens ℝ) : Set ℝ) = ({(q : ℝ)}ᶜ : Set ℝ) := rfl

theorem coe_compl (V : Opens ℝ) : ((Vᶜ : Opens ℝ) : Set ℝ) = interior (V : Set ℝ)ᶜ :=
  Opens.coe_compl_eq_interior_compl

theorem coe_iInf {ι : Sort*} (V : ι → Opens ℝ) :
    ((⨅ i, V i : Opens ℝ) : Set ℝ) = interior (⋂ i, (V i : Set ℝ)) := by
  apply Set.Subset.antisymm
  · apply interior_maximal _ (⨅ i, V i).isOpen
    exact Set.subset_iInter fun i => (iInf_le V i : (⨅ i, V i) ≤ V i)
  · have h : Opens.interior (⋂ i, (V i : Set ℝ)) ≤ ⨅ i, V i :=
      le_iInf fun i => fun x hx => Set.mem_iInter.mp (interior_subset hx) i
    exact h

/-- A nonempty open subset of `ℝ` is not contained in a singleton. -/
theorem open_subset_singleton {W : Set ℝ} (hW : IsOpen W) (x : ℝ) (h : W ⊆ {x}) : W = ∅ := by
  have : W ⊆ interior {x} := interior_maximal h hW
  rw [interior_singleton] at this
  exact Set.subset_empty_iff.mp this

theorem U_compl (q : ℚ) : (U q)ᶜ = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  exfalso
  have hd : Disjoint (U q)ᶜ (U q) := disjoint_compl_left
  have hsub : (((U q)ᶜ : Opens ℝ) : Set ℝ) ⊆ {(q : ℝ)} := by
    intro y hy
    by_contra hne
    have hyU : y ∈ ((U q : Opens ℝ) : Set ℝ) := hne
    have : y ∈ (((U q)ᶜ ⊓ U q : Opens ℝ) : Set ℝ) := ⟨hy, hyU⟩
    rw [hd.eq_bot] at this
    exact this
  have := open_subset_singleton ((U q)ᶜ).isOpen _ hsub
  have hx' : x ∈ (((U q)ᶜ : Opens ℝ) : Set ℝ) := hx
  rw [this] at hx'
  exact hx'

theorem U_compl_compl (q : ℚ) : (U q)ᶜᶜ = ⊤ := by
  rw [U_compl, compl_bot]

theorem iInf_compl_compl_U : ⨅ q, (U q)ᶜᶜ = ⊤ := by
  simp only [U_compl_compl, iInf_top]

theorem iInter_U : (⋂ q, ((U q : Opens ℝ) : Set ℝ)) = {x : ℝ | Irrational x} := by
  ext x
  simp only [coe_U, Set.mem_iInter, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_ofPred_eq, Irrational, Set.mem_range, not_exists]
  exact ⟨fun h q hq => h q hq.symm, fun h q hq => h q hq.symm⟩

theorem interior_irrational : interior {x : ℝ | Irrational x} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨q, hq⟩ :=
    (Rat.denseRange_cast (𝕜 := ℝ)).exists_mem_open isOpen_interior ⟨x, hx⟩
  exact (interior_subset hq : Irrational (q : ℝ)) ⟨q, rfl⟩

theorem iInf_U : ⨅ q, U q = ⊥ := by
  apply SetLike.coe_injective
  rw [coe_iInf, iInter_U, interior_irrational]
  rfl

theorem iInf_U_compl : (⨅ q, U q)ᶜ = ⊤ := by
  rw [iInf_U, compl_bot]

theorem iInf_U_compl_compl : (⨅ q, U q)ᶜᶜ = ⊥ := by
  rw [iInf_U_compl, compl_top]

theorem bot_ne_top : (⊥ : Opens ℝ) ≠ ⊤ := by
  intro h
  have : (0 : ℝ) ∈ ((⊤ : Opens ℝ) : Set ℝ) := Set.mem_univ _
  rw [← h] at this
  exact this

theorem not_all :
    (⨅ q, U q)ᶜᶜ = ⊥ ∧ ⨅ q, (U q)ᶜᶜ = ⊤ ∧ (⊥ : Opens ℝ) ≠ ⊤ ∧
      (⨅ q, U q)ᶜᶜ ≠ ⨅ q, (U q)ᶜᶜ := by
  refine ⟨iInf_U_compl_compl, iInf_compl_compl_U, bot_ne_top, ?_⟩
  rw [iInf_U_compl_compl, iInf_compl_compl_U]
  exact bot_ne_top

end NotAllInfiniteReals
