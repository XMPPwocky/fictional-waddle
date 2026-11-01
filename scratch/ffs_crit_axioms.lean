import BoundaryTheorem.Factored
open BoundaryTheorem.Factored

-- Critic's own axiom audit (round 1). Every main theorem of Factored.lean.
#print axioms determines_history
#print axioms history_subset_of_determines
#print axioms determines_iff
#print axioms history_eq_of_isLeast
#print axioms history_congr
#print axioms FFS.gdetermines_iff
#print axioms FFS.isHistory_ghistory
#print axioms FFS.isHistory_iff
#print axioms prodFFS
#print axioms prodFFS_gdetermines_iff
#print axioms prodFFS_ghistory
#print axioms history_proj
#print axioms afterDice_iff_before
#print axioms indep_of_not_mem_history
#print axioms Q_eq_of_indep
#print axioms exists_posWeights_not_indep
#print axioms mem_history_iff_exists_dep
#print axioms not_mem_history_iff_forall_indep
#print axioms xorY_dependsOn
#print axioms xorY_indep
#print axioms mem_history_iff_partial_ne_zero
#print axioms not_dependsOn_of_partial_eq_zero
#print axioms freeze_linSlot
#print axioms afterDice_linSlot_iff
#print axioms bridge_linear_iff
#print axioms credit_eq_zero_of_not_afterDice
#print axioms credit_eq_zero_iff_of_afterDice
#print axioms isKantian_freeze_iff
#print axioms conservative_freeze
#print axioms kantianCredit_eq_zero_of_not_afterDice
#print axioms afterDice_iff_exists_kantianCredit_ne_zero
#print axioms kantianCredit_linSlot

-- Signatures, to compare with the docs and with Causal.linear_iff.
#check @bridge_linear_iff
#check @BoundaryTheorem.Causal.linear_iff
#check @mem_history_iff_exists_dep
#check @mem_history_iff_partial_ne_zero
#check @FFS.isHistory_iff
#check @prodFFS_ghistory

-- Non-vacuity probes.
-- (a) With zero weights `Indep` holds trivially (prob = 0/0 = 0): so the ∀-direction over ALL p is not
--     vacuous-by-contradiction but it does include degenerate p; the ∃-direction restricts to PosWeights.
example {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)] (d : ι)
    (Y : (∀ i, α i) → Bool) : Indep (fun _ _ => (0 : ℝ)) Y d := by
  intro y a
  simp [prob, mass, wt, Fintype.card_ne_zero]

-- (b) An empty factor makes every history empty (no configuration exists).
example {ι : Type} [Fintype ι] [DecidableEq ι] (Y : (∀ _ : ι, Empty) → Bool) : history Y = ∅ := by
  ext i
  simp only [mem_history, BoundaryTheorem.Factored.DependsOn, Finset.notMem_empty, iff_false]
  rintro ⟨ω, _, _, _⟩
  exact (ω i).elim

-- (c) The hypotheses of `bridge_linear_iff` are jointly satisfiable: dice factor ℝ², two slots.
example : ∃ (E : Fin 2 → Type) (_ : ∀ i, NormedAddCommGroup (E i)) (_ : ∀ i, NormedSpace ℝ (E i))
    (_ : FiniteDimensional ℝ (E 0)) (_ : Nontrivial (E 0)), 2 ≤ Module.finrank ℝ (E 0) :=
  ⟨fun _ => Fin 2 → ℝ, inferInstance, inferInstance, inferInstance, inferInstance, by simp⟩

-- (d) The XOR counterexample really is a PosWeights distribution.
example : PosWeights (α := fun _ : Bool => Bool) (fun _ _ => (1 : ℝ)) := fun _ _ => one_pos

-- (e) The bridge is literally Causal.linear_iff on the frozen world: check the field expression unifies.
example {ι : Type} [Fintype ι] [DecidableEq ι] {E : ι → Type} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] {N K : Type} [Fintype N] [DecidableEq N] [Fintype K] (d : ι)
    (r : N → ℝ) (b : N → (∀ i, E i) → E d) (hb : ∀ j, ¬ BoundaryTheorem.Factored.DependsOn (b j) d) (ω : ∀ i, E i)
    (a : N → K → ℝ) (R : K → (N → E d) → ℝ) :
    BoundaryTheorem.Causal.causalField (freeze d ω (linSlot d r b)) (BoundaryTheorem.Causal.scalarA a) R =
      BoundaryTheorem.Causal.causalField (BoundaryTheorem.Causal.linResp r fun j => b j ω)
        (BoundaryTheorem.Causal.scalarA a) R := by
  rw [freeze_linSlot d r b hb ω]
