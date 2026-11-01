import Mathlib
import BoundaryTheorem.Causal

/-!
# Kin = the slots after the dice factor (finite factored sets)

Source: Garrabrant, *Temporal Inference with Finite Factored Sets* (arXiv 2109.11513), connected to the Kantian
learner of `BoundaryTheorem/Causal.lean`.

A finite factored set presents a sample space as a product `Ω = Π i, α i` of *factors*. A variable `Y : Ω → β`
has a **history** `h(Y)`: the smallest set of factors that determines it. "`X` is before `Y`" means
`h(X) ⊆ h(Y)`. We single out one factor `d`, the **dice**: the randomisation of my policy. The claim this file
proves, in four presentations, is that *kin* — the slots the Kantian learner credits — are exactly the slots
whose state is **after the dice**, `d ∈ h(x_j)`, weighted by the derivative of the slot's state along the dice:

* (1) **Product presentation.** `DependsOn Y i` (some pair differing only in coordinate `i` separates `Y`),
  `Determines S Y`, `history Y := {i | DependsOn Y i}`. `determines_history` and `history_subset_of_determines`:
  `history Y` is the unique smallest determining set (`history_eq_of_isLeast`). Garrabrant's own definition (a set
  with a family of partitions whose canonical map to the product of the quotients is a bijection; `h(X)` = the
  smallest determining subfamily) is formalised as `FFS` and shown to agree: `FFS.isHistory_iff`,
  `prodFFS_ghistory`.
* (2) **Time.** `Before X Y := history X ⊆ history Y`; `AfterDice d Y := d ∈ history Y`, which equals
  "the coordinate projection `ω ↦ ω d` is before `Y`" when `α d` is nontrivial (`afterDice_iff_before`).
* (3) **Probabilistic** (finite factors). `indep_of_not_mem_history`: `d ∉ h(Y)` ⟹ `Y ⊥ ω_d` under *every*
  product distribution. `mem_history_iff_exists_dep`: `d ∈ h(Y)` ⟺ some full-support product distribution makes
  `Y` and `ω_d` dependent. **The sharper "⟺ dependent under a fixed full-support product distribution" is
  false**: `xorY_dependsOn`/`xorY_indep` (XOR of two uniform bits depends on each bit yet is independent of it).
* (4) **Continuous.** For normed factors and differentiable `Y`: `d ∈ h(Y)` ⟺ the partial derivative of `Y` along
  the dice factor is nonzero somewhere (`mem_history_iff_partial_ne_zero`); the ⟸ of "zero partial everywhere
  ⟹ no dependence" is the mean value theorem along the `d`-line (`is_const_of_fderiv_eq_zero`).
* (5) **Bridge to `Causal.lean`.** The world is `Ω = Π i, E i` with the dice factor `E d = V` (my policy) and
  the other factors frozen at `ω`. For linear-in-dice slots `x_j(ω) = r_j • ω_d + b_j(other)`:
  `afterDice_linSlot_iff : d ∈ h(x_j) ↔ r_j ≠ 0`, and `bridge_linear_iff` restates `Causal.linear_iff`: the field
  is conservative for every C² family ⟺ credits `a_{jk} = c_k r_j`, which vanish off the after-dice set
  (`credit_eq_zero_of_not_afterDice`, `credit_eq_zero_iff_of_afterDice`). For general differentiable slots the
  Kantian credit is `c_k • ∂_d x_j`, and its support is the after-dice set (`afterDice_iff_exists_kantianCredit_ne_zero`,
  `kantianCredit_eq_zero_of_not_afterDice`).
-/

open Finset
open BoundaryTheorem.Potential

namespace BoundaryTheorem.Factored

set_option linter.unusedSectionVars false

/-! ## (1) The product presentation: dependence, determination, history -/

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} {β γ : Type*}

/-- `Y` depends on factor `i`: two configurations that differ only in coordinate `i` give different values of
`Y`. -/
def DependsOn (Y : (∀ i, α i) → β) (i : ι) : Prop :=
  ∃ ω ω' : ∀ i, α i, (∀ j, j ≠ i → ω j = ω' j) ∧ Y ω ≠ Y ω'

theorem not_dependsOn_iff {Y : (∀ i, α i) → β} {i : ι} :
    ¬ DependsOn Y i ↔ ∀ ω ω' : ∀ i, α i, (∀ j, j ≠ i → ω j = ω' j) → Y ω = Y ω' := by
  unfold DependsOn
  push Not
  rfl

/-- The factors in `S` determine `Y`: configurations agreeing on `S` give the same value of `Y`. -/
def Determines (S : Finset ι) (Y : (∀ i, α i) → β) : Prop :=
  ∀ ω ω' : ∀ i, α i, (∀ j ∈ S, ω j = ω' j) → Y ω = Y ω'

theorem Determines.mono {S T : Finset ι} {Y : (∀ i, α i) → β} (hST : S ⊆ T) (h : Determines S Y) :
    Determines T Y :=
  fun ω ω' hω => h ω ω' fun j hj => hω j (hST hj)

open Classical in
/-- The history of `Y`: the set of factors `Y` depends on. The theorems below show it is the unique smallest set
of factors determining `Y`, i.e. Garrabrant's `h(Y)` in the product presentation. -/
noncomputable def history (Y : (∀ i, α i) → β) : Finset ι := univ.filter (DependsOn Y)

theorem mem_history {Y : (∀ i, α i) → β} {i : ι} : i ∈ history Y ↔ DependsOn Y i := by
  simp [history]

/-- The configuration that takes `ω'` on the factors in `T` and `ω` elsewhere. -/
def hybrid (ω ω' : ∀ i, α i) (T : Finset ι) : ∀ i, α i := fun j => if j ∈ T then ω' j else ω j

theorem hybrid_empty (ω ω' : ∀ i, α i) : hybrid ω ω' ∅ = ω := by
  funext j
  simp [hybrid]

theorem hybrid_insert_agree (ω ω' : ∀ i, α i) (T : Finset ι) (i : ι) :
    ∀ j, j ≠ i → hybrid ω ω' (insert i T) j = hybrid ω ω' T j := by
  intro j hj
  simp [hybrid, hj]

/-- **The history determines `Y`.** Two configurations agreeing on every factor `Y` depends on give the same
value: move from one to the other one factor at a time, each step changing a factor `Y` does not depend on. -/
theorem determines_history (Y : (∀ i, α i) → β) : Determines (history Y) Y := by
  intro ω ω' h
  have key : ∀ T : Finset ι, (∀ i ∈ T, ¬ DependsOn Y i) → Y (hybrid ω ω' T) = Y ω := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; rw [hybrid_empty]
    | insert i T hi ih =>
      intro hT
      have h1 : ¬ DependsOn Y i := hT i (mem_insert_self i T)
      rw [not_dependsOn_iff] at h1
      rw [h1 _ _ (hybrid_insert_agree ω ω' T i)]
      exact ih fun j hj => hT j (mem_insert_of_mem hj)
  have hfull : hybrid ω ω' (history Y)ᶜ = ω' := by
    funext j
    by_cases hj : j ∈ history Y
    · simp [hybrid, hj, h j hj]
    · simp [hybrid, hj]
  rw [← hfull]
  exact (key (history Y)ᶜ fun i hi => by simpa [mem_history] using hi).symm

/-- **The history is contained in every determining set.** -/
theorem history_subset_of_determines {S : Finset ι} {Y : (∀ i, α i) → β} (h : Determines S Y) :
    history Y ⊆ S := by
  intro i hi
  obtain ⟨ω, ω', hoff, hne⟩ := mem_history.1 hi
  by_contra hiS
  exact hne (h ω ω' fun j hj => hoff j fun hji => hiS (hji ▸ hj))

/-- A set of factors determines `Y` iff it contains the history. -/
theorem determines_iff {S : Finset ι} {Y : (∀ i, α i) → β} : Determines S Y ↔ history Y ⊆ S :=
  ⟨history_subset_of_determines, fun hS => (determines_history Y).mono hS⟩

/-- **Uniqueness.** Any smallest determining set is the history. -/
theorem history_eq_of_isLeast {H : Finset ι} {Y : (∀ i, α i) → β} (hH : Determines H Y)
    (hmin : ∀ S, Determines S Y → H ⊆ S) : H = history Y :=
  Subset.antisymm (hmin _ (determines_history Y)) (history_subset_of_determines hH)

/-- The history depends only on the partition of `Ω` induced by `Y` (its fibres), not on the values. -/
theorem history_congr {Y : (∀ i, α i) → β} {Y' : (∀ i, α i) → γ}
    (h : ∀ ω ω', Y ω = Y ω' ↔ Y' ω = Y' ω') : history Y = history Y' := by
  ext i
  simp only [mem_history, DependsOn, ne_eq, h]

end Product

/-! ## (1') Garrabrant's own definitions, and their agreement with the product presentation -/

section Garrabrant

variable {S : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A finite factored set** (Garrabrant, Def. of "factored set", indexed form): a set `S` with a family of
partitions `fac i` (modelled as setoids; a setoid is the same data as a partition into nonempty parts), such that
the canonical map `s ↦ (part of s in each factor)` is a bijection `S ≃ Π i, (parts of factor i)`.
Garrabrant takes a *set* `B` of partitions; an indexed family is slightly more general (a nontrivial partition
cannot be listed twice without breaking the bijection, and a trivial one is harmless). -/
structure FFS (S : Type*) (ι : Type*) where
  /-- The factors. -/
  fac : ι → Setoid S
  /-- The canonical map to the product of the factors is a bijection. -/
  bij : Function.Bijective fun (s : S) (i : ι) => Quotient.mk (fac i) s

namespace FFS

variable (F : FFS S ι)

/-- The bijection with the product presentation. -/
noncomputable def equiv : S ≃ ∀ i, Quotient (F.fac i) := Equiv.ofBijective _ F.bij

theorem equiv_apply (s : S) (i : ι) : F.equiv s i = Quotient.mk (F.fac i) s := rfl

/-- Garrabrant's "`X` is determined by the factors in `C`": if `s, t` lie in the same part of every factor in `C`,
they lie in the same part of `X`. -/
def GDetermines (C : Finset ι) (X : Setoid S) : Prop :=
  ∀ s t : S, (∀ i ∈ C, F.fac i s t) → X s t

/-- Garrabrant's history `h(X)`: a set of factors `H` that determines `X` and is contained in every set of factors
that determines `X` (the smallest determining set). -/
def IsHistory (X : Setoid S) (H : Finset ι) : Prop :=
  F.GDetermines H X ∧ ∀ C, F.GDetermines C X → H ⊆ C

/-- The partition `X`, transported along the bijection to a variable on the product presentation. -/
noncomputable def pres (X : Setoid S) : (∀ i, Quotient (F.fac i)) → Quotient X :=
  fun ω => Quotient.mk X (F.equiv.symm ω)

/-- Garrabrant's determination is determination in the product presentation. -/
theorem gdetermines_iff (C : Finset ι) (X : Setoid S) :
    F.GDetermines C X ↔ Determines C (F.pres X) := by
  constructor
  · intro h ω ω' hC
    apply Quotient.sound
    apply h
    intro i hi
    apply Quotient.exact (s := F.fac i)
    rw [← F.equiv_apply, ← F.equiv_apply, F.equiv.apply_symm_apply, F.equiv.apply_symm_apply]
    exact hC i hi
  · intro h s t hC
    have := h (F.equiv s) (F.equiv t) fun i hi => by
      rw [F.equiv_apply, F.equiv_apply]
      exact Quotient.sound (hC i hi)
    simp only [pres, Equiv.symm_apply_apply] at this
    exact Quotient.exact this

/-- Garrabrant's history, computed in the product presentation. -/
noncomputable def ghistory (X : Setoid S) : Finset ι := history (F.pres X)

/-- **Garrabrant's history exists** and is `history` of the transported variable. -/
theorem isHistory_ghistory (X : Setoid S) : F.IsHistory X (F.ghistory X) :=
  ⟨(F.gdetermines_iff _ X).2 (determines_history _),
    fun C hC => history_subset_of_determines ((F.gdetermines_iff C X).1 hC)⟩

/-- **Garrabrant's history is unique** and agrees with the product presentation. -/
theorem isHistory_iff (X : Setoid S) (H : Finset ι) : F.IsHistory X H ↔ H = F.ghistory X := by
  constructor
  · rintro ⟨hH, hmin⟩
    exact history_eq_of_isLeast ((F.gdetermines_iff H X).1 hH)
      fun C hC => hmin C ((F.gdetermines_iff C X).2 hC)
  · rintro rfl
    exact F.isHistory_ghistory X

end FFS

/-- The product `Π i, α i` with its coordinate partitions is a finite factored set. -/
def prodFFS (α : ι → Type*) : FFS (∀ i, α i) ι where
  fac i := Setoid.ker fun ω => ω i
  bij := by
    constructor
    · intro ω ω' h
      funext i
      exact Quotient.exact (congrFun h i)
    · intro q
      refine ⟨fun i => (q i).out i, ?_⟩
      funext i
      conv_rhs => rw [← Quotient.out_eq (q i)]
      exact Quotient.sound rfl

/-- On the product factored set, Garrabrant's determination of the partition induced by `Y` is `Determines`. -/
theorem prodFFS_gdetermines_iff {α : ι → Type*} {β : Type*} (C : Finset ι) (Y : (∀ i, α i) → β) :
    (prodFFS α).GDetermines C (Setoid.ker Y) ↔ Determines C Y :=
  Iff.rfl

/-- **Garrabrant's `h(Y)` on the product factored set is `history Y`.** -/
theorem prodFFS_ghistory {α : ι → Type*} {β : Type*} (Y : (∀ i, α i) → β) :
    (prodFFS α).ghistory (Setoid.ker Y) = history Y :=
  history_eq_of_isLeast ((prodFFS_gdetermines_iff _ Y).1 ((prodFFS α).isHistory_ghistory _).1)
    fun C hC => ((prodFFS α).isHistory_ghistory _).2 C ((prodFFS_gdetermines_iff C Y).2 hC)

end Garrabrant

/-! ## (2) Time: "before", and "after the dice" -/

section Time

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} {β γ δ : Type*}

/-- Garrabrant's time: `X` is (weakly) before `Y` when its history is contained in the history of `Y`. -/
def Before (X : (∀ i, α i) → β) (Y : (∀ i, α i) → γ) : Prop := history X ⊆ history Y

theorem before_refl (X : (∀ i, α i) → β) : Before X X := Subset.refl _

theorem before_trans {X : (∀ i, α i) → β} {Y : (∀ i, α i) → γ} {Z : (∀ i, α i) → δ}
    (h1 : Before X Y) (h2 : Before Y Z) : Before X Z := Subset.trans h1 h2

/-- The coordinate projection onto factor `d`. -/
def proj (d : ι) : (∀ i, α i) → α d := fun ω => ω d

theorem history_proj_subset (d : ι) : history (proj d : (∀ i, α i) → α d) ⊆ {d} := by
  intro i hi
  obtain ⟨ω, ω', hoff, hne⟩ := mem_history.1 hi
  rw [mem_singleton]
  by_contra hid
  exact hne (hoff d (Ne.symm hid))

/-- The history of the coordinate projection onto a nontrivial factor is that factor. -/
theorem history_proj [∀ i, Nonempty (α i)] (d : ι) [Nontrivial (α d)] :
    history (proj d : (∀ i, α i) → α d) = {d} := by
  refine Subset.antisymm (history_proj_subset d) ?_
  rw [singleton_subset_iff, mem_history]
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (α d)
  let ω := Classical.arbitrary (∀ i, α i)
  refine ⟨Function.update ω d x, Function.update ω d y, fun j hj => ?_, ?_⟩
  · simp [Function.update_of_ne hj]
  · simpa [proj] using hxy

/-- `Y` is after the dice factor `d`: the dice is one of the factors `Y` depends on. -/
def AfterDice (d : ι) (Y : (∀ i, α i) → β) : Prop := d ∈ history Y

/-- "After the dice" is "the dice coordinate is before `Y`" (for a nontrivial dice factor). -/
theorem afterDice_iff_before [∀ i, Nonempty (α i)] (d : ι) [Nontrivial (α d)] (Y : (∀ i, α i) → β) :
    AfterDice d Y ↔ Before (proj d) Y := by
  unfold AfterDice Before
  rw [history_proj, singleton_subset_iff]

end Time

/-! ## (3) Probabilistic: the one-factor slice of the fundamental theorem -/

section Prob

open Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} {β : Type*} [∀ i, Fintype (α i)] (d : ι)

/-- The weight of a configuration under the product of the factor weights `p i`. -/
noncomputable def wt (p : ∀ i, α i → ℝ) (ω : ∀ i, α i) : ℝ := ∏ i, p i (ω i)

/-- The (unnormalised) mass of an event. -/
noncomputable def mass (p : ∀ i, α i → ℝ) (A : (∀ i, α i) → Prop) : ℝ :=
  ∑ ω, if A ω then wt p ω else 0

/-- The probability of an event under the normalised product distribution. -/
noncomputable def prob (p : ∀ i, α i → ℝ) (A : (∀ i, α i) → Prop) : ℝ :=
  mass p A / mass p fun _ => True

/-- `Y` is independent of the coordinate `ω d`: the product rule holds for every pair of values. -/
def Indep (p : ∀ i, α i → ℝ) (Y : (∀ i, α i) → β) (d : ι) : Prop :=
  ∀ (y : β) (a : α d),
    prob p (fun ω => Y ω = y ∧ ω d = a) = prob p (fun ω => Y ω = y) * prob p (fun ω => ω d = a)

/-- A product distribution with full support: every factor weight is positive. -/
def PosWeights (p : ∀ i, α i → ℝ) : Prop := ∀ i a, 0 < p i a

/-- The configurations of the factors other than `d`. -/
abbrev Rest (α : ι → Type*) (d : ι) := ∀ j : {j // j ≠ d}, α j

/-- The weight of the factors other than `d`. -/
noncomputable def wt' (p : ∀ i, α i → ℝ) (r : Rest α d) : ℝ := ∏ j : {j // j ≠ d}, p j (r j)

theorem symm_apply_self (a : α d) (r : Rest α d) : (Equiv.piSplitAt d α).symm (a, r) d = a := by simp

theorem symm_apply_ne (a : α d) (r : Rest α d) {j : ι} (hj : j ≠ d) :
    (Equiv.piSplitAt d α).symm (a, r) j = r ⟨j, hj⟩ := by simp [hj]

theorem wt_symm (p : ∀ i, α i → ℝ) (a : α d) (r : Rest α d) :
    wt p ((Equiv.piSplitAt d α).symm (a, r)) = p d a * wt' d p r := by
  unfold wt wt'
  rw [Fintype.prod_eq_mul_prod_compl d, symm_apply_self]
  congr 1
  have hsub : ∏ j ∈ ({d}ᶜ : Finset ι), p j ((Equiv.piSplitAt d α).symm (a, r) j) =
      ∏ j : {j // j ≠ d}, p j ((Equiv.piSplitAt d α).symm (a, r) j) :=
    prod_subtype ({d}ᶜ) (fun j => by simp) _
  rw [hsub]
  exact prod_congr rfl fun j _ => by rw [symm_apply_ne d a r j.2]

/-- The mass of an event, split along the dice factor. -/
theorem mass_eq (p : ∀ i, α i → ℝ) (A : (∀ i, α i) → Prop) :
    mass p A = ∑ a : α d, p d a *
      ∑ r : Rest α d, if A ((Equiv.piSplitAt d α).symm (a, r)) then wt' d p r else 0 := by
  unfold mass
  rw [← (Equiv.piSplitAt d α).symm.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [wt_symm]
  split_ifs <;> simp

/-- The mass of `Y = y` restricted to the other factors, at dice value `a`. -/
noncomputable def Q (p : ∀ i, α i → ℝ) (Y : (∀ i, α i) → β) (y : β) (a : α d) : ℝ :=
  ∑ r : Rest α d, if Y ((Equiv.piSplitAt d α).symm (a, r)) = y then wt' d p r else 0

/-- The total mass of the other factors. -/
noncomputable def Z' (p : ∀ i, α i → ℝ) : ℝ := ∑ r : Rest α d, wt' d p r

theorem mass_and (p : ∀ i, α i → ℝ) (Y : (∀ i, α i) → β) (y : β) (a : α d) :
    mass p (fun ω => Y ω = y ∧ ω d = a) = p d a * Q d p Y y a := by
  rw [mass_eq, sum_eq_single a]
  · unfold Q
    congr 1
    refine sum_congr rfl fun r _ => ?_
    simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (mem_univ a) h

theorem mass_Y (p : ∀ i, α i → ℝ) (Y : (∀ i, α i) → β) (y : β) :
    mass p (fun ω => Y ω = y) = ∑ a, p d a * Q d p Y y a :=
  mass_eq d p _

theorem mass_coord (p : ∀ i, α i → ℝ) (a : α d) :
    mass p (fun ω => ω d = a) = p d a * Z' d p := by
  rw [mass_eq, sum_eq_single a]
  · unfold Z'
    congr 1
    refine sum_congr rfl fun r _ => ?_
    simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (mem_univ a) h

theorem mass_univ (p : ∀ i, α i → ℝ) : mass p (fun _ => True) = (∑ a, p d a) * Z' d p := by
  rw [mass_eq d, sum_mul]
  simp only [ite_true, Z']

theorem prob_mul_of_mass {p : ∀ i, α i → ℝ} {A B C : (∀ i, α i) → Prop}
    (h : mass p A * mass p (fun _ => True) = mass p B * mass p C) :
    prob p A = prob p B * prob p C := by
  unfold prob
  by_cases hZ : mass p (fun _ => True) = 0
  · simp [hZ]
  · rw [div_mul_div_comm, div_eq_div_iff hZ (mul_ne_zero hZ hZ)]
    linear_combination (mass p fun _ => True) * h

theorem mass_mul_of_prob {p : ∀ i, α i → ℝ} {A B C : (∀ i, α i) → Prop}
    (hZ : mass p (fun _ => True) ≠ 0) (h : prob p A = prob p B * prob p C) :
    mass p A * mass p (fun _ => True) = mass p B * mass p C := by
  unfold prob at h
  rw [div_mul_div_comm, div_eq_div_iff hZ (mul_ne_zero hZ hZ)] at h
  apply mul_right_cancel₀ hZ
  linear_combination h

/-- **No dependence ⟹ independence under every product distribution.** If `Y` does not depend on the dice
factor, `Y` and `ω d` satisfy the product rule for every choice of factor weights (positive or not). -/
theorem indep_of_not_mem_history {Y : (∀ i, α i) → β} (hd : d ∉ history Y) (p : ∀ i, α i → ℝ) :
    Indep p Y d := by
  rw [mem_history, not_dependsOn_iff] at hd
  have hQ : ∀ y a a', Q d p Y y a = Q d p Y y a' := fun y a a' =>
    sum_congr rfl fun r _ => by
      rw [hd ((Equiv.piSplitAt d α).symm (a, r)) ((Equiv.piSplitAt d α).symm (a', r))
        fun _ hj => by rw [symm_apply_ne d a r hj, symm_apply_ne d a' r hj]]
  intro y a
  apply prob_mul_of_mass
  rw [mass_and, mass_Y, mass_coord, mass_univ]
  have : ∑ a', p d a' * Q d p Y y a' = (∑ a', p d a') * Q d p Y y a := by
    rw [sum_mul]
    exact sum_congr rfl fun a' _ => by rw [hQ y a' a]
  rw [this]
  ring

theorem wt'_pos {p : ∀ i, α i → ℝ} (hp : PosWeights p) (r : Rest α d) : 0 < wt' d p r :=
  prod_pos fun _ _ => hp _ _

/-- Under a full-support product distribution, independence forces the conditional mass of `Y = y` not to depend
on the dice value. -/
theorem Q_eq_of_indep [∀ i, Nonempty (α i)] {p : ∀ i, α i → ℝ} (hp : PosWeights p)
    {Y : (∀ i, α i) → β} (h : Indep p Y d) (y : β) (a a' : α d) : Q d p Y y a = Q d p Y y a' := by
  have hZ' : 0 < Z' d p := sum_pos (fun r _ => wt'_pos d hp r) univ_nonempty
  have hS : 0 < ∑ b, p d b := sum_pos (fun b _ => hp d b) univ_nonempty
  have hZ : mass p (fun _ => True) ≠ 0 := by
    rw [mass_univ]
    exact (mul_pos hS hZ').ne'
  have key : ∀ b, Q d p Y y b * ∑ b', p d b' = ∑ b', p d b' * Q d p Y y b' := by
    intro b
    have h1 := mass_mul_of_prob hZ (h y b)
    rw [mass_and, mass_Y, mass_coord, mass_univ] at h1
    have hb : p d b * Z' d p ≠ 0 := (mul_pos (hp d b) hZ').ne'
    apply mul_right_cancel₀ hb
    linear_combination h1
  exact mul_right_cancel₀ hS.ne' ((key a).trans (key a').symm)

/-- **Dependence ⟹ some full-support product distribution sees it.** If `Y` depends on the dice factor, there are
positive factor weights under which `Y` and `ω d` violate the product rule: concentrate the other factors near a
separating configuration. -/
theorem exists_posWeights_not_indep {Y : (∀ i, α i) → β} (h : DependsOn Y d) :
    ∃ p : ∀ i, α i → ℝ, PosWeights p ∧ ¬ Indep p Y d := by
  obtain ⟨ω, ω', hoff, hne⟩ := h
  have : ∀ i, Nonempty (α i) := fun i => ⟨ω i⟩
  have hC : (1 : ℝ) ≤ Fintype.card (Rest α d) := by exact_mod_cast Fintype.card_pos
  set ε : ℝ := 1 / (2 * (Fintype.card (Rest α d) : ℝ)) with hεdef
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hεdef]
    exact div_le_one_of_le₀ (by linarith) (by positivity)
  set p : ∀ i, α i → ℝ := fun i b => if b = ω i then 1 else ε with hpdef
  have hp : PosWeights p := fun i b => by
    simp only [hpdef]
    split_ifs <;> linarith
  refine ⟨p, hp, fun hind => ?_⟩
  set r₀ : Rest α d := fun j => ω j with hr₀
  have hQ := Q_eq_of_indep d hp hind (Y ω) (ω d) (ω' d)
  have hsymm₀ : (Equiv.piSplitAt d α).symm (ω d, r₀) = ω := (Equiv.piSplitAt d α).symm_apply_apply ω
  have hsymm₁ : (Equiv.piSplitAt d α).symm (ω' d, r₀) = ω' := by
    have : r₀ = fun j : {j // j ≠ d} => ω' j := funext fun j => hoff j j.2
    rw [this]
    exact (Equiv.piSplitAt d α).symm_apply_apply ω'
  have hwt₀ : wt' d p r₀ = 1 := by simp [wt', hpdef, hr₀]
  have hwt : ∀ r : Rest α d, r ≠ r₀ → wt' d p r ≤ ε := by
    intro r hr
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hr
    unfold wt'
    rw [← mul_prod_erase univ _ (mem_univ j)]
    have hj' : r j ≠ ω j := hj
    have h1 : p j (r j) = ε := by simp [hpdef, hj']
    rw [h1]
    apply mul_le_of_le_one_right hε.le
    apply prod_le_one₀
    · intro i _
      exact (hp _ _).le
    · intro i _
      simp only [hpdef]
      split_ifs <;> linarith
  have hlow : 1 ≤ Q d p Y (Y ω) (ω d) := by
    unfold Q
    have := single_le_sum
      (f := fun r : Rest α d => if Y ((Equiv.piSplitAt d α).symm (ω d, r)) = Y ω then wt' d p r else 0)
      (fun r _ => by
        split_ifs
        · exact (wt'_pos d hp r).le
        · exact le_rfl)
      (mem_univ r₀)
    simpa [hsymm₀, hwt₀] using this
  have hup : Q d p Y (Y ω) (ω' d) ≤ 1 / 2 := by
    unfold Q
    calc _ ≤ (univ : Finset (Rest α d)).card • ε := sum_le_card_nsmul _ _ _ fun r _ => ?_
      _ = (Fintype.card (Rest α d) : ℝ) * ε := by rw [card_univ, nsmul_eq_mul]
      _ = 1 / 2 := by
        rw [hεdef]
        field_simp
    split_ifs with hY
    · by_cases hr : r = r₀
      · subst hr
        rw [hsymm₁] at hY
        exact absurd hY.symm hne
      · exact hwt r hr
    · exact hε.le
  linarith

/-- **The one-factor slice of Garrabrant's fundamental theorem.** The dice factor is in the history of `Y` iff
some full-support product distribution makes `Y` and the dice coordinate dependent. -/
theorem mem_history_iff_exists_dep {Y : (∀ i, α i) → β} :
    d ∈ history Y ↔ ∃ p : ∀ i, α i → ℝ, PosWeights p ∧ ¬ Indep p Y d := by
  constructor
  · intro h
    exact exists_posWeights_not_indep d (mem_history.1 h)
  · rintro ⟨p, _, hp⟩
    by_contra hd
    exact hp (indep_of_not_mem_history d hd p)

/-- Contrapositive form: the dice factor is outside the history of `Y` iff `Y` is independent of the dice
coordinate under every full-support product distribution (and then under every product distribution). -/
theorem not_mem_history_iff_forall_indep {Y : (∀ i, α i) → β} :
    d ∉ history Y ↔ ∀ p : ∀ i, α i → ℝ, PosWeights p → Indep p Y d := by
  rw [mem_history_iff_exists_dep]
  push Not
  rfl

end Prob

/-! ### The fixed-distribution version is false: XOR of two uniform bits -/

section Xor

open Classical

/-- `Y(ω) = ω true XOR ω false` on two binary factors. -/
def xorY : (Bool → Bool) → Bool := fun ω => xor (ω true) (ω false)

/-- `xorY` depends on the first factor. -/
theorem xorY_dependsOn : DependsOn (α := fun _ : Bool => Bool) xorY true :=
  ⟨fun _ => false, fun b => b, fun j hj => by cases j <;> simp_all, by decide⟩

/-- Yet under the uniform product distribution `xorY` is independent of the first coordinate: the product rule
holds for every pair of values. So "`d ∈ h(Y)` ⟺ dependent under a *fixed* full-support product distribution"
is false; only the existential version (`mem_history_iff_exists_dep`) holds. -/
theorem xorY_indep : Indep (α := fun _ : Bool => Bool) (fun _ _ => (1 : ℝ)) xorY true := by
  intro y a
  have hm : ∀ A : (Bool → Bool) → Prop, mass (α := fun _ : Bool => Bool) (fun _ _ => (1 : ℝ)) A =
      ∑ x : Bool × Bool, if A ((Equiv.boolArrowEquivProd Bool).symm x) then 1 else 0 := by
    intro A
    unfold mass
    rw [← (Equiv.boolArrowEquivProd Bool).symm.sum_comp]
    simp [wt]
  simp only [prob, hm, Fintype.sum_prod_type, Fintype.sum_bool, xorY]
  cases y <;> cases a <;> simp <;> norm_num

end Xor

/-! ## (4) Continuous: the dice is in the history iff the partial derivative along it is somewhere nonzero -/

section Continuous

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The partial derivative of `Y` along factor `d` at `ω`: the derivative composed with the inclusion of the
`d`-th factor. -/
noncomputable def partialAlong (d : ι) (Y : (∀ i, E i) → G) (ω : ∀ i, E i) : E d →L[ℝ] G :=
  (fderiv ℝ Y ω).comp (ContinuousLinearMap.single ℝ E d)

theorem pi_single_eq_single (d : ι) :
    ContinuousLinearMap.pi (Pi.single d (ContinuousLinearMap.id ℝ (E d))) =
      ContinuousLinearMap.single ℝ E d := by
  ext x j
  by_cases hj : j = d
  · subst hj; simp
  · simp [hj]

/-- Moving only the `d`-th factor: the derivative of `x ↦ Y (ω with factor d set to x)` is the partial derivative
along `d`. -/
theorem hasFDerivAt_update_comp (d : ι) {Y : (∀ i, E i) → G} (ω : ∀ i, E i) (x : E d)
    (hY : DifferentiableAt ℝ Y (Function.update ω d x)) :
    HasFDerivAt (fun x => Y (Function.update ω d x)) (partialAlong d Y (Function.update ω d x)) x := by
  have := hY.hasFDerivAt.comp x (hasFDerivAt_update ω x)
  rw [pi_single_eq_single] at this
  exact this

theorem update_eq_of_agree {d : ι} {ω ω' : ∀ i, E i} (hoff : ∀ j, j ≠ d → ω j = ω' j) :
    Function.update ω d (ω' d) = ω' := by
  funext j
  by_cases hj : j = d
  · subst hj; simp
  · rw [Function.update_of_ne hj]
    exact hoff j hj

/-- **The continuous criterion.** For differentiable `Y`, the dice factor is in the history of `Y` iff the partial
derivative along the dice is nonzero at some point. (⟸ by uniqueness of the derivative: if `Y` did not depend on
`d`, the restriction to the `d`-line would be constant. ⟹ by the mean value theorem along the `d`-line: zero
partial everywhere makes the restriction constant, so `Y` cannot separate two points differing only in `d`.) -/
theorem mem_history_iff_partial_ne_zero (d : ι) {Y : (∀ i, E i) → G} (hY : Differentiable ℝ Y) :
    d ∈ history Y ↔ ∃ ω, partialAlong d Y ω ≠ 0 := by
  rw [mem_history]
  constructor
  · intro h
    by_contra hz
    push Not at hz
    obtain ⟨ω, ω', hoff, hne⟩ := h
    apply hne
    have hdiff : Differentiable ℝ fun x => Y (Function.update ω d x) :=
      fun x => (hasFDerivAt_update_comp d ω x (hY _)).differentiableAt
    have hconst := is_const_of_fderiv_eq_zero hdiff
      (fun x => (hasFDerivAt_update_comp d ω x (hY _)).fderiv.trans (hz _)) (ω d) (ω' d)
    simpa [update_eq_of_agree hoff] using hconst
  · rintro ⟨ω, hω⟩
    by_contra h
    rw [not_dependsOn_iff] at h
    apply hω
    have hc : (fun x => Y (Function.update ω d x)) = fun _ => Y ω :=
      funext fun x => h _ _ fun j hj => Function.update_of_ne hj _ _
    have h1 := hasFDerivAt_update_comp d ω (ω d) (hY _)
    rw [Function.update_eq_self] at h1
    rw [hc] at h1
    exact h1.unique (hasFDerivAt_const _ _)

/-- Zero partial derivative along `d` everywhere ⟹ `Y` does not depend on `d` (the ⟹ half, stated directly). -/
theorem not_dependsOn_of_partial_eq_zero (d : ι) {Y : (∀ i, E i) → G} (hY : Differentiable ℝ Y)
    (hz : ∀ ω, partialAlong d Y ω = 0) : ¬ DependsOn Y d := by
  rw [← mem_history, mem_history_iff_partial_ne_zero d hY]
  push Not
  exact hz

end Continuous

/-! ## (5) Bridge to `Causal.lean`: kin = the slots after the dice, weighted by the derivative along the dice -/

section Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)] {N K : Type*} [Fintype N] [DecidableEq N] [Fintype K] (d : ι)

/-- The world seen from the dice: freeze every factor other than `d` at its value in `ω`, and let the policy
`θ ∈ E d` vary. Slot `j`'s state becomes the function `θ ↦ x j (ω with the dice set to θ)` of `Causal.lean`. -/
def freeze (ω : ∀ i, E i) (x : N → (∀ i, E i) → E d) : N → E d → E d :=
  fun j θ => x j (Function.update ω d θ)

/-- Linear-in-dice slots: slot `j` holds `r j • θ + b j (other factors)`. -/
def linSlot (r : N → ℝ) (b : N → (∀ i, E i) → E d) : N → (∀ i, E i) → E d :=
  fun j ω => r j • ω d + b j ω

/-- Freezing the other factors turns a linear-in-dice slot into `Causal.linResp` with base states `b j ω`. -/
theorem freeze_linSlot (r : N → ℝ) (b : N → (∀ i, E i) → E d) (hb : ∀ j, ¬ DependsOn (b j) d)
    (ω : ∀ i, E i) : freeze d ω (linSlot d r b) = Causal.linResp r fun j => b j ω := by
  funext j θ
  simp only [freeze, linSlot, Causal.linResp, Function.update_self]
  congr 1
  exact (not_dependsOn_iff.1 (hb j)) _ _ fun i hi => Function.update_of_ne hi _ _

/-- **Kin = after the dice.** A linear-in-dice slot is after the dice iff its response `r j` is nonzero. -/
theorem afterDice_linSlot_iff [Nontrivial (E d)] (r : N → ℝ) (b : N → (∀ i, E i) → E d)
    (hb : ∀ j, ¬ DependsOn (b j) d) (j : N) : d ∈ history (linSlot d r b j) ↔ r j ≠ 0 := by
  rw [mem_history]
  constructor
  · intro h hr
    apply hb j
    obtain ⟨ω, ω', hoff, hne⟩ := h
    refine ⟨ω, ω', hoff, fun heq => hne ?_⟩
    simp [linSlot, hr, heq]
  · intro hr
    obtain ⟨v, hv⟩ := exists_ne (0 : E d)
    refine ⟨Function.update 0 d v, 0, fun i hi => Function.update_of_ne hi _ _, ?_⟩
    have hb' : b j (Function.update 0 d v) = b j 0 :=
      (not_dependsOn_iff.1 (hb j)) _ _ fun i hi => Function.update_of_ne hi _ _
    simp only [linSlot, Function.update_self, Pi.zero_apply, smul_zero, zero_add, hb']
    intro heq
    exact smul_ne_zero hr hv (by simpa using heq)

/-- **`Causal.linear_iff`, restated on the factored world.** Freeze the other factors at any `ω`. If `dim V ≥ 2`
and some slot is after the dice, then the learner's field is conservative for every C² reward family iff its
credits are `a j k = c k * r j`: the true response along the dice times a credit per reward. -/
theorem bridge_linear_iff [FiniteDimensional ℝ (E d)] [Nontrivial (E d)]
    (h2 : 2 ≤ Module.finrank ℝ (E d)) (r : N → ℝ) (b : N → (∀ i, E i) → E d)
    (hb : ∀ j, ¬ DependsOn (b j) d) (hr : ∃ j, d ∈ history (linSlot d r b j)) (a : N → K → ℝ)
    (ω : ∀ i, E i) :
    (∀ R : K → (N → E d) → ℝ, (∀ k, ContDiff ℝ 2 (R k)) →
        Conservative (Causal.causalField (freeze d ω (linSlot d r b)) (Causal.scalarA a) R)) ↔
      ∃ c : K → ℝ, ∀ j k, a j k = c k * r j := by
  rw [freeze_linSlot d r b hb ω]
  refine Causal.linear_iff h2 r ?_ _ a
  simpa [afterDice_linSlot_iff d r b hb] using hr

/-- The Kantian credits vanish off the after-dice set. -/
theorem credit_eq_zero_of_not_afterDice [Nontrivial (E d)] (r : N → ℝ) (b : N → (∀ i, E i) → E d)
    (hb : ∀ j, ¬ DependsOn (b j) d) {a : N → K → ℝ} {c : K → ℝ} (hc : ∀ j k, a j k = c k * r j)
    {j : N} (hj : d ∉ history (linSlot d r b j)) (k : K) : a j k = 0 := by
  rw [afterDice_linSlot_iff d r b hb, not_not] at hj
  rw [hc, hj, mul_zero]

/-- On the after-dice set the Kantian credit of slot `j` for reward `k` vanishes only if the credit `c k` attached
to that reward vanishes: the support of `j ↦ a j k` is exactly the after-dice set whenever `c k ≠ 0`. -/
theorem credit_eq_zero_iff_of_afterDice [Nontrivial (E d)] (r : N → ℝ) (b : N → (∀ i, E i) → E d)
    (hb : ∀ j, ¬ DependsOn (b j) d) {a : N → K → ℝ} {c : K → ℝ} (hc : ∀ j k, a j k = c k * r j)
    {j : N} (hj : d ∈ history (linSlot d r b j)) (k : K) : a j k = 0 ↔ c k = 0 := by
  rw [afterDice_linSlot_iff d r b hb] at hj
  rw [hc, mul_eq_zero, or_iff_left hj]

/-! ### General differentiable slots -/

/-- The Kantian credit of slot `j` for reward `k` at world state `ω`: the credit `c k` times the true response of
the slot's state to the dice, `∂_d x_j (ω)`. -/
noncomputable def kantianCredit (c : K → ℝ) (x : N → (∀ i, E i) → E d) (j : N) (k : K)
    (ω : ∀ i, E i) : E d →L[ℝ] E d :=
  c k • partialAlong d (x j) ω

/-- Freezing the other factors: the true response of slot `j` in `Causal.lean` is the partial derivative of its
state along the dice. -/
theorem fderiv_freeze (ω : ∀ i, E i) (x : N → (∀ i, E i) → E d) (hx : ∀ j, Differentiable ℝ (x j))
    (j : N) (θ : E d) :
    fderiv ℝ (freeze d ω x j) θ = partialAlong d (x j) (Function.update ω d θ) :=
  (hasFDerivAt_update_comp d ω θ (hx j _)).fderiv

/-- **A learner on the frozen world is Kantian in the sense of `Causal.lean` iff its assumed responses are the
Kantian credits `c k • ∂_d x_j`.** -/
theorem isKantian_freeze_iff (ω : ∀ i, E i) (x : N → (∀ i, E i) → E d)
    (hx : ∀ j, Differentiable ℝ (x j)) (A : N → K → E d → (E d →L[ℝ] E d)) :
    Causal.IsKantian (freeze d ω x) A ↔
      ∃ c : K → ℝ, ∀ j k θ, A j k θ = kantianCredit d c x j k (Function.update ω d θ) := by
  unfold Causal.IsKantian kantianCredit
  simp only [fderiv_freeze d ω x hx]

/-- The Kantian learner's field on the frozen world is conservative (from `Causal.conservative_of_isKantian`). -/
theorem conservative_freeze (ω : ∀ i, E i) (x : N → (∀ i, E i) → E d)
    (hx : ∀ j, Differentiable ℝ (x j)) (c : K → ℝ) (R : K → (N → E d) → ℝ)
    (hR : ∀ k, Differentiable ℝ (R k)) :
    Conservative (Causal.causalField (freeze d ω x)
      (fun j k θ => kantianCredit d c x j k (Function.update ω d θ)) R) :=
  Causal.conservative_of_isKantian _ _ ((isKantian_freeze_iff d ω x hx _).2 ⟨c, fun _ _ _ => rfl⟩) R
    (fun j θ => (hasFDerivAt_update_comp d ω θ (hx j _)).differentiableAt) hR

/-- **Kantian credit vanishes off the after-dice set.** If slot `j`'s state does not depend on the dice, its
Kantian credit is zero everywhere, for every reward. -/
theorem kantianCredit_eq_zero_of_not_afterDice (c : K → ℝ) (x : N → (∀ i, E i) → E d)
    (hx : ∀ j, Differentiable ℝ (x j)) {j : N} (hj : d ∉ history (x j)) (k : K) (ω : ∀ i, E i) :
    kantianCredit d c x j k ω = 0 := by
  rw [mem_history_iff_partial_ne_zero d (hx j)] at hj
  push Not at hj
  simp [kantianCredit, hj ω]

/-- **The support of the Kantian credit is the after-dice set.** For a reward with nonzero credit `c k ≠ 0`,
slot `j` receives a nonzero Kantian credit somewhere iff the dice is in the history of its state. -/
theorem afterDice_iff_exists_kantianCredit_ne_zero (c : K → ℝ) (x : N → (∀ i, E i) → E d)
    (hx : ∀ j, Differentiable ℝ (x j)) (j : N) {k : K} (hk : c k ≠ 0) :
    d ∈ history (x j) ↔ ∃ ω, kantianCredit d c x j k ω ≠ 0 := by
  rw [mem_history_iff_partial_ne_zero d (hx j)]
  unfold kantianCredit
  simp [hk]

/-- The linear-in-dice slots are differentiable when the base states are. -/
theorem differentiable_linSlot (r : N → ℝ) (b : N → (∀ i, E i) → E d)
    (hb : ∀ j, Differentiable ℝ (b j)) (j : N) : Differentiable ℝ (linSlot d r b j) := by
  unfold linSlot
  fun_prop

/-- On linear-in-dice slots the Kantian credit is the scalar credit `c k * r j` of `Causal.linear_iff`. -/
theorem kantianCredit_linSlot (c : K → ℝ) (r : N → ℝ) (b : N → (∀ i, E i) → E d)
    (hb : ∀ j, ¬ DependsOn (b j) d) (hbd : ∀ j, Differentiable ℝ (b j)) (j : N) (k : K)
    (ω : ∀ i, E i) :
    kantianCredit d c (linSlot d r b) j k ω = Causal.scalarA (fun j k => c k * r j) j k (ω d) := by
  have h := fderiv_freeze d ω (linSlot d r b) (differentiable_linSlot d r b hbd) j (ω d)
  rw [Function.update_eq_self, freeze_linSlot d r b hb ω, Causal.fderiv_linResp] at h
  unfold kantianCredit
  rw [← h, Causal.scalarA, mul_smul]

end Bridge

end BoundaryTheorem.Factored
