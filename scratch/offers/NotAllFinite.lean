import Mathlib

/-!
# Not-all theorem, finite half

PROVED:
* `NotAllFinite.compl_compl_finset_inf`: in any Heyting algebra, double negation
  distributes over finite meets: `(s.inf a)ᶜᶜ = s.inf (fun i => (a i)ᶜᶜ)`.
* `NotAllFinite.compl_finset_inf_eq_bot`: in any Heyting algebra, if every `a i`
  with `i ∈ s` is dense (`(a i)ᶜ = ⊥`), then the finite meet is dense:
  `(s.inf a)ᶜ = ⊥`.
* `NotAllFinite.opens_compl_compl_finset_inf`: statement (1) for the frame
  `TopologicalSpace.Opens X` of open sets of any topological space `X`.
* `NotAllFinite.opens_compl_finset_inf_eq_bot`: statement (2) for
  `TopologicalSpace.Opens X`: a finite intersection of dense-in-the-Heyting-sense
  open sets has bottom pseudocomplement.

INTERPRETED (not formalized):
* Reading `(s.inf a)ᶜ = ⊥` as "'not all' fails for a finite domain with no
  exception" is an informal gloss; the formal content is the equation above.
-/

namespace NotAllFinite

theorem compl_compl_finset_inf {α ι : Type*} [HeytingAlgebra α]
    (s : Finset ι) (a : ι → α) :
    (s.inf a)ᶜᶜ = s.inf (fun i => (a i)ᶜᶜ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.inf_insert, Finset.inf_insert, compl_compl_inf_distrib, ih]

theorem compl_finset_inf_eq_bot {α ι : Type*} [HeytingAlgebra α]
    (s : Finset ι) (a : ι → α) (h : ∀ i ∈ s, (a i)ᶜ = ⊥) :
    (s.inf a)ᶜ = ⊥ := by
  have htop : s.inf (fun i => (a i)ᶜᶜ) = ⊤ := by
    rw [Finset.inf_eq_top_iff]
    intro i hi
    rw [h i hi, compl_bot]
  rw [← compl_compl_compl (s.inf a), compl_compl_finset_inf, htop, compl_top]

theorem opens_compl_compl_finset_inf {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (a : ι → TopologicalSpace.Opens X) :
    (s.inf a)ᶜᶜ = s.inf (fun i => (a i)ᶜᶜ) :=
  compl_compl_finset_inf s a

theorem opens_compl_finset_inf_eq_bot {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (a : ι → TopologicalSpace.Opens X) (h : ∀ i ∈ s, (a i)ᶜ = ⊥) :
    (s.inf a)ᶜ = ⊥ :=
  compl_finset_inf_eq_bot s a h

end NotAllFinite
