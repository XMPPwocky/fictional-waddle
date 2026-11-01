import Mathlib

/-!
# (A → R) → A is a monad (Garrabrant's "type of agency"; Escardó–Oliva's selection monad)

`J R A := (A → R) → A`, the selection functions (choose an A given how A's are valued), and `K R A := (A → R) → R`,
the quantifiers. `bindJ ε f` chooses first with `ε`, valuing each candidate `a` by how its continuation `f a` would
then play out: one step of backward induction.

* G1–G3 `left_id`, `right_id`, `assoc`: the monad laws for J.
* G4 `interleave_return`, G5 `interleave_bind`: MrMind's interleave `θ ε = fun p => p (ε p)` is a monad morphism
  J → K. Selecting and then evaluating is a quantifier, compatibly with sequencing.
* G6 `argmax_attains`: on a finite nonempty `A` with linearly ordered `R`, some selection function attains the max:
  `p (ε p) = sup p`. Argmax is the canonical (A → R) → A.
-/

namespace SelectionMonad

def J (R A : Type*) := (A → R) → A
def K (R A : Type*) := (A → R) → R

def pureJ {R A : Type*} (a : A) : J R A := fun _ => a
def bindJ {R A B : Type*} (ε : J R A) (f : A → J R B) : J R B := fun p => f (ε (fun a => p (f a p))) p

def pureK {R A : Type*} (a : A) : K R A := fun p => p a
def bindK {R A B : Type*} (φ : K R A) (f : A → K R B) : K R B := fun p => φ (fun a => f a p)

def interleave {R A : Type*} (ε : J R A) : K R A := fun p => p (ε p)

/-- **G1.** -/
theorem left_id {R A B : Type*} (a : A) (f : A → J R B) : bindJ (pureJ a) f = f a := by
  rfl

/-- **G2.** -/
theorem right_id {R A : Type*} (ε : J R A) : bindJ ε pureJ = ε := by
  rfl

/-- **G3.** -/
theorem assoc {R A B C : Type*} (ε : J R A) (f : A → J R B) (g : B → J R C) :
    bindJ (bindJ ε f) g = bindJ ε (fun a => bindJ (f a) g) := by
  rfl

/-- **G4.** -/
theorem interleave_return {R A : Type*} (a : A) : interleave (pureJ (R := R) a) = pureK a := by
  rfl

/-- **G5.** -/
theorem interleave_bind {R A B : Type*} (ε : J R A) (f : A → J R B) :
    interleave (bindJ ε f) = bindK (interleave ε) (fun a => interleave (f a)) := by
  rfl

/-- **G6.** -/
theorem argmax_attains {A R : Type*} [Fintype A] [Nonempty A] [LinearOrder R] :
    ∃ ε : J R A, ∀ p : A → R, ∀ a, p a ≤ p (ε p) := by
  classical
  refine ⟨fun p => Classical.choose (Finset.exists_max_image Finset.univ p Finset.univ_nonempty), ?_⟩
  intro p a
  exact (Classical.choose_spec (Finset.exists_max_image Finset.univ p Finset.univ_nonempty)).2 a (Finset.mem_univ a)

end SelectionMonad
