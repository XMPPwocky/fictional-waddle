import Mathlib

/-!
# Computation pays in the other machine's blank tape

Joint physics is reversible: an injective map `f` on `System × Environment`. "Erase" means that every system state
in use is sent to one state `s₀`, whatever it was. The environment starts in a known set `E₀` (its blank tape).

* L1 `erasure_moves_the_bits`: the environment's reachable set after erasure has EXACTLY `|S| · |E₀|` states. The
  erased `log |S|` bits are not destroyed; they are written into the environment. Joint volume is conserved.
* L2 `erasure_needs_room`: so a reversible erasure exists only if `|S| · |E₀| ≤ |E|`. A full (hot) environment has
  no room. Computing consumes the other machine's blank tape.
* L3 `swap_erases_iff_cold`: the standard eraser, swapping the system with one environment register: the system
  ends in `s₀` for every start iff that register started at `s₀`. Only cold tape erases.
-/

namespace LandauerCounting

open Finset

/-- **L1.** -/
theorem erasure_moves_the_bits {S E : Type*} [Fintype S] [DecidableEq S] [DecidableEq E] (E₀ : Finset E)
    (f : S × E → S × E) (hf : Function.Injective f) (s₀ : S) (herase : ∀ s e, e ∈ E₀ → (f (s, e)).1 = s₀) :
    ((univ ×ˢ E₀).image (fun p => (f p).2)).card = Fintype.card S * E₀.card := by
  rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_univ]
  rintro ⟨s, e⟩ hp ⟨s', e'⟩ hq h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hq
  apply hf
  exact Prod.ext (by rw [herase s e hp.2, herase s' e' hq.2]) h

/-- **L2.** -/
theorem erasure_needs_room {S E : Type*} [Fintype S] [Fintype E] [DecidableEq S] [DecidableEq E] (E₀ : Finset E)
    (f : S × E → S × E) (hf : Function.Injective f) (s₀ : S) (herase : ∀ s e, e ∈ E₀ → (f (s, e)).1 = s₀) :
    Fintype.card S * E₀.card ≤ Fintype.card E := by
  rw [← erasure_moves_the_bits E₀ f hf s₀ herase]
  exact Finset.card_le_univ _

/-- **L3.** The swap eraser on `S × (S × R)`: `(s, (r₁, r)) ↦ (r₁, (s, r))`. -/
theorem swap_erases_iff_cold {S R : Type*} (s₀ r₁ : S) (r : R) :
    (∀ s : S, ((fun p : S × (S × R) => (p.2.1, (p.1, p.2.2))) (s, (r₁, r))).1 = s₀) ↔ r₁ = s₀ := by
  constructor
  · intro h; exact h s₀
  · intro h s; simp [h]

end LandauerCounting
