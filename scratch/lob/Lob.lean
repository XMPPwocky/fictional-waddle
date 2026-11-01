import Mathlib

/-!
# Löb's theorem from the derivability conditions

The setting is abstract: a type of formulas with an implication and a box, a provability predicate closed
under modus ponens and two propositional rules, the Hilbert–Bernays–Löb derivability conditions, and the
diagonal (fixed-point) lemma supplied as a hypothesis.

PROVED:
* `lob`: if `⊢ □P → P` then `⊢ P`.
* `second_incompleteness`: if the system proves its own consistency `□⊥ → ⊥`, it proves `⊥`.
* `fairbot_cooperates`: if a sentence `C` satisfies `⊢ □C → C` (it holds whenever it is provable, as two
  programs that each cooperate on finding a proof that the pair cooperates do), then `⊢ C`.
INTERPRETED (not formalized): the encoding of an actual arithmetic, the diagonal lemma, and programs reading
each other's source.
-/

namespace LobAbstract

variable {F : Type*} (imp : F → F → F) (box : F → F) (Prov : F → Prop)

structure Logic : Prop where
  mp : ∀ a b, Prov (imp a b) → Prov a → Prov b
  syl : ∀ a b c, Prov (imp a b) → Prov (imp b c) → Prov (imp a c)
  sRule : ∀ a b c, Prov (imp a (imp b c)) → Prov (imp a b) → Prov (imp a c)
  d1 : ∀ a, Prov a → Prov (box a)
  d2 : ∀ a b, Prov (imp (box (imp a b)) (imp (box a) (box b)))
  d3 : ∀ a, Prov (imp (box a) (box (box a)))

theorem lob (L : Logic imp box Prov) (P ψ : F)
    (fix1 : Prov (imp ψ (imp (box ψ) P))) (fix2 : Prov (imp (imp (box ψ) P) ψ))
    (h : Prov (imp (box P) P)) : Prov P := by
  have s1 : Prov (imp (box ψ) (box (imp (box ψ) P))) :=
    L.mp _ _ (L.d2 _ _) (L.d1 _ fix1)
  have s3 : Prov (imp (box ψ) (imp (box (box ψ)) (box P))) := L.syl _ _ _ s1 (L.d2 _ _)
  have s4 : Prov (imp (box ψ) (box P)) := L.sRule _ _ _ s3 (L.d3 _)
  have s5 : Prov (imp (box ψ) P) := L.syl _ _ _ s4 h
  have s6 : Prov ψ := L.mp _ _ fix2 s5
  exact L.mp _ _ s5 (L.d1 _ s6)

theorem second_incompleteness (L : Logic imp box Prov) (bot ψ : F)
    (fix1 : Prov (imp ψ (imp (box ψ) bot))) (fix2 : Prov (imp (imp (box ψ) bot) ψ))
    (hcon : Prov (imp (box bot) bot)) : Prov bot :=
  lob imp box Prov L bot ψ fix1 fix2 hcon

theorem fairbot_cooperates (L : Logic imp box Prov) (C ψ : F)
    (fix1 : Prov (imp ψ (imp (box ψ) C))) (fix2 : Prov (imp (imp (box ψ) C) ψ))
    (hcode : Prov (imp (box C) C)) : Prov C :=
  lob imp box Prov L C ψ fix1 fix2 hcode

end LobAbstract
