import Mathlib

/-!
# Troll bridge from Löb's theorem in the abstract setting

The setting is restated from `scratch/lob/Lob.lean`: a type of formulas with an implication and a box, a
provability predicate closed under modus ponens and two propositional rules, the Hilbert–Bernays–Löb
derivability conditions, and the diagonal (fixed-point) sentence supplied as the hypotheses `fix1`, `fix2`.
A negation `neg` is added together with the single hypothesis schema `exfalso : ⊢ ¬a → (a → b)`.

PROVED:
* `lob`: if `⊢ □P → P` (with a diagonal sentence `ψ ↔ (□ψ → P)`), then `⊢ P`.
* `troll_bridge`: from `exfalso`, the policy `⊢ □(C → B) → ¬C`, and a diagonal sentence for `C → B`,
  the system proves both `C → B` and `¬C`.
* `troll_bridge_any`: the consequent is arbitrary; for every `B'`, the same hypotheses with `B'` in place
  of `B` give `⊢ C → B'`.
* `troll_bridge_everything`: from the hypotheses for one `B`, the system proves `C → B'` for every `B'`.

INTERPRETED (not formalized):
* Nothing about a troll appears in the formal statement; there is no bridge, no payoff and no troll who
  punishes crossing. The only ingredients are a policy, material implication and Löb's theorem.
* `C` means "the agent crosses", `B` an arbitrary (for instance bad) outcome, and `policy` is the agent's
  own source code: if it proves that crossing implies `B`, it does not cross.
* `exfalso` (material implication: a false antecedent implies anything) is the step disputed in the
  literature; it is what turns `¬C` into `C → B` and lets Löb close the loop, so the agent proves it does
  not cross, and proves that crossing would yield any outcome whatsoever.
-/

namespace TrollBridgeB

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

theorem troll_bridge (L : Logic imp box Prov) (neg : F → F) (C B ψ : F)
    (exfalso : ∀ a b, Prov (imp (neg a) (imp a b)))
    (policy : Prov (imp (box (imp C B)) (neg C)))
    (fix1 : Prov (imp ψ (imp (box ψ) (imp C B))))
    (fix2 : Prov (imp (imp (box ψ) (imp C B)) ψ)) :
    Prov (imp C B) ∧ Prov (neg C) := by
  have h : Prov (imp (box (imp C B)) (imp C B)) := L.syl _ _ _ policy (exfalso C B)
  have hCB : Prov (imp C B) := lob imp box Prov L (imp C B) ψ fix1 fix2 h
  exact ⟨hCB, L.mp _ _ policy (L.d1 _ hCB)⟩

theorem troll_bridge_any (L : Logic imp box Prov) (neg : F → F) (C : F)
    (exfalso : ∀ a b, Prov (imp (neg a) (imp a b))) :
    ∀ B' ψ : F, Prov (imp (box (imp C B')) (neg C)) →
      Prov (imp ψ (imp (box ψ) (imp C B'))) →
      Prov (imp (imp (box ψ) (imp C B')) ψ) →
      Prov (imp C B') :=
  fun B' ψ policy fix1 fix2 =>
    (troll_bridge imp box Prov L neg C B' ψ exfalso policy fix1 fix2).1

theorem troll_bridge_everything (L : Logic imp box Prov) (neg : F → F) (C B ψ : F)
    (exfalso : ∀ a b, Prov (imp (neg a) (imp a b)))
    (policy : Prov (imp (box (imp C B)) (neg C)))
    (fix1 : Prov (imp ψ (imp (box ψ) (imp C B))))
    (fix2 : Prov (imp (imp (box ψ) (imp C B)) ψ)) :
    ∀ B' : F, Prov (imp C B') :=
  fun B' => L.mp _ _ (exfalso C B')
    (troll_bridge imp box Prov L neg C B ψ exfalso policy fix1 fix2).2

end TrollBridgeB
