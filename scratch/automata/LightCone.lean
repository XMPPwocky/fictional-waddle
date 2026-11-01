/-
# Local rules have light cones: the fridge-light problem, in both directions

A one-dimensional cellular automaton on ℤ with states S: each cell's next state is a fixed function of
itself and its two neighbours. Neural cellular automata have this form with a learned rule.

PROVED
1. `light_cone`: after n steps, cell i depends only on the initial cells in [i − n, i + n]: two initial
   configurations that agree there give the same state at cell i.
2. `inside_hidden`: if two worlds differ only inside a region [a, b] (the inside of the fridge), then
   for n steps every cell farther than n from that region sees exactly the same history. No probe
   outside can tell whether the light is on inside until a signal has had time to reach it.
3. `outside_hidden`: the same holds with inside and outside swapped: a cell inside [a + n, b − n]
   cannot tell two worlds that differ only outside [a, b] for n steps.

INTERPRETED (not formalized)
- Locality is symmetric: whatever cannot see in cannot be seen from in, at the same speed. A closed
  door is a region you have not yet received a signal from, from either side.
- This is a property of any local rule, including the Physarum Ear's simulated medium; it does not use
  anything specific to that code.
-/

import Mathlib

namespace LightCone

variable {S : Type*}

def step (rule : S → S → S → S) (f : ℤ → S) : ℤ → S := fun i => rule (f (i - 1)) (f i) (f (i + 1))

theorem light_cone (rule : S → S → S → S) (n : ℕ) (f g : ℤ → S) (i : ℤ)
    (h : ∀ j, i - n ≤ j → j ≤ i + n → f j = g j) :
    (step rule)^[n] f i = (step rule)^[n] g i := by
  induction n generalizing i f g with
  | zero => exact h i (by simp) (by simp)
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    apply ih
    intro j hj1 hj2
    simp only [step]
    push_cast at hj1 hj2 h
    rw [h (j - 1) (by omega) (by omega), h j (by omega) (by omega), h (j + 1) (by omega) (by omega)]

theorem inside_hidden (rule : S → S → S → S) (n : ℕ) (f g : ℤ → S) (a b : ℤ)
    (hdiff : ∀ j, (j < a ∨ b < j) → f j = g j) (i : ℤ) (hfar : i + n < a ∨ b < i - n) :
    (step rule)^[n] f i = (step rule)^[n] g i := by
  apply light_cone
  intro j h1 h2
  apply hdiff
  omega

theorem outside_hidden (rule : S → S → S → S) (n : ℕ) (f g : ℤ → S) (a b : ℤ)
    (hdiff : ∀ j, a ≤ j → j ≤ b → f j = g j) (i : ℤ) (hin : a + n ≤ i ∧ i ≤ b - n) :
    (step rule)^[n] f i = (step rule)^[n] g i := by
  apply light_cone
  intro j h1 h2
  apply hdiff <;> omega

end LightCone

#print axioms LightCone.light_cone
#print axioms LightCone.inside_hidden
#print axioms LightCone.outside_hidden
