import Mathlib

/-!
# Provable puns from one message: place value is valency, and trusting trust

PROVED:
* `place_value_is_valency`: a one-place verb on two-digit numbers in base `n` (functions on `Fin (m * n)`) is the
  same thing as a two-place verb on (high digit, low digit) (functions `Fin m → Fin n → C`). Positional notation
  is currying.
* `time_of_day_is_three_place`: a function of the second of the day is a three-place verb on hours, minutes and
  seconds, with mixed radix 24, 60, 60.
* `trojan_invisible`: a compiler that misbehaves only on chosen trigger sources agrees with the honest compiler on
  every other source, so no test that avoids the triggers can tell them apart (Thompson's point).
* `trojan_reproduces`: the trojan compiling the honest compiler's source yields itself, so a clean source never
  removes it.
* `diverse_double_check_sound`: two checkers, each sound except on its own backdoor set, accept only true claims
  when both must agree and the backdoor sets are disjoint (Wheeler's diverse double-compiling, in its logical
  core).
INTERPRETED (not formalized): grammar, compilers in the wild, and the regex check that called a commented-out
theorem proved.
-/

namespace TrustingPlaces

def place_value_is_valency (m n : ℕ) (C : Type*) : (Fin (m * n) → C) ≃ (Fin m → Fin n → C) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl C)).trans (Equiv.curry (Fin m) (Fin n) C)

def time_of_day_is_three_place (C : Type*) : (Fin (24 * 60 * 60) → C) ≃ (Fin 24 → Fin 60 → Fin 60 → C) :=
  (place_value_is_valency (24 * 60) 60 C).trans
    (Equiv.arrowCongr (Equiv.refl _) (Equiv.refl _) |>.trans (place_value_is_valency 24 60 (Fin 60 → C)))

theorem seconds_in_a_day : 24 * 60 * 60 = 86400 := by norm_num

section Trojan
variable {Src Bin : Type*} [DecidableEq Src]

def trojan (honest : Src → Bin) (compilerSrc loginSrc : Src) (self badLogin : Bin) (s : Src) : Bin :=
  if s = compilerSrc then self else if s = loginSrc then badLogin else honest s

theorem trojan_invisible (honest : Src → Bin) (compilerSrc loginSrc : Src) (self badLogin : Bin) (s : Src)
    (h1 : s ≠ compilerSrc) (h2 : s ≠ loginSrc) :
    trojan honest compilerSrc loginSrc self badLogin s = honest s := by
  simp [trojan, h1, h2]

theorem trojan_reproduces (honest : Src → Bin) (compilerSrc loginSrc : Src) (self badLogin : Bin) :
    trojan honest compilerSrc loginSrc self badLogin compilerSrc = self := by
  simp [trojan]

end Trojan

theorem diverse_double_check_sound {Claim : Type*} (truth : Claim → Prop) (c₁ c₂ : Claim → Prop)
    (B₁ B₂ : Set Claim) (h₁ : ∀ x, x ∉ B₁ → c₁ x → truth x) (h₂ : ∀ x, x ∉ B₂ → c₂ x → truth x)
    (hdisj : Disjoint B₁ B₂) (x : Claim) (hx₁ : c₁ x) (hx₂ : c₂ x) : truth x := by
  by_cases hb : x ∈ B₁
  · exact h₂ x (Set.disjoint_left.mp hdisj hb) hx₂
  · exact h₁ x hb hx₁

end TrustingPlaces
