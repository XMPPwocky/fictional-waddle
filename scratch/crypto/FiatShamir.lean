/-
# Fiat–Shamir breaks exactly where the prover can solve a self-referential equation

A Schnorr-style identification protocol over a field K: public generator g and public key
y = x · g for a secret x. The prover sends a commitment a, receives a challenge c, and answers z;
the verifier accepts when z · g = a + c · y. Fiat–Shamir replaces the random challenge by c = H(a).

PROVED
1. `honest_accepts`: with the secret x, the answer z = r + c x to the commitment a = r g is accepted.
2. `simulate`: without the secret, for ANY challenge c and answer z, the commitment a = z g − c y is
   accepted. A prover who knows the challenge before committing can always pass.
3. `special_soundness`: two accepted answers to the same commitment under different challenges reveal
   the secret: y = ((z − z')/(c − c')) · g. So a prover who can answer two challenges for one
   commitment can compute x.
4. `one_challenge_without_secret`: if the prover cannot produce x, then for each commitment at most one
   challenge can be answered: answering two would give x by item 3.
5. `fs_fixed_point_forgery`: under Fiat–Shamir, any commitment a satisfying the fixed-point equation
   a = z g − H(a) y yields an accepted proof (a, H(a), z) with no secret.
6. `constant_hash_forgery`: if H ignores its input (H a = c₀ for all a), such a fixed point always
   exists, so every statement can be "proved".

INTERPRETED (not formalized)
- Fiat–Shamir is sound only when the prover cannot solve the self-referential equation a = z g − H(a) y,
  a fixed point of a map that contains the hash itself. Goldwasser and Kalai (2003) built protocols for
  which every concrete hash admits such self-reference; the random-oracle model assumes it away.
-/

import Mathlib

namespace FiatShamir

variable {K : Type*} [Field K]

def Accepts (g y a c z : K) : Prop := z * g = a + c * y

theorem honest_accepts (g x r c : K) : Accepts g (x * g) (r * g) c (r + c * x) := by
  unfold Accepts; ring

theorem simulate (g y c z : K) : Accepts g y (z * g - c * y) c z := by
  unfold Accepts; ring

theorem special_soundness (g y a c c' z z' : K) (hc : c ≠ c') (h1 : Accepts g y a c z)
    (h2 : Accepts g y a c' z') : y = ((z - z') / (c - c')) * g := by
  unfold Accepts at h1 h2
  have hcc : c - c' ≠ 0 := sub_ne_zero.mpr hc
  have key : (z - z') * g = (c - c') * y := by linear_combination h1 - h2
  field_simp
  linear_combination key.symm

theorem one_challenge_without_secret (g y a : K)
    (hnox : ¬ ∃ x : K, y = x * g) (c c' z z' : K) (h1 : Accepts g y a c z) (h2 : Accepts g y a c' z') :
    c = c' := by
  by_contra hc
  exact hnox ⟨(z - z') / (c - c'), special_soundness g y a c c' z z' hc h1 h2⟩

theorem fs_fixed_point_forgery (H : K → K) (g y a z : K) (hfix : a = z * g - H a * y) :
    Accepts g y a (H a) z := by
  unfold Accepts
  linear_combination -hfix

theorem constant_hash_forgery (c₀ g y z : K) :
    ∃ a, a = z * g - (fun _ => c₀) a * y ∧ Accepts g y a ((fun _ => c₀) a) z :=
  ⟨z * g - c₀ * y, rfl, simulate g y c₀ z⟩

end FiatShamir

#print axioms FiatShamir.honest_accepts
#print axioms FiatShamir.simulate
#print axioms FiatShamir.special_soundness
#print axioms FiatShamir.one_challenge_without_secret
#print axioms FiatShamir.fs_fixed_point_forgery
#print axioms FiatShamir.constant_hash_forgery
