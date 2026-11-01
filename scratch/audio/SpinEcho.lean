import Mathlib

/-!
# Echoes on the 3-sphere keep their loudness

A stereo frame of analytic (holomorphic) signals is a pair `(z₁, z₂)` of complex numbers. A unit-norm pair is a point
of the 3-sphere. An element of SU(2) is `[[a, -conj b], [b, conj a]]` with `|a|² + |b|² = 1`.

PROVED:
* `su2_preserves_energy`: applying an SU(2) element to a stereo frame keeps `|z₁|² + |z₂|²` exactly, so every echo
  that is rotated around the 3-sphere this way has the loudness of the original, before any decay is applied.
* `pingpong_preserves_energy`, `pingpong_twice`: swapping the channels (classic ping-pong) also keeps the energy, and
  swapping twice brings the sound back to where it started.
INTERPRETED (not formalized): the analytic signal as the holomorphic extension of a real signal; the echo path as a
walk on the 3-sphere whose shadow on the 2-sphere (the Hopf map) is the stereo image.
-/

namespace SpinEcho
open Complex ComplexConjugate

theorem su2_preserves_energy (a b z₁ z₂ : ℂ) (h : normSq a + normSq b = 1) :
    normSq (a * z₁ - conj b * z₂) + normSq (b * z₁ + conj a * z₂) = normSq z₁ + normSq z₂ := by
  simp only [normSq_apply, sub_re, sub_im, add_re, add_im, mul_re, mul_im, conj_re, conj_im] at h ⊢
  linear_combination (z₁.re * z₁.re + z₁.im * z₁.im + z₂.re * z₂.re + z₂.im * z₂.im) * h

theorem pingpong_preserves_energy (z₁ z₂ : ℂ) : normSq z₂ + normSq z₁ = normSq z₁ + normSq z₂ := add_comm _ _

theorem pingpong_twice (z₁ z₂ : ℂ) : ((z₁, z₂).swap).swap = (z₁, z₂) := rfl

end SpinEcho
