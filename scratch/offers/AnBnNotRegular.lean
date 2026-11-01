import Mathlib

/-!
# The language a^n b^n is not regular

Alphabet `Bool`, with `false` read as `a` and `true` read as `b`.

PROVED
* `AnBnNotRegular.mem_L_iff`: `w ∈ L` iff `w = a^n b^n` for some `n` (definitional unfolding).
* `AnBnNotRegular.replicate_mem_L_iff`: `a^j b^i ∈ L` iff `j = i`.
* `AnBnNotRegular.dfa_accepts_ne`: no DFA over `Bool` whose state type is `Finite`
  (in any universe) has `M.accepts = L`.
* `AnBnNotRegular.not_isRegular`: `¬ L.IsRegular`.

Proof: the map `i ↦ M.eval (a^i)` from `ℕ` to a finite state type is not injective, so
`a^i` and `a^j` reach the same state for some `i ≠ j`; then `a^i b^i` and `a^j b^i` are
either both accepted or both rejected, while exactly the first lies in `L`.
-/

namespace AnBnNotRegular

/-- The language `{aⁿbⁿ | n ∈ ℕ}` over `Bool`, with `false = a`, `true = b`. -/
def L : Language Bool :=
  {w | ∃ n, w = List.replicate n false ++ List.replicate n true}

theorem mem_L_iff (w : List Bool) :
    w ∈ L ↔ ∃ n, w = List.replicate n false ++ List.replicate n true := Iff.rfl

theorem replicate_mem_L_iff (i j : ℕ) :
    List.replicate j false ++ List.replicate i true ∈ L ↔ j = i := by
  constructor
  · rintro ⟨n, hn⟩
    have h1 := congrArg (List.count false) hn
    have h2 := congrArg (List.count true) hn
    simp [List.count_replicate] at h1 h2
    omega
  · rintro rfl
    exact ⟨j, rfl⟩

theorem dfa_accepts_ne {σ : Type*} [Finite σ] (M : DFA Bool σ) : M.accepts ≠ L := by
  intro hM
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => M.eval (List.replicate k false))
  have key : M.eval (List.replicate i false ++ List.replicate i true) =
      M.eval (List.replicate j false ++ List.replicate i true) := by
    simp only [DFA.eval, DFA.evalFrom_of_append] at heq ⊢
    rw [heq]
  have hi : List.replicate i false ++ List.replicate i true ∈ M.accepts := by
    rw [hM]; exact (replicate_mem_L_iff i i).2 rfl
  have hj : List.replicate j false ++ List.replicate i true ∈ M.accepts := by
    rw [DFA.mem_accepts] at hi ⊢
    rwa [← key]
  rw [hM, replicate_mem_L_iff] at hj
  exact hij hj.symm

theorem not_isRegular : ¬ L.IsRegular := by
  rintro ⟨σ, _, M, hM⟩
  exact dfa_accepts_ne M hM

end AnBnNotRegular
