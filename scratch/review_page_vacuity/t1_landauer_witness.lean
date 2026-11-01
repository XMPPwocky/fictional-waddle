import Mathlib
/-! Vacuity sweep test 1: are LandauerCounting L1/L2's hypotheses satisfiable with |S| ≥ 2 and a nonempty E₀,
and is the bound |S|·|E₀| ≤ |E| attained?  Witness: S = Bool, E = Bool × Bool, E₀ = {e | e.1 = false}, f = swap. -/
namespace ReviewVacuity1

def f : Bool × (Bool × Bool) → Bool × (Bool × Bool) := fun p => (p.2.1, (p.1, p.2.2))

theorem f_inj : Function.Injective f := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [f, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  subst h1 h2 h3; rfl

def E0 : Finset (Bool × Bool) := Finset.univ.filter (fun e => e.1 = false)

theorem herase : ∀ s e, e ∈ E0 → (f (s, e)).1 = false := by
  intro s e he
  simp only [E0, Finset.mem_filter, Finset.mem_univ, true_and] at he
  simp [f, he]

/-- The L2 bound is tight here: 2 · 2 = 4 = |E|. -/
theorem tight : Fintype.card Bool * E0.card = Fintype.card (Bool × Bool) := by decide

/-- And L1's image count is exactly |S|·|E₀| = 4 for this witness. -/
theorem image_count : ((Finset.univ ×ˢ E0).image (fun p => (f p).2)).card = 4 := by decide

end ReviewVacuity1
