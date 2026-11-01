import Mathlib

/-!
# Sleeping Beauty comes apart along the accounting

Fair coin. Heads: one awakening; Tails: two awakenings, with the memory erased between them (copies in time that she
cannot recognize). At each awakening she may buy, for price `x`, a ticket paying `1` if Heads.

* SB1 `per_awakening_breakeven`: if every awakening's purchase settles (credit summed over copies), the fair price is
  `1/3`: thirder / SIA.
* SB2 `per_world_breakeven`: if a world settles at most one purchase (credit per world), the fair price is `1/2`:
  halfer / SSA.

The probability is not the primitive. The fair price is fixed by how credit is routed over unrecognized copies, as in
Armstrong's anthropic decision theory.
-/

namespace SleepingBeauty

/-- **SB1.** Per-awakening settlement: expected profit `½(1 − x) + ½·2(−x)` is zero iff `x = 1/3`. -/
theorem per_awakening_breakeven (x : ℝ) : (1 / 2) * (1 - x) + (1 / 2) * (2 * (0 - x)) = 0 ↔ x = 1 / 3 := by
  constructor <;> intro h <;> linarith

/-- **SB2.** Per-world settlement: expected profit `½(1 − x) + ½(−x)` is zero iff `x = 1/2`. -/
theorem per_world_breakeven (x : ℝ) : (1 / 2) * (1 - x) + (1 / 2) * (0 - x) = 0 ↔ x = 1 / 2 := by
  constructor <;> intro h <;> linarith

end SleepingBeauty
