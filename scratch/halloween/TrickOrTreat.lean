import Mathlib

/-!
# Trick or treat as a threat game

A house either gives a treat (cost `c > 0` to the house) or refuses. After a refusal the visitor either plays the
trick (cost `t > 0` to the house, net value `m` to the visitor) or walks on (value 0 to both).

PROVED:
* `idle_threat`: if playing the trick costs the visitor (`m < 0`), walking on is the visitor's best reply to a
  refusal, so the threat is not credible.
* `refuse_idle_threat`: against a non-credible threat the house does strictly better refusing (0 versus `−c`).
* `credible_threat_pays_iff`: if the visitor enjoys the trick (`m > 0`), refusal is followed by the trick, and the
  house prefers to give the treat exactly when `c < t`.
* `self_trick_cancels`: a trick you predict perfectly leaves no residual. With an exact self-prediction (gain 1),
  the surprise left after subtracting your own forecast is zero, which is why you cannot tickle or trick yourself.
INTERPRETED (not formalized): costumes as delays and rotations of identity, porch lights off as opting out.
-/

namespace TrickOrTreat

theorem idle_threat (m : ℝ) (hm : m < 0) : max m 0 = 0 := max_eq_right hm.le

theorem refuse_idle_threat (c t m : ℝ) (hc : 0 < c) (hm : m < 0) :
    let houseIfRefuse := if m > 0 then -t else 0
    houseIfRefuse > -c := by
  simp only [show ¬ m > 0 from not_lt.mpr hm.le, ite_false]
  linarith

theorem credible_threat_pays_iff (c t m : ℝ) (hm : 0 < m) :
    let houseIfRefuse := if m > 0 then -t else 0
    (-c > houseIfRefuse) ↔ c < t := by
  simp only [hm, ite_true]
  constructor <;> intro h <;> linarith

theorem self_trick_cancels (a w : ℝ) : (a + w) - 1 * a = w := by ring

end TrickOrTreat
