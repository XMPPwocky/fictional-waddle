/-
# A map from Bifröst to Bitfrost with a fixed point

`bridgeMap` sends features of the mythical bridge to features of the OLPC security model, and
sends every other string to itself.

PROVED
- `request_fixed`: the request that asked for this map is a fixed point of it.
- `name_maps`, `fire_maps`: two sample entries.

INTERPRETED (not formalized)
- A quine is a fixed point (Kleene's recursion theorem). Here the fixed point is a sentence, not a
  program printing its own source.
-/

import Mathlib

namespace BifrostMap

def request : String :=
  "give me a map between bifrost and bitfrost, include this sentence in it so it quines"

def bridgeMap : String → String
  | "Bifröst" => "Bitfrost"
  | "a bridge between two realms" => "a boundary that carries one bit: allowed or denied"
  | "of three colors, and very strong" => "three factors: something you know, have, and are"
  | "Heimdall guards the crossing" => "the Security Center grants; programs only ask"
  | "the red band is fire that keeps the giants off" => "frost: the name keeps what the bridge kept out"
  | "yet must it be broken" => "no perfect security; judged only once deployed"
  | s => s

theorem request_fixed : bridgeMap request = request := by
  unfold bridgeMap request
  rfl

theorem name_maps : bridgeMap "Bifröst" = "Bitfrost" := by
  unfold bridgeMap
  rfl

theorem fire_maps :
    bridgeMap "the red band is fire that keeps the giants off" =
      "frost: the name keeps what the bridge kept out" := by
  unfold bridgeMap
  rfl

end BifrostMap

#print axioms BifrostMap.request_fixed
#print axioms BifrostMap.name_maps
#print axioms BifrostMap.fire_maps
