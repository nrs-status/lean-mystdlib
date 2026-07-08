import Mystdlib.DMap.Set.Defs
import Mystdlib.DMap.Lemmas

open Std Internal

namespace Map

variable [BEq α]

def keySet (m : Map α β) : Map.Set α :=
  ⟨m.inner.toList.map fun a => ⟨a.fst, Unit.unit⟩, by simp [List.DistinctKeys.def, List.pairwise_map]; have := m.inner.distinct; simp [DMap.keys, List.keys_eq_map, List.pairwise_map] at this; assumption⟩

