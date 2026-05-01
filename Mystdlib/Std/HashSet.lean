import Std

open Std

universe u
variable {α : Type u} [BEq α] [Hashable α] [DecidableEq α]

def Std.HashSet.isSubset (sa sb : HashSet α) : Bool :=
  sa.inter sb == sa

variable [EquivBEq α]  [LawfulHashable α] [LawfulBEq α]
example {x y : α} : (HashSet.contains (HashSet.insert .emptyWithCapacity y) x) -> x = y := by grind


