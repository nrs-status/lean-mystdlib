import Std

open Std

universe u
variable {α : Type u} [BEq α] [Hashable α] [DecidableEq α]

def Std.HashSet.isSubset (sa sb : HashSet α) : Bool :=
  sa.inter sb == sa

variable [EquivBEq α]  [LawfulHashable α] [LawfulBEq α] -- these are the minimal instances needed for automation with grind and simp to work nicely with hash types
example {x y : α} : (HashSet.contains (HashSet.insert .emptyWithCapacity y) x) -> x = y := by grind


