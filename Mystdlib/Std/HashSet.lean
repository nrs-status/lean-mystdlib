import Std

open Std

universe u
variable {α : Type u} [BEq α] [Hashable α]

def Std.HashSet.subset? (sa sb : HashSet α) : Bool :=
  sa.inter sb == sa
