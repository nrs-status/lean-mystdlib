import Std

open Std

instance [BEq α] [Ord α] [BEq β] [Hashable α] [Hashable β] : Hashable (TreeMap α β) where
  hash := hash ∘ TreeMap.toList

