
class TCLE (x y : Nat) where

instance : TCLE x x where

instance [TCLE x y] : TCLE x (Nat.succ y) where

class TCLT (x y : Nat) where

instance [TCLE x y] : TCLT x (Nat.succ y) where

class TCAdd (x y : Nat) (result : outParam Nat) where

instance : TCAdd 0 x x where

instance : TCAdd x 0 x where

instance [TCAdd x y z] : TCAdd (Nat.succ x) y (Nat.succ z) where

instance [TCAdd x y z] : TCAdd x (Nat.succ y) (Nat.succ z) where

