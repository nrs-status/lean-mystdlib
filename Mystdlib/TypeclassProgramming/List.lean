
namespace List

class Concat (l : List α) (last : α) (result : outParam (List α)) where

instance : List.Concat [] x [x] where

instance [List.Concat l x l'] : List.Concat (x' :: l) x (x' :: l') where

class ReverseAux (l acc : List α) (result : outParam (List α)) where

instance : ReverseAux (α := α) [] l l where

instance [ReverseAux l (a :: acc) r] : ReverseAux (a :: l) acc r  where

class Reverse (l : List α) (result : outParam (List α)) where

instance [ReverseAux l [] r] : Reverse l r where

class ReverseAuxNOP (l acc r : List α)

instance : ReverseAuxNOP (α := α) [] l l where

instance [ReverseAuxNOP l (a :: acc) r] : ReverseAuxNOP (a :: l) acc r where

class ReverseNOP (l r : List α) where

instance [ReverseAuxNOP l [] r] : ReverseNOP l r where

class LengthNOP (l : List α) (n : Nat) where

instance : LengthNOP (α := α) [] 0 where

instance [LengthNOP l n] : LengthNOP (x :: l) (Nat.succ n) where



