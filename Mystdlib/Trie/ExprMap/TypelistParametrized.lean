import Std
open Std

inductive ExprMap  (l : List Type) : Nat -> Type
| empty : ExprMap l n 
| mk
  (h : n < l.length)
  (bvar : HashMap Nat (l.get ⟨n, h⟩))
  (app : ExprMap l n.succ)
  : ExprMap l n


@[reducible]
def mylist : List Type := [
  Nat, 
  ExprMap [Nat, ExprMap [Nat, ExprMap [Nat] 0] 0, ExprMap [Nat, ExprMap [Nat] 0] 0] 0,
  ExprMap [Nat, ExprMap [Nat, ExprMap [Nat] 0] 0, ExprMap [Nat, ExprMap [Nat] 0] 0] 0,
  ExprMap [Nat, ExprMap [Nat, ExprMap [Nat] 0] 0, ExprMap [Nat, ExprMap [Nat] 0] 0] 0,
  ]

def myexprmap : ExprMap mylist 0 :=
  .mk (by grind) {(7, nat_lit 5)} (.mk (by grind) {} (.mk (by grind) {} (.mk (by grind) {} .empty)))
