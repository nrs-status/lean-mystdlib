import Std

open Std

unsafe inductive ExprMap (α : Type u)
| empty : ExprMap α
| mk 
  (bvar : HashMap Nat α)
  (app : ExprMap (ExprMap α))
  : ExprMap α


unsafe def myexprmap : ExprMap Nat :=
  .mk
    {(5,1)} -- lvl0 
    (.mk 
      {(5, .mk {} .empty), 
      (45, .mk {(1, 0), (2, 3), (50, 50)} (.mk {(0, .mk {(5, 10)} .empty), (1, .empty)} .empty))} 
      (.mk {(1, .mk {} .empty)} .empty))

/-
l {(5,1)}
r l 5 {}
r l 45 l {(1, 0), (2, 3), (50, 50)}
r l 45 r l 0 {(5, 10)}
r r l 1 {}
-/


unsafe def myexprmap' : ExprMap Nat :=
  .mk
    {(5,1)} -- lvl0 
    (.mk 
      {(5, .mk {} .empty), 
      (45, .mk {(1, 0), (2, 3), (50, 50)} (.mk {(0, .mk {(5, 10)} .empty), (1, .empty)} .empty))} 
      (.mk 
      {(1, .mk 
        {(1, .mk {} (.mk {} (.mk 
          {(9, .mk {(8, .mk {(1, 1), (5, 5), (7, 7)} .empty), (11, .empty)} (.mk {} .empty)),
          (10, .empty), 
          (100, .empty)} .empty)))} 
        .empty),
       (100, .mk {(1, .empty), 
                  (456, .mk {(5, 1), (4, 4)} .empty)} .empty)
            } .empty))



/-
l {(5,1)}
r l 5 {}
r l 45 l {(1, 0), (2, 3), (50, 50)}
r l 45 r l 0 {(5, 10)}
r l 45 r l 1 .empty
r r 1 l 1 r r l 9 l 8 {(1, 1), (5, 5), (7, 7)}
r r 1 l 1 r r l 9 l 11 .empty
r r 1 l 1 r r l 9 r {}
r r 1 l 1 r r l 10 .empty
r r 1 l 1 r r l 100 .empty
-/

