import Mathlib.Data.PFunctor.Univariate.M

inductive ListA (α : Type u) 
| nil
| cons : α -> ListA α
deriving DecidableEq, Repr

def ListPFunctor.{u} (α : Type u) : PFunctor.{u, u} where
  A := ListA α
  B := fun
  | .nil => PEmpty
  | .cons _ => PUnit

def range : (ListPFunctor Nat).M :=
  PFunctor.M.corec 
    (X := Nat) 
    (fun n => .mk (.cons n) fun .unit => n.succ)
    0

/--
info: [ListA.cons 0,
 ListA.cons 1,
 ListA.cons 2,
 ListA.cons 3,
 ListA.cons 4,
 ListA.cons 5,
 ListA.cons 6,
 ListA.cons 7,
 ListA.cons 8,
 ListA.cons 9]
-/
#guard_msgs in
#eval List.iterate (fun x => 
  match h : x.head with 
  | .nil => .mk ⟨.nil, nofun⟩ -- not reached in this example
  | .cons _ => x.children (h ▸ .unit)) range 10
  |>.map (·.head)



