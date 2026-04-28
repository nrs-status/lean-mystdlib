import Mystdlib.Optics.Tambara.Combinators
import Mystdlib.Optics.Tambara.Optics
import Mystdlib.Optics.Tambara.Traversal

open Tamb

class Plated α where
  plate : Traversal' α α

def children
  [Plated α]
  : α -> List α
  := toListOf Plated.plate


partial def transformOf
  [Nonempty β]
  (x : ProfOptic l α β α β)
  [Tambs l (Replacing α β)]
  : (β -> β) -> α -> β
  := fun f => over x (transformOf x f)

def mylist := [7, 5, 6]

def mytraversed := traversed' (F := List) (α := Nat)

inductive mytype
| a (x : Nat)
| b (x : Nat) (l : List mytype)
deriving Repr, Inhabited

def myterm := mytype.b 0 
  [.b 0 [.a 0], 
  .b 0 [.a 0], 
  .a 0]

def mythingaux : mytype -> List mytype × (List mytype -> mytype) := fun
  | .a x => ([.a x], fun l' => l'[0]!)
  | .b x l =>
    (.b x l :: l, fun | .cons (.b x' l') xs => .b x' xs | _ => panic! "error")

def mytraversal := Traversal.mk mythingaux

def neoterm := mytype.b 0 [.a 0, .a 0, .b 0 [.a 1]]

#eval over mytraversal (fun | .a n => .a n.succ | .b n l => .b n.succ l) neoterm

