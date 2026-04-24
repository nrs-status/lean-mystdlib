import Mystdlib.Optics.Tambara.Optics
import Mystdlib.Optics.Tambara.Combinators

namespace Tamb

class TupleGet (i : Nat) (prod : Type u) (selection : outParam (Type v)) where
  get : prod -> selection

instance : TupleGet 0 α α where
  get := id

instance : TupleGet 0 (Prod α β) α where
  get := Prod.fst

instance
  [TupleGet n ξ α]
  : TupleGet n.succ (Prod β ξ) α
  where
    get := TupleGet.get n ∘ Prod.snd

class TupleSet (i : Nat) (prod_type : Type u) (selection : outParam (Type v)) (new_selection_type : Type w) (new_prod_type : outParam (Type z)) where
  set : prod_type -> new_selection_type -> new_prod_type

instance : TupleSet 0 α α α' α' where
  set := fun _ => id

instance : TupleSet 0 (α × β) α α' (α' × β) where
  set := fun (_, b) a' => (a', b)

instance 
  [inst : TupleSet n ξ α α' ξ']
  : TupleSet n.succ (β × ξ) α α' (β × ξ') where
    set := fun (b, xξ) a' => have := inst.set xξ a'; (b, this)

def polyset
  (i : Nat)
  {prod_type : Type u}
  (xprod : prod_type)
  {new_selection_type : Type w}
  (new_selection : new_selection_type)
  [TupleSet i prod_type selection_type new_selection_type new_prod_type]
  : new_prod_type
  := TupleSet.set i xprod new_selection

def tuple {α β ς τ : Type u} (i : Nat) [TupleGet i ς α] [TupleSet i ς α β τ] : Lens α β ς τ :=
  .mk (TupleGet.get i) (TupleSet.set i)

def tuple' (i : Nat) [TupleGet i ς α] [TupleSet i ς α α ς] :=
  @tuple α α ς ς i










