
def iterate (f : Type -> Type) : Nat -> Type
| .zero => Thunk Empty
| .succ n => f (iterate f n)

def Fix (f : Type -> Type) := Σn, iterate f n

@[reducible]
def ListF (α β : Type) := Unit ⊕ (α × β)

@[reducible]
def List' (α : Type) := Fix (ListF α)

