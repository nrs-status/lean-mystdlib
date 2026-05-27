import Lean

deriving instance TypeName for String
deriving instance TypeName for Bool
deriving instance TypeName for Nat
deriving instance TypeName for Int
deriving instance TypeName for Lean.Expr
deriving instance TypeName for Lean.Syntax
deriving instance TypeName for Lean.Name

instance : Inhabited Dynamic where
  default := Dynamic.mk Nat.zero

def Dynamic.get! (α : Type u) [Inhabited α] [TypeName α] (v : Dynamic) : α :=
  match v.get? α with
  | .some x => x
  | .none => panic! "Dynamic.get! failed"
