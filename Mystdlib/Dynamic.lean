import Lean

deriving instance TypeName for String
deriving instance TypeName for Bool
deriving instance TypeName for Nat
deriving instance TypeName for Int
deriving instance TypeName for Lean.Expr

instance : Inhabited Dynamic where
  default := Dynamic.mk Nat.zero

