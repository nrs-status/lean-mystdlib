import Lean

open Lean

instance : ToMessageData Exception where
  toMessageData := Lean.Exception.toMessageData

instance [ToMessageData ε] [ToMessageData α] : ToMessageData (Except ε α) where
toMessageData := fun
| .ok x => m!"Except.ok {x}"
| .error x => m!"Except.error {x}"

macro "_throwError" : term => `(throwError "NO ERROR SPECIFIED")

macro "throw_notype" : term => `(throwError m!"elaborator {decl_name%} requires an expected type but there is none")

