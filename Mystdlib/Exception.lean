import Lean

section
open Lean

instance : ToMessageData Exception where
  toMessageData := Lean.Exception.toMessageData

instance [ToMessageData ε] [ToMessageData α] : ToMessageData (Except ε α) where
toMessageData := fun
| .ok x => m!"Except.ok {x}"
| .error x => m!"Except.error {x}"

macro "_throwError" : term => `(throwError "NO ERROR SPECIFIED")


macro "unreachable" : term => `(throwError "reached code that is expected to be unreachable")
end

section
macro "throw_notype" : term => `(throwError m!"elaborator {decl_name%} requires an expected type but there is none")

end

section
open  Lean Elab Term PrettyPrinter

def Lean.MacroM.stxNomatch (decl_name : Name) (stx : Syntax) : MacroM α :=
  throw <| .error stx (decl_name.toString ++ ": unsupported syntax in MacroM:\n" ++ toString stx)

def Lean.Elab.Term.TermElabM.stxNomatch (decl_name : Name) (stx : Syntax) : TermElabM α := do
  let stx_format <- ppCategory `term stx
  throwError m!"{decl_name}: unsupported syntax in TermElabM:\n{stx_format}"

def Lean.Elab.Command.CommandElabM.stxNomatch (decl_name : Name) (stx : Syntax) : CommandElabM α := do
  let stx_format <- liftCoreM <| ppCategory `command stx
  throwError m!"{decl_name}: unsupported syntax in CommandElabM:\n{stx_format}"

macro "stxNomatch" stx:term : term => `(.stxNomatch decl_name% $stx)

end
