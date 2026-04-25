
open Lean

def MacroM.run (x : Lean.MacroM α) : Option α :=
  let r := x.run {
    methods := default
    quotContext := `InOptics
    ref := .missing
    currMacroScope := 0
  } default
  match r with
  | .ok x _ => x
  | .error _ _ => .none



def MacroM.stx (x : MacroM Syntax) : Syntax :=
  MacroM.run x |>.elim .missing id

def MacroM.tstx (x : MacroM (TSyntax k)) : TSyntax k :=
  MacroM.run x |>.elim (.mk .missing) id

