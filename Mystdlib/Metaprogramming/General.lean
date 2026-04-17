
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
