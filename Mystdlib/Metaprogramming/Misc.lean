import Lean

open Lean

-- MacroM

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


--

def Lean.Name.explicit_repr : Lean.Name -> String
| .anonymous => ".anonymous"
| .num nm nat => ".num " ++ "(" ++ nm.explicit_repr ++ ") " ++ toString nat
| .str nm s => ".str " ++ "(" ++ nm.explicit_repr ++ ") " ++ s


-- MetaM

def getLamVarsDecls (lam_expr : Expr) : MetaM (Array LocalDecl) := do
  let opt_decls <- Meta.lambdaTelescope lam_expr (fun ar _body => do
    let lctx <- getLCtx
    ar.mapM (fun e => .pure <| lctx.findFVar? e)
    )
  .pure opt_decls.reduceOption

def getLamVarsUserNames (lam_expr : Expr) : MetaM (Array String) := do
  let decls <- getLamVarsDecls lam_expr
  return decls.map (Name.toString ∘ LocalDecl.userName)

def getLamConstVarsUserNames (nm : Name) : MetaM (Array String) := do
  let constInfo <- getConstInfoDefn nm
  getLamVarsUserNames constInfo.value
