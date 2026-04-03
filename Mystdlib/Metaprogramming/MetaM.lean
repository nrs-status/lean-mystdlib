import Lean

open Lean

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
