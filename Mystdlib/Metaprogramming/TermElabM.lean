import Lean

open Lean Elab Term

def declTypeOfNm (nm : Name) : TermElabM Expr := do
  let decl_typ := (<- getLCtx).getFromUserName! nm |>.type
  return (<- instantiateExprMVars decl_typ)

--

inductive DeclPrintInfoα 
| nm | expr | expr_repr | expr_typ | expr_typ_repr 
deriving BEq, Hashable, Repr

@[reducible]
def DeclPrintInfoβ : DeclPrintInfoα -> Type
| .nm => Name
| .expr => Expr
| .expr_repr => Format
| .expr_typ => Expr
| .expr_typ_repr => Format

def DeclPrintInfo := Std.DHashMap DeclPrintInfoα DeclPrintInfoβ

def declPrintInfos : TermElabM (Array DeclPrintInfo) := do
  let lctx <- getLCtx
  let r : PersistentArray (Option DeclPrintInfo) <- lctx.decls.mapM fun decl? => do
    let .some decl := decl? | return Option.none
    let typ <- Lean.Meta.inferType decl.toExpr
    return .some <| Std.DHashMap.ofList [
      .mk .nm decl.userName,
      .mk .expr decl.toExpr,
      .mk .expr_repr (repr decl.toExpr),
      .mk .expr_typ typ,
      .mk .expr_typ_repr (repr typ)
    ]
  return r.toArray |>.reduceOption

instance {a : DeclPrintInfoα} : ToMessageData (DeclPrintInfoβ a) where
  toMessageData ba := by cases a; all_goals simp [DeclPrintInfoβ] at ba; exact
    (toMessageData ba)

def printDeclPrintInfo (x : DeclPrintInfo) : TermElabM Unit := do
  x.forM fun k v => logInfo m!"{repr k}: {v}"

