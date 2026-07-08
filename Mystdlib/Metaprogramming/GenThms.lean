import Mystdlib.Metaprogramming.SyntaxOptics
import Lean 
import Qq

open Lean Elab Term Meta Command Tactic

open Qq

unsafe def evalExprToExpr (target targetType : Expr) : TermElabM Expr := do
  let evalExpr_expr <- mkAppM ``evalExpr #[targetType, toExpr targetType, toExpr target, q(DefinitionSafety.unsafe), q(Bool.true)]
  let delab <- Lean.PrettyPrinter.delab evalExpr_expr
  let stx <- `(do let r <- $(.mk delab):term; return toExpr r)
  (<- evalTerm (TermElabM Expr) q(TermElabM Expr) stx .unsafe)

def eqOfTermElab  (β : Expr -> Type u) (elab_ : (e : Expr) -> β e -> TermElabM Expr) : (e : Expr) -> β e -> TermElabM Expr := fun e βe => do
  mkAppM ``Eq #[e, <- elab_ e βe]

unsafe def eqOfEvalExprToExpr (target targetType : Expr) : TermElabM Expr := 
  eqOfTermElab (fun _ => Expr) (fun x y => evalExprToExpr x y) target targetType

unsafe def eqOfEvalExprToExpr' (target : Expr) : TermElabM Expr :=
  eqOfTermElab (fun _ => Unit) (fun x _ => do evalExprToExpr x (<- inferType x)) target .unit

def reduceWithTacticSeq (target : Expr) (tacticSeq : Lean.Syntax) : TermElabM Expr := do
  let mvarExpr <- mkFreshExprMVar target
  let r <- Tactic.run mvarExpr.mvarId! (evalTactic tacticSeq)
  return (<- r[0]!.getType)

def eqOfTacticSeq (target : Expr) (tacticSeq : Lean.Syntax) : TermElabM Expr := do
  eqOfTermElab (fun _ => Lean.Syntax) reduceWithTacticSeq target tacticSeq

def delabbing (x : TermElabM Expr) : TermElabM Syntax := do
  let r <- x
  return <- Lean.PrettyPrinter.delab r

def genThm (decl_nm : Name) (statement : Syntax) (body : Syntax) : CommandElabM Unit := do
  elabCommand <| thm_stx_prism.review {
    declid := ⟨decl_nm, #[]⟩
    typespec := statement
    body := body
  }


unsafe def mkExprEvalToExprEq_arrayAssignment (e : Expr) (eta_expand? : Bool) (assignments : Array (Option Expr)) : TermElabM Expr := do
  let target <- if eta_expand? then etaExpand e else do return e
  let (mvars, _, instantiatedExpr) <- lambdaMetaTelescope target
  discard <| assignments.zipIdx.mapM fun | (.none, _) => return | (.some x, n) => discard <| isDefEq mvars[n]! x
  let e' <- instantiateMVars instantiatedExpr
  let r <- Expr.getBinderName target
  dbg_trace r
  let r' := Expr.getForallBinderNames (<- inferType target)
  dbg_trace r'
  eqOfEvalExprToExpr' e' 

unsafe def mkExprEvalToExprEq_hashMapAssignment (e : Expr) (eta_expand? : Bool) (assignments : Std.HashMap Name Expr) : TermElabM Expr := do
  let target <- if eta_expand? then etaExpand e else do return e
  let binder_names := Expr.getForallBinderNames (<- inferType target)
  let assignments := binder_names.toArray.map fun nm => assignments.get? nm
  mkExprEvalToExprEq_arrayAssignment e eta_expand? assignments

unsafe def mkExprEvalToExprEq (e : Expr) (eta_expand? : Bool) (assignments : Array (Option Expr) ⊕ Std.HashMap Name Expr) : TermElabM Expr := match assignments with
| .inl x => mkExprEvalToExprEq_arrayAssignment e eta_expand? x
| .inr x => mkExprEvalToExprEq_hashMapAssignment e eta_expand? x
