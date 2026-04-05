import Lean

open Lean Elab Term Meta Expr

syntax (name := const_pdescr) "const " term : term

@[term_elab const_pdescr]
def const_elab : TermElab
| `(const $x), t? =>
  match t? with
  | .some t =>
    if Expr.isForall t 
    then Meta.forallTelescope t fun xs cod => do
      let constant_fn_result <- elabTermAndSynthesize x (.some cod)
      Meta.mkLambdaFVars xs constant_fn_result
    else do
      throwError 
        ("expected type " ++ toString (<- PrettyPrinter.ppExpr t) ++ " is not a function type")
  | .none => throwError "no expected type; an expected type is required"
| _, _ => throwUnsupportedSyntax

