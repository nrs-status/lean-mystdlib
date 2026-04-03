import Mystdlib.Metaprogramming.Syntax
import Mystdlib.Recursive
import Mystdlib.Array
import Batteries.Data.Array

open Recursive


open Lean


def Lean.Syntax.getAnonVarId? (stx : Syntax) : Option Nat :=
  stx.getAtLeaf? #[`anon_fn_var_pdescr, `num] >>= (fun | .inl x => .some x.toNat! | _ => .none)

def anon_fn_collect_wf (ar : Array Nat) : Bool :=
  let starts_at_zero := 0 ∈ ar
  let correct_ordering := if h : ar.sortDedup.size < 2
    then Bool.true
    else ar.sortDedup.tuplize 2 !p !p |>.foldl (fun prev ar => prev && decide (ar[0]!.succ = ar[1]!)) .true
  starts_at_zero && correct_ordering

def anon_fn_vars_to_fvars (stx : Syntax) : Syntax :=
  replace stx
    (match ·.getAnonVarId? with | .some n => return mkIdent ("__anon_fn_var_" ++ toString n).toName | _ => .none)

syntax (name := anon_fn_var_pdescr) "%" num : term
syntax (name := anon_fn_pdescr) "#(" term ")" : term

open Elab Term in
@[term_elab anon_fn_pdescr]
def elab_anon_fn : TermElab
| `(#($x)), t? => do
  let var_ids := collect x.raw Lean.Syntax.getAnonVarId? |>.dedupSorted
  if ¬ var_ids.isEmpty
  then
    let fun_binders := var_ids.map ("__anon_fn_var_" ++ toString ·)
    let fn_body <- Lean.PrettyPrinter.formatTerm (anon_fn_vars_to_fvars x.raw)
    elabTerm (<- constructTerm <| #["fun"] ++ fun_binders ++ #["=>", toString fn_body]) t?
  else do elabTerm (<- `(fun _ => $x)) t?
| _, _ => throwUnsupportedSyntax



