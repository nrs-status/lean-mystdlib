import Lean
import Qq

syntax (name := _let_arrow_pdescr) "_let " term " <- " term doSeq : doElem
syntax (name := _let_pdescr) "_let " term " := " term doSeq : doElem

set_option backward.do.legacy false

macro_rules
| `(doElem|_let $x:term := $y:term $rest:doSeq) => 
  `(doElem|match $y:term with | $x => $rest | _ => throwError "unimplemented _let error")
| `(doElem|_let $x:term <- $y:term $rest:doSeq) =>
  `(doElem|match <- $y:term with | $x => $rest | _ => throwError "unimplemented _let error")



/-
previous version; kept because useful example of DoElab

syntax (name := _let_arrow_pdescr) "_let " term " <- " term : doElem
syntax (name := _let_pdescr) "_let " term " := " term : doElem
open Lean Elab Do
open Lean Parser Term

open Qq

@[doElem_elab _let_pdescr]
def _let_elab : DoElab := fun stx cont =>
  match stx with
| `(doElem|_let $pat := $rhs) => do
  let mt <- mkMonadicType (<- read).doBlockResultType
  doElabToSyntax "_let" cont.continueWithUnit fun body => do
    let stx <- `(match $rhs:term with | $pat => $body | _ => _throwError)
    elabTerm stx mt
| _ => throwUnsupportedSyntax


@[doElem_elab _let_arrow_pdescr]
def _let_arrow_elab : DoElab := fun stx cont =>
  match stx with
  | `(doElem|_let $pat <- $rhs) => do
    let mt <- mkMonadicType (<- read).doBlockResultType
    doElabToSyntax "_let" cont.continueWithUnit fun body => do
      let stx <- `(bind $rhs (fun _x => match _x with | $pat => $body | _ => _throwError))
      elabTerm stx mt
  | _ => throwUnsupportedSyntax
-/


