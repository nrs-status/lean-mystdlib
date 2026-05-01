import Mystdlib.Metaprogramming.SyntaxOptics
import Lean

open Lean

open Tamb

def lensdefOfStructNField (structnm : Ident) (fieldnm : Ident) (fieldtyp : Syntax)  : DefStx :=
  let structnm := mkIdent structnm.getId.eraseMacroScopes
  let fieldnm := mkIdent fieldnm.getId.eraseMacroScopes
  let get := MacroM.tstx `((fun lensdefgen_x => lensdefgen_x.$(.mk fieldnm)))
  let set := MacroM.tstx `((fun lensdefgen_x lensdefgen_y => { lensdefgen_x with $(.mk fieldnm.raw):ident := lensdefgen_y }))
  {
    declid := ⟨structnm.getId.toString ++ "_" ++ fieldnm.getId.toString |>.toName, #[]⟩
    optdeclsig := .some <| MacroM.stx `(Lens' $(.mk fieldtyp) $(.mk structnm))
    body := MacroM.stx `(Lens.mk $get $set)
  }

open Lean Elab Command in
elab "#genfieldlenses" c:command : command =>
  match structure_stx_prism.preview c with
  | .some x => do
    let := x.fields
    |>.map (fun ⟨_, lhs, rhs⟩ => lensdefOfStructNField 
      (.mk <| mkCIdent x.declid.nm) (.mk <| mkIdent lhs) rhs)
    |>.map def_stx_prism.review
    elabCommand c
    this.forM elabCommand
  | .none => throwError m!"failed to match with structure stx prism"

def prismdefOfInductiveAlt (inductivenm : Ident) (ctornm : Ident) (ctortyp : Syntax) : DefStx :=
  let inductivenm := mkIdent inductivenm.getId.eraseMacroScopes
  let ctornm := mkIdent ctornm.getId.eraseMacroScopes
  let ctornm_w_prefix := MacroM.stx `(.$(.mk ctornm))
  let (head, rest) := arrow_iso_stx.view.{0,0} ctortyp
  let prodtyp := prod_iso_stx.review.{0,0} (head, rest.dropLast)
  let tuple_elms : Array Syntax := Array.range (1 + rest.dropLast.length)
    |>.map (fun n => mkCIdent ("genprismdef_tuple_x" ++ (toString n) |>.toName))
  let build_fn_body := app_iso_stx.review.{0,0} (ctornm_w_prefix, tuple_elms)
  let build_fn_arg := tuple_iso_stx.review.{0,0} (tuple_elms[0]!, tuple_elms.drop 1 |>.toList)
  let build := MacroM.stx `(fun $(.mk build_fn_arg) => $(.mk build_fn_body))
  let matchfn := MacroM.stx `((fun s => match s with | $(.mk build_fn_body) => Sum.inr $(.mk build_fn_arg) | x => Sum.inl x))
  { 
    declid := ⟨inductivenm.getId.toString ++ "_" ++ ctornm.getId.toString |>.toName, #[]⟩
    optdeclsig := .some <| MacroM.stx `(Prism' $(.mk prodtyp) $(.mk inductivenm))
    body := MacroM.stx `(Prism.mk $(.mk build) $(.mk matchfn))
  }

open Lean Elab Command in
elab "#genprisms" c:command : command =>
  match inductive_stx_prism.preview c with
  | .some x => do
    let := x.ctors
    |>.map (fun ctor => prismdefOfInductiveAlt (mkCIdent x.declid.nm) (mkCIdent ctor.nm) (arrow_iso_stx.review.{0,0} ctor.rhs.someD))
    |>.map def_stx_prism.review
    elabCommand c
    this.forM (fun s => do dbg_trace <- liftCoreM <| Lean.PrettyPrinter.ppCategory `command s; elabCommand s)
  | .none => throwError m!"failed to match with inductive stx prism"

/-
#genfieldlenses
structure mystructure : Type where
  xx : Nat
  yy : Bool

#check mystructure.xx
#print mystructure_xx
#print mystructure_yy
-/


/-
#genprisms
inductive mytyp
| mka : Nat -> mytyp
| mkb : Bool -> Nat -> mytyp

#check mytyp_mkb
-/
