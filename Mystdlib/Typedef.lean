import Mystdlib.Metaprogramming.SyntaxOptics
import Mystdlib.Exception
import Lean

/-
automatically generate a model structure type from an unsafe declaration
-/

open Lean

section
open Parser Command

def skipUntil (pred : Char → Bool) : Parser where
  fn :=
    andthenFn
      (takeUntilFn pred)
      (takeWhileFn Char.isWhitespace)

def skipUntilWs : Parser := skipUntil Char.isWhitespace

def skipUntilWsOrDelim : Parser := skipUntil fun c =>
  c.isWhitespace || c == '(' || c == ')' || c == ':' || c == '{' || c == '}' || c == '|'

def typedef_body := recover declId skipUntilWsOrDelim >> ppIndent optDeclSig >> optional (symbol " :=" <|> " where") >>
  many ctor >> optional (ppDedent ppLine >> computedFields) >> optDeriving
end

open Elab Command Term

open Tamb

syntax (name := typedef_pdescr) "typedef " typedef_body : command

def genUnsafeInductiveDecl : Macro
| `(typedef $declid:declId $optdeclsig $[where]? $ctors* $[$cfields]? $optderiving) =>
  `(unsafe inductive $declid $optdeclsig where $ctors* $[$cfields]? $optderiving)
| _ => Macro.throwUnsupported

-- make model type from result of elaborating the unsafe inductive
def mkModelStructureStx (inductive_view_nm : Name) (inductive_view_binders : Array Syntax) (typector_typ : Syntax) (ctors : Array (Syntax × Syntax)) : Syntax :=
    let typ_field_type := inductive_view_binders
    |> (fun ar => if h : ar.isEmpty then (typector_typ, []) else (ar.back !p, ar.push typector_typ |>.toList)) 
    |> arrow_iso_stx.review.{0,0}
    let ctor_types_replacing_head := (each <∘> arrow_iso_stx <∘> arrow_last <∘> app_iso_stx <∘> tuple 0).set (mkIdent `typ) (ctors.map Prod.snd)
    let field_idents := #[mkIdent `typ] ++ (ctors.map Prod.fst)
    let field_types := #[typ_field_type] ++ ctor_types_replacing_head
    let fields := field_idents.zip field_types 
      |>.map (fun (lhs, rhs) => MacroM.stx `(Lean.Parser.Command.structSimpleBinder|$(.mk lhs):ident : $(.mk rhs)))
    let structure_stx := structure_stx_prism.review { 
      declmods := default
      declid := ⟨inductive_view_nm.toString ++ "_impl" |>.toName, #[]⟩
      optdeclsig := .none
      fields := fields.filterMap structure_field_stx_prism.preview
      optderiving := #[]
      }
    structure_stx


section

open private checkNoInductiveNameConflicts elabInductiveViews FinalizeContext from Lean.Elab.MutualInductive

def elabMutualInductiveInfo (elems : Array Syntax) := show CommandElabM _ from do
  let inductives <- elems.mapM fun stx => do
    let modifiers <- elabModifiers ⟨stx[0]⟩
    pure (modifiers, stx[1])
  if inductives.any (·.1.isMeta) && inductives.any (!·.1.isMeta) then
    throwError "A mix of `meta` and non-`meta` declarations in the same `mutual` block is not supported"
  let elabs <- runTermElabM fun _ =>
    inductives.mapM fun (modifiers, stx) => mkInductiveView modifiers stx
  let res ← runTermElabM fun vars => do
    elabs.forM fun e => checkValidInductiveModifier e.view.modifiers
    checkNoInductiveNameConflicts elabs
    elabInductiveViews vars elabs
  let views := elabs.map (·.view)
  return (res, views)

@[command_elab typedef_pdescr]
def typedef_elab : CommandElab :=
  fun stx => match stx with
  | `(typedef $_declid $_optdeclsig $[where]? $_ctors* $[$cfields]? $_optderiving) => do
    let unsafe_inductive_stx <- liftMacroM <| genUnsafeInductiveDecl stx
    let wo_macro_scopes := syntax_traversal <∘> syntax_ident <∘> tuple 2 
      |>.over Lean.Name.eraseMacroScopes unsafe_inductive_stx
    let elab_result <- elabMutualInductiveInfo #[wo_macro_scopes]
    let .some inductive_view := elab_result.2[0]? | unreachable -- should be caught by elabMutualInductiveInfo
    let .some typector_typ := inductive_view.type? | throwError "typedef elab did not produce type ctor's type"
    let model_struct_stx := mkModelStructureStx 
      inductive_view.declName 
      inductive_view.binders.getArgs 
      typector_typ 
      (inductive_view.ctors.map fun x => (x.declId, x.type?.someD))
    elabCommand model_struct_stx
  | _ => throwUnsupportedSyntax

-- haven't tested if it works since porting from lua repo

end

