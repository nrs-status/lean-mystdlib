import Lean
import Qq

open Qq
open Lean Elab Term Meta

namespace UnificationHelper

structure Data where
  declName : Name
  elaborator : TermElab

initialize Ext : SimplePersistentEnvExtension (Name × TermElab) (NameMap TermElab) <- 
  registerSimplePersistentEnvExtension {
    addEntryFn := fun nm_map (nm, elaborator) => nm_map.insert nm elaborator
    addImportedFn := mkStateFromImportedEntries 
      (fun nm_map (nm, elaborator) => nm_map.insert nm elaborator)
      {}
  }

def addExtEntry {m : Type → Type} [MonadEnv m]
    (declName : Name) (elaborator : TermElab) : m Unit :=
  modifyEnv (Ext.addEntry ·
    (declName, elaborator))

def resolveToUniqueName (nm : Lean.Name) : CoreM Name := do
  let resolution <- resolveGlobalName nm
  if h : 0 == resolution.length 
  then throwError m!"could not resolve name {nm}"
  else 
  if 1 < resolution.length then throwError m!"multiple possible interpretations for {nm}: {resolution}"
  return resolution[0]'(by grind) |>.1

syntax (name := attr_pdescr) "unif_helper " ident : attr

unsafe initialize registerBuiltinAttribute {
  name := `attr_pdescr
  descr := "add an elaborator that can be found with the ¿ syntax"
  add := fun elaborator_decl_nm attr_tag_stx _attrKind => -- @[$attr_tag_stx] def $declnm ...
    match attr_tag_stx with
    | `(attr| unif_helper $term_decl_to_extend_id:ident) => do
      let decl_as_const <- getConstInfo elaborator_decl_nm
      let .defnInfo defnval := decl_as_const | throwError "getConstInfo {elaborator_decl_nm} did not produce a defn"
      let elaborator <- MetaM.run' <| evalExpr TermElab defnval.type defnval.value
      addExtEntry (<- resolveToUniqueName term_decl_to_extend_id.getId) elaborator
    | _ => throwUnsupportedSyntax
}

syntax (name := pdescr) term "¿" optional(ppSpace term,*) : term

@[term_elab pdescr]
def elaborator : TermElab := fun stx t? => do
  let `($(head)¿ $[$ts?,*]?) := stx | throwUnsupportedSyntax
  let stx' := match ts? with
    | .some ts => Syntax.mkApp head ts
    | .none => head
  /- logInfo m!"stx: {stx}" -/
  /- logInfo m!"ident_nm: {repr head}" -/
  /- logInfo m! "head.raw.getId: {head.raw.getId}" -/
  let decl_nm <- resolveToUniqueName head.raw.getId
  /- logInfo m!"decl_nm: {repr decl_nm}" -/
  /- logInfo m!"t?: {t?}" -/
  let elabs := PersistentEnvExtension.getState Ext (<- getEnv)
  /- logInfo m!"-- repr elabs.1--\n{elabs.1.map Prod.fst}" -/
  /- logInfo m!"-- repr elabs.2--\n{elabs.2.keys}" -/
  let .some elaborator := elabs.2.get? decl_nm | throwError m!"id {decl_nm} not in unif helper env ext"
  elaborator stx' t?

end UnificationHelper









