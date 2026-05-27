import Mathlib.Logic.Function.Defs
import Mathlib.Control.Bifunctor
import Lean

--

notation f " ∘₂ " g => Function.bicompr f g

export Function (curry uncurry)

export Bifunctor (bimap)

-- to do e.g. |>.foldl.flip
def Function.flip {α : Sort u} {β : Sort v} {φ : Sort w} (f : α → β → φ) :
β → α → φ := _root_.flip f

abbrev fmap [Functor F] (f : α -> β) (xfα : F α) : F β := Functor.map f xfα

--

def amp (x : α) (f : α -> β) : β := f x

infixl:10 "&" => amp


--

syntax (name := recur_pdescr) "recur" : term

open Lean Elab Term in
@[term_elab recur_pdescr]
def recur_stx_elab : TermElab := fun _ et => do
  let .some decl_nm <- getDeclName? | throwError "could not get decl name"
  let e <- elabTerm (mkIdent decl_nm) et
  return e

--

-- typehole that reduces the type
syntax (name := holeModReduction_pdescr) "_r" : term

open Lean Elab Term in
@[term_elab holeModReduction_pdescr]
def holeModReductionElab : TermElab := fun _ expectedType? => do
  let .some expectedType := expectedType? | throwError "no expected type"
  let reducedExpectedType <- Lean.Meta.reduce expectedType true false true
  let w_pp <- Lean.PrettyPrinter.ppExpr reducedExpectedType
  logInfo w_pp
  let hole <- elabTerm (<- `(_)) expectedType
  .pure hole


--

syntax (name := elab_w_pdescr) "elab_w " term : term

open Lean Elab Term Meta in
@[term_elab elab_w_pdescr]
def elab_w_elab : TermElab := fun stx et? => 
  match stx with
  | `(elab_w $x) => do
    let `(fun $_ => $_) := x | throwUnsupportedSyntax
    let val : Expr := Lean.mkForall `stx .default 
      (<- mkAppM ``Option #[mkConst ``Expr])
      (<- mkAppM ``TermElabM #[mkConst ``Expr])
    let tac <- unsafe evalTerm (Option Expr -> TermElabM Expr) val x
    tac et?
  | _ => throwUnsupportedSyntax

--

macro "#run_elab " x:doSeq : command => `(#eval show Lean.Elab.TermElabM Unit from do $x)


--

syntax:max (name := mod_subtype_pdescr) term "<:" : term
macro_rules
| `($(x)<:) => `(⟨$x, (by repeat first | rfl | native_decide | simp | simp_all | grind)⟩)

syntax:max (name := bang_p_pdescr) "!p" : term
macro_rules
| `(!p) => `(by repeat first | rfl | native_decide | simp | simp_all | grind)

--

elab "#grab" c:command : command => Lean.logInfo (toString c)

elab "#grab_expand" c:command : command => do
  let x <- Lean.Elab.liftMacroM (Lean.expandMacros c)
  Lean.logInfo x

--

syntax (name := mod_match_pdescr) term " %fun| " term " => " term : term
macro_rules 
| `($x %fun| $y => $z) => `(fun | $y => $z | v => $x v)


--

syntax:max (name := simp_exact_pdescr) term ";s!" : term
macro_rules
| `($x;s!) => `(by simp; exact $x)
