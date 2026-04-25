import Mystdlib.Optics.Tambara
import Mystdlib.Metaprogramming.General

open Lean
open Tamb


def Syntax.mkArrow : Syntax -> Syntax -> Syntax :=
  fun head body =>
  MacroM.run `($(.mk head) -> $(.mk body)) |>.elim .missing TSyntax.raw

def arrow_prism_match : Syntax -> Syntax ⊕ Syntax × Syntax
| `($x -> $y) => .inr (x, y)
| `(Lean.Parser.Term.depArrow| $x -> $y) => .inr (x, y)
| x => .inl x

def arrow_prism : Prism' (Syntax × Syntax) Syntax :=
  .mk 
    (Function.uncurry Syntax.mkArrow)
    arrow_prism_match

partial def arrow_traverseVL : TraversalVL' Syntax Syntax  :=
  fun F _ f x => match matching arrow_prism x with
  | .inl x => f x
  | .inr (head, body) => 
    Syntax.mkArrow <$> f head <*> arrow_traverseVL F f body

partial def arrow_traverse := arrow_traverseVL.toTraversal
  
def arrow_snoc := Function.curry (review arrow_prism)

/- def mything := arrow_traverseVL Id _ _ -/

partial def arrow_cons_match (accum : List Syntax) : Syntax -> Syntax ⊕ Syntax × Syntax 
| `($x -> $y) => match matching arrow_prism y with
  | .inl y' => .inr (x, y)
  | .inr y' => arrow_cons_match (x :: accum) y
| `(Lean.Parser.Term.depArrow|$x -> $y) => match matching arrow_prism y with
  | .inl y' => .inr (x, y)
  | .inr y' => arrow_cons_match (x :: accum) y
| x => .inl x

--def arrow_cons_build (parts : Syntax ×

#run_elab
  let myarrow <- `(Nat -> Unit -> Nat)
  let mytype <- `(List String)
  dbg_trace <- Lean.PrettyPrinter.formatTerm (arrow_snoc myarrow mytype)

def app_prism : Prism' (Syntax × Array Syntax) Syntax :=
  .mk
    (Function.uncurry (fun x y => Lean.Syntax.mkApp (.mk x) (.mk y)))
    fun
    | `($head $body*) => .inr (head, body)
    | x => .inl x

partial def app_traverseVL : TraversalVL' Syntax Syntax :=
  fun F _ f x => match matching app_prism x with
  | .inl x => f x
  | .inr (head, args) => 
    (fun c k => Lean.Syntax.mkApp (.mk c) (.mk k)) <$> f head <*> args.traverse (app_traverseVL F f)


inductive bracketedBinderKind | explicit | implicit | strict_implicit | instance_implicit
def bracketedBinder : Prism' (bracketedBinderKind × Array Syntax × Syntax) Syntax :=
  .mk 
    (fun (kind, lhs, rhs) => --MacroM.stx `(bracketedBinder| ($(.mk lhs) : $(.mk rhs)))) 
      MacroM.stx <| match kind with
      | .explicit => `(bracketedBinder|($(.mk lhs)* : $(.mk rhs)))
      | .implicit => `(bracketedBinder|{$(.mk lhs)* : $(.mk rhs)})
      | .strict_implicit => `(bracketedBinder|{{$(.mk lhs)* : $(.mk rhs)}})
      | .instance_implicit => if h : lhs.isEmpty
        then `(bracketedBinder|[$(.mk rhs)])
        else `(bracketedBinder|[$(.mk (lhs[0]'!p)) : $(.mk rhs)])
      )
    <| fun
    | `(bracketedBinder|($lhs* : $rhs)) => .inr (.explicit, lhs, rhs)
    | `(bracketedBinder|{$lhs* : $rhs}) => .inr (.implicit, lhs, rhs)
    | `(bracketedBinder|{{$lhs* : $rhs}}) => .inr (.strict_implicit, lhs, rhs)
    | `(bracketedBinder|[$lhs : $rhs]) => .inr (.instance_implicit, #[lhs], rhs)
    | `(bracketedBinder|[$x]) => .inr (.instance_implicit, #[], x)
    | x => .inl x
