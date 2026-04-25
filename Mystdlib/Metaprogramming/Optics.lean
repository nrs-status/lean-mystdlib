import Mystdlib.Optics.Tambara
import Mystdlib.Metaprogramming.General

open Lean
open Tamb

def Syntax.mkArrow : Syntax -> Syntax -> Syntax :=
  fun head body =>
  MacroM.run `($(.mk head) -> $(.mk body)) |>.elim .missing TSyntax.raw

def arrow_prism_aux : Syntax -> Syntax ⊕ Syntax × Syntax
| `($x -> $y) => .inr (x, y)
| `(Lean.Parser.Term.depArrow| $x -> $y) => .inr (x, y)
| x => .inl x

def arrow_prism : Prism' (Syntax × Syntax) Syntax :=
  .mk 
    (Function.uncurry Syntax.mkArrow)
    arrow_prism_aux

partial def arrow_traverseVL : TraversalVL' Syntax Syntax  :=
  fun F _ f x => match matching arrow_prism x with
  | .inl x => f x
  | .inr (head, body) => 
    Syntax.mkArrow <$> f head <*> arrow_traverseVL F f body

partial def arrow_traverse := arrow_traverseVL.toTraversal
  
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


/-
inductive BracketedBinder
| explicit
  (lhs : TSyntaxArray [`ident, `Lean.Parser.Term.hole])
  (h : ¬ lhs.isEmpty)
  (rhs : Term)
| implicit
  (lhs : TSyntaxArray [`ident, `Lean.Parser.Term.hole])
  (h : ¬ lhs.isEmpty)
  (rhs : Term)
| strict_implicit
  (lhs : TSyntaxArray [`ident, `Lean.Parser.Term.hole])
  (h : ¬ lhs.isEmpty)
  (rhs : Term)
| instance_implicit
  (lhs : Option Ident)
  (rhs : Term)
deriving Repr

def Lean.Syntax.toBracketedBinder : Syntax -> Option BracketedBinder
| `(bracketedBinder|($lhs* : $rhs)) =>
  if h : lhs.isEmpty
  then .none
  else .some <| .explicit lhs (by grind) rhs
| `(bracketedBinder|{$lhs* : $rhs}) =>
  if h : lhs.isEmpty
  then .none
  else .some <| .implicit lhs (by grind) rhs
| `(bracketedBinder|{{$lhs* : $rhs}}) =>
  if h : lhs.isEmpty
  then .none
  else .some <| .strict_implicit lhs (by grind) rhs
| `(bracketedBinder|[$lhs : $rhs]) => .some <| .instance_implicit lhs rhs
| `(bracketedBinder|[$x]) => .some <| .instance_implicit .none x
| _ => .none

def BracketedBinder.toStx : BracketedBinder -> MacroM Syntax
| .explicit lhs _ rhs => `(bracketedBinder|($lhs* : $rhs))
| .implicit lhs _ rhs => `(bracketedBinder|{$lhs* : $rhs})
| .strict_implicit lhs _ rhs => `(bracketedBinder|{{$lhs* : $rhs}})
| .instance_implicit lhs rhs => match lhs with
  | .some lhs' => `(bracketedBinder| [$lhs' : $rhs])
  | .none => `(bracketedBinder| [$rhs])
-/

def bracketedBinder : Prism' (Syntax × Syntax) Syntax :=
  .mk _ _

