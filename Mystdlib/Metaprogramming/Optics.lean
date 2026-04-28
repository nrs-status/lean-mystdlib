import Mystdlib.Optics.Tambara.Fold
import Mystdlib.Optics.Tambara
import Mystdlib.Metaprogramming.General
import Mystdlib.Optics.Tambara.Traversal

open Lean

open Tamb

section Arrow

def Syntax.mkArrow : Syntax -> Syntax -> Syntax :=
  fun head body => MacroM.stx `($(.mk head) -> $(.mk body))

def Syntax.mkArrows : List Syntax -> Syntax
| .nil => .missing
| .cons x .nil => x
| .cons x xs => Syntax.mkArrow x (Syntax.mkArrows xs)

partial def arrow_prism_match : Syntax -> Syntax ⊕ (Syntax × Syntax × List Syntax)
| `($x -> $y) => match arrow_prism_match y with
  | .inl _ => .inr (x, y, [])
  | .inr (y', y'', l) => .inr (x, y', y'' :: l)
| `(Lean.Parser.Term.depArrow|$x -> $y) => match arrow_prism_match y with
  | .inl _ => .inr (x, y, [])
  | .inr (y', y'', l) => .inr (x, y', y'' :: l)
| x => .inl x

def arrow_prism : Prism' (Syntax × Syntax × List Syntax) Syntax :=
  .mk
    (fun (x, y, xs) => Syntax.mkArrows (x :: y :: xs))
    arrow_prism_match

def two_elm_arrow_iso : Iso' (Syntax × Syntax) (Syntax × Syntax × List Syntax) :=
  .mk 
    (fun (fst, snd, rest) => (fst, Syntax.mkArrows (snd :: rest)))
    (fun (head, rest) => match matching arrow_prism rest with
      | .inl x => (head, x, [])
      | .inr (y, y', rest') => (head, y, (y' :: rest')))

def two_elm_arrow := arrow_prism.compose two_elm_arrow_iso

def arrow_append := Function.curry (review two_elm_arrow)

def arrow_fold : Fold Syntax Syntax :=
  .mk (arrow_prism.elim (fun _ => .nil) (fun (fst, snd, rest) => fst :: snd :: rest))

partial def arrow_traversalVL : TraversalVL' Syntax Syntax  :=
  fun _ _ f x => Syntax.mkArrows <$> traverse f (toListOf arrow_fold x)

partial def arrow_traversal := arrow_traversalVL.toTraversal

end Arrow

section App

def app_prism : Prism' (Syntax × Array Syntax) Syntax :=
  .mk
    (Function.uncurry (fun x y => Lean.Syntax.mkApp (.mk x) (.mk y)))
    fun
    | `($head $body*) => .inr (head, body)
    | x => .inl x

partial def app_traverseVL : TraversalVL' Syntax Syntax :=
  fun F _ f x => match matching app_prism x with
  | .inl x => pure x
  | .inr (head, args) => 
    (fun c k => Lean.Syntax.mkApp (.mk c) (.mk k)) <$> f head <*> args.traverse (app_traverseVL F f)

end App


inductive bracketedBinderKind | explicit | implicit | strict_implicit | instance_implicit
def bracketedBinder : Prism' (bracketedBinderKind × Array Syntax × Syntax) Syntax :=
  .mk 
    (fun (kind, lhs, rhs) =>  
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




