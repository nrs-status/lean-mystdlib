import Mystdlib.Optics.Tambara.Fold
import Mystdlib.Optics.Tambara
import Mystdlib.Metaprogramming.General
import Mystdlib.Optics.Tambara.Traversal

open Lean

open Tamb

open Lean.PrettyPrinter

section Arrow

def Syntax.mkArrow : Syntax -> Syntax -> Syntax :=
  fun head body => MacroM.stx `($(.mk head) -> $(.mk body))

def Syntax.mkArrows : List Syntax -> Syntax
| .nil => .missing
| .cons x .nil => x
| .cons x xs => Syntax.mkArrow x (Syntax.mkArrows xs)

partial def arrow_iso_stx_to : Syntax -> (Syntax × List Syntax)
| `($x -> $y) => match recur y with
  | (head, rest) => (x, head :: rest)
| `(Lean.Parser.Term.depArrow|$x -> $y) => match recur y with
  | (head, rest) => (x, head :: rest)
| x => (x, [])

def arrow_iso_stx_from : (Syntax × List Syntax) -> Syntax
| (head, rest) => Syntax.mkArrows (head :: rest)

def arrow_iso_stx : Iso' (Syntax × List Syntax) Syntax :=
  .mk arrow_iso_stx_to arrow_iso_stx_from

def arrow_last : Lens' Syntax (Syntax × List Syntax) :=
  .mk 
    (fun (head, tail) => if h : tail.isEmpty then head else tail.getLast !p) 
    (fun (head, tail) new => if h : tail.isEmpty then (new, []) else (head, tail.modify tail.length.pred (fun _ => new)))

def arrow_fold : Fold Syntax Syntax :=
  .mk (F := List) (arrow_iso_stx_to · |> uncurry .cons)

def arrow_aff_list : AffineTraversal' Syntax (List Syntax) :=
  .mk 
    (fun | .nil => .inl .nil | x => .inr <| Syntax.mkArrows x)
    (fun l stx => arrow_iso_stx.view.{0, 0} stx |> (fun (head, rest) => l ++ (head :: rest)))

partial def arrow_traversalVL : TraversalVL' Syntax Syntax  :=
  fun _ _ f x => Syntax.mkArrows <$> traverse f (arrow_fold.toListOf x)

partial def arrow_traversal := arrow_traversalVL.toTraversal

end Arrow

section App

def app_prism : Prism' (Syntax × Array Syntax) Syntax :=
  .mk
    (Function.uncurry (fun x y => Lean.Syntax.mkApp (.mk x) (.mk y)))
    fun
    | `($head $body*) => .inr (head, body)
    | x => .inl x

partial def app_traversalVL : TraversalVL' Syntax Syntax :=
  fun F _ f x => match app_prism.matching x with
  | .inl x => pure x
  | .inr (head, args) => 
    (fun c k => Lean.Syntax.mkApp (.mk c) (.mk k)) <$> f head <*> args.traverse (app_traversalVL F f)

end App

section Matchers

def syntax_missing : Prism' Unit Syntax :=
  .mk (fun _ => .missing) (fun | .missing => .inr .unit | x => .inl x)

def syntax_node : Prism' (SourceInfo × SyntaxNodeKind × Array Syntax) Syntax :=
  .mk 
    (fun (srcinf, kind, ar) => .node srcinf kind ar)
    (fun | .node srcinf kind ar => .inr (srcinf, kind, ar) | x => .inl x)

def syntax_atom : Prism' (SourceInfo × String) Syntax :=
  .mk
    (fun (inf, str) => .atom inf str)
    (fun | .atom inf str => .inr (inf, str) | x => .inl x)

def syntax_ident : Prism' (SourceInfo × Substring.Raw × Name × List Syntax.Preresolved) Syntax :=
  .mk
    (fun (inf, substr, nm, l) => .ident inf substr nm l)
    (fun | .ident inf substr nm l => .inr (inf, substr, nm, l) | x => .inl x)

end Matchers

section All

partial def syntax_traversalVL : TraversalVL' Syntax Syntax :=
  fun _ _ f x => match x with
  | .node _ _ rest =>
    (fun head rest' => match head with | .node x y _ => .node x y rest' | x => x) <$> f x <*> rest.traverse (syntax_traversalVL _ f)
  | _ => f x

def syntax_traversal : Traversal'.{0,0} Syntax Syntax := TraversalVL.toTraversal syntax_traversalVL


/-
def xr'' := arrow_iso_stx <∘> arrow_last <∘> app_prism <∘> tuple 0
def ctortype1 := MacroM.stx `(Unit -> Nat -> mytype String)
def ctortype2 := MacroM.stx `(mytype Bool)
def ctortypes := [ctortype1, ctortype2]
def r'' := xr''.set (mkIdent `typate)
def r := r'' ctortype1

#run_elab
  ctortypes.forM (fun s => do dbg_trace <- formatTerm <| r'' s)
-/
end All


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




