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

partial def app_traversalVL : TraversalVL' Syntax Syntax :=
  fun F _ f x => match matching app_prism x with
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
#run_elab
  let mystx <- `(Nat.succ 5 (Nat.succ 7 7))
  let newthing := syntax_traversal.compose syntax_ident
  let thingate := over (syntax_traversal.compose syntax_ident) (over (tuple 2) Lean.Name.eraseMacroScopes)
  dbg_trace <- formatTerm <| thingate mystx
  let thingate' := syntax_traversal <∘> syntax_ident %~ tuple 2 %~ Lean.Name.eraseMacroScopes
  dbg_trace <- formatTerm <| thingate' mystx
  dbg_trace <- formatTerm <| syntax_traversal <∘> syntax_ident %~ tuple 2 %~ Lean.Name.eraseMacroScopes <| mystx
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




