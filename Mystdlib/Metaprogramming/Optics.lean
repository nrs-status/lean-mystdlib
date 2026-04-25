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

/- def app_traverseVL : TraversalVL' Syntax Syntax := -/
/-   fun F _ f x => match matching app_prism x with -/
/-   | .inl x => f x -/
/-   | .inr x => (fun c k => Lean.Syntax.mkApp (.mk c) (.mk k)) <$> _ <*> app_traverseVL F f _ -/


