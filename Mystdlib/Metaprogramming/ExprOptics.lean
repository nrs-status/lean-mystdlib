import Mystdlib.Optics.Tambara.Combinators
import Mystdlib.Optics.Tambara.Traversal
import Mystdlib.Optics.Tambara.Plated
import Mystdlib.Optics.PathedCollect

import Mystdlib.Metaprogramming.Misc

open Lean PrettyPrinter

open Tamb

partial def expr_traversalVL : TraversalVL' Expr Expr :=
  fun _ _ f x => match x with
  | .bvar deBruijnIndex => f x
  | .fvar fvarId => f x
  | .mvar mvarId => f x
  | .sort u => f x
  | .const declName us => f x
  | .app fn arg =>
    (fun fx ffn farg => match fx with | .app _ _ => .app ffn farg | x => x) <$> f x <*> expr_traversalVL _ f fn <*> expr_traversalVL _ f arg
  | .lam binderName binderType body binderInfo =>
    (fun fx fbt fbody => match fx with | .lam bname _ _ binfo => .lam bname fbt fbody binfo | x => x) <$> f x <*> expr_traversalVL _ f binderType <*> expr_traversalVL _ f body
  | .forallE binderName binderType body binderInfo =>
    (fun fx fbt fbody => match fx with | .forallE bname _ _ binfo => .forallE bname fbt fbody binfo | x => x) <$> f x <*> expr_traversalVL _ f binderType <*> expr_traversalVL _ f body
  | .letE declName type value body nondep =>
    (fun fx ftype fval fbody => match fx with | .letE declname _ _ _ nondep => .letE declname ftype fval fbody nondep | x => x) <$> f x <*> expr_traversalVL _ f type <*> expr_traversalVL _ f value <*> expr_traversalVL _ f body
  | .lit _ => f x
  | .mdata data expr =>
    (fun fx fexpr => match fx with | .mdata data _ => .mdata data fexpr | x => x) <$> f x <*> expr_traversalVL _ f expr
  | .proj typeName idx struct =>
    (fun fx fstruct => match fx with | .proj tn idx _ => .proj tn idx fstruct | x => x) <$> f x <*> expr_traversalVL _ f struct

def expr_traversal : Traversal' Expr Expr :=
  TraversalVL.toTraversal expr_traversalVL

open PathedCollect in
def pathedCollectStep (p : Expr -> Bool) (e : Expr) : StateM (PathedCollect.State Expr) Unit :=
  modify fun σ =>
    let aux  : State Expr -> State Expr := match e with
      | .mdata .. | .proj .. => pushObligation 1
      | .app .. | .lam .. | .forallE .. => pushObligation 2
      | .letE .. => pushObligation 3
      | _ => decreaseObligation
    { aux σ with collected := ite (p e) (List.cons (σ.currentPath, e)) id σ.collected }

def _root_.pathedCollect (p : Expr -> Bool) (e : Expr) : List (Array Nat × Expr) :=
  let aux := expr_traversalVL 
    (StateM (PathedCollect.State Expr)) 
    (fun e => do pathedCollectStep p e; return e) 
    e
  (aux ⟨#[0], #[], []⟩).2.collected

section Arrow



end Arrow
