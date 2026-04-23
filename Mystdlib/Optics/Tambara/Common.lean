import Mystdlib.FunList
import Mystdlib.Optics.Tambara.Traversal
import Mathlib.Data.Tree.Basic
import Mystdlib.Optics.Tambara.Tambara
import Mystdlib.Optics.Tambara.Combinators

namespace Tamb

def fst {α β : Type} : Lens' α (α × β) :=
  .mk Prod.fst (fun (_, r) a => (a, r))

def snd {α β : Type} : Lens' β (α × β) :=
  .mk Prod.snd (fun (l, _) b => (l, b))

def Tree.extractInOrder : Tree α -> List α × (List α -> Tree α)
| .nil => ([], fun _ => .nil)
| .node x l r =>
  have lr := extractInOrder l
  have rr := extractInOrder r
  (x :: lr.fst ++ rr.fst, fun | .nil => .nil | .cons a as => .node a (lr.snd (as.take lr.fst.length)) (rr.snd (as.drop lr.fst.length)))

def Tree.inOrderTraversal {α}: Traversal' α (Tree α) :=
  Traversal.mk Tree.extractInOrder


