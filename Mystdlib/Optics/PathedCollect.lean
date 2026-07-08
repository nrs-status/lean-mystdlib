
namespace PathedCollect

structure State (α : Type u) where
  currentPath : Array Nat
  sameDepthObligations : Array Nat
  collected : List (Array Nat × α)


def pushObligation (obligations : Nat) (σ : State α) : State α :=
  { σ with
    currentPath := σ.currentPath.push 0
    sameDepthObligations := σ.sameDepthObligations.push obligations
  }

partial def decreaseObligation (σ : State α) : State α :=
  if h : σ.sameDepthObligations.isEmpty
  then σ
  else
    if σ.sameDepthObligations[σ.sameDepthObligations.size.pred]'(by simp_all; grind) = 1
    then decreaseObligation { σ with
      sameDepthObligations := σ.sameDepthObligations.pop
      currentPath := σ.currentPath.pop |>.modify σ.currentPath.pop.size.pred Nat.succ
    }
    else { σ with
      sameDepthObligations := σ.sameDepthObligations.modify σ.sameDepthObligations.size.pred Nat.pred
      currentPath := σ.currentPath.modify σ.currentPath.size.pred Nat.succ
    }

-- this can be made generic by using Tambara.Plated but I need to fix Traversal.ofTraverseVL because it currently does not preserve the sequencing of the VL traversal it is given as an argument

/- example implementation for Expr

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


-/

end PathedCollect
