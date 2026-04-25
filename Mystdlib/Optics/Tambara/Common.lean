import Mystdlib.Optics.Tambara.Traversal
import Mathlib.Data.Tree.Basic
import Mystdlib.Optics.Tambara.Tambara
import Mystdlib.Optics.Tambara.Combinators

namespace Tamb

instance {ς τ γ : Type u} : Profunctor (fun α β => (ς -> α) -> (ς -> β -> τ) -> γ) where
  map := fun f g h p q => h (f ∘ p) ((fun k => k ∘ g) ∘ q)

instance  {ς τ γ : Type u} : Tamb ⟨Prod, Prod⟩ (fun (α β : Type u) => (ς -> α) -> (ς -> β -> τ) -> γ) where
  tamb := fun f x =>
    fun g => f (Prod.snd ∘ x) (fun s b => g s (x s |>.fst, b))

def withLens 
  (x : Lens α β ς τ)
  (f : (ς -> α) -> (ς -> β -> τ) -> γ)
  : γ
  := x (fun α β => (ς -> α) -> (ς -> β -> τ) -> γ) f id (fun _ => id)

/- def passthrough -/
/-   (x : Lens α β ς τ) -/
/-   (f : α -> β) -/
/-   : ς -> β × τ -/
/-   :=  -/
/-     have := x (· -> ·) f -/
/-     have thisa := view x -/
/-     _ -/

def fst {α β : Type u} : Lens' α (α × β) :=
  .mk Prod.fst (fun (_, r) a => (a, r))

def snd {α β : Type u} : Lens' β (α × β) :=
  .mk Prod.snd (fun (l, _) b => (l, b))

--def parallel : Lens α β ς τ -> Lens α' β' ς' τ' -> 

def left : Prism' α (α ⊕ β) :=
  .mk .inl (Sum.elim .inr (fun b => .inl (.inr b)))

def right : Prism' β (α ⊕ β) := 
  .mk .inr (Sum.elim (fun a => .inl (.inl a)) .inr)

def some : Prism α β (Option α) (Option β) :=
  .mk .some (Option.elim · (.inl .none) .inr)

def some' : Prism' α (Option α) :=
  .mk .some (Option.elim · (.inl .none) .inr)

def none : Prism' Unit (Option α) :=
  .mk (fun _ => .none) .inl



def Tree.extractInOrder : Tree α -> List α × (List α -> Tree α)
| .nil => ([], fun _ => .nil)
| .node x l r =>
  have lr := extractInOrder l
  have rr := extractInOrder r
  (x :: lr.fst ++ rr.fst, fun | .nil => .nil | .cons a as => .node a (lr.snd (as.take lr.fst.length)) (rr.snd (as.drop lr.fst.length)))

def Tree.inOrderTraversal {α}: Traversal' α (Tree α) :=
  Traversal.mk Tree.extractInOrder


