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

-- make change, and separate changed part. return changed part and entire structure
def showing
  (x : Lens α β ς τ)
  (f : α -> β)
  : ς -> β × τ
  := fun s => (f <| x.view s, x.over f s)

-- like showing, but return old part
def tracking
  (x : Lens α β ς τ)
  (f : α -> β)
  : ς -> α × τ
  := fun s => (x.view s, x.over f s)


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

def is (p : α -> Bool) : Prism' α α :=
  .mk id (fun a => if p a then .inr a else .inl a)

def Tree.extractInOrder : Tree α -> List α × (List α -> Tree α)
| .nil => ([], fun _ => .nil)
| .node x l r =>
  have lr := extractInOrder l
  have rr := extractInOrder r
  (x :: lr.fst ++ rr.fst, fun | .nil => .nil | .cons a as => .node a (lr.snd (as.take lr.fst.length)) (rr.snd (as.drop lr.fst.length)))

def Tree.inOrderTraversal {α}: Traversal' α (Tree α) :=
  Traversal.mk Tree.extractInOrder

/-
def mything : List α -> Tree α
| .nil => .nil
| .cons x xs => .node x .nil (mything xs)


def neothing : List α -> Tree α :=
  Traversable.foldl (fun t a => .node a .nil t) .nil

def neothing' : List α -> Tree α :=
  Traversable.foldr (fun a t => .node a .nil t) .nil
#eval neothing [1, 2, 3, 4]
#eval neothing' [1, 2, 3, 4]
#eval mything [1, 2, 3, 4]
-/
