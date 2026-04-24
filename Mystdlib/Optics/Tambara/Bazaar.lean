import Mystdlib.Traversable
import Mystdlib.Optics.Tambara.Tambara
import Mystdlib.Optics.Tambara.CategoriesInstances
import Mystdlib.Optics.Tambara.Optics

/- ofMniip -/

structure Bazaar (α β τ : Type u) : Type u where
  length : Nat
  elements : Vector α length
  continuation : Vector β length → τ

def Vector.unappend n m (v : Vector α (n + m)) : Vector α n × Vector α m
  :=
    ( Vector.cast (@Nat.min_add_right_self n m) (v.take n)
    , Vector.cast (@Nat.add_sub_cancel_left n m) (v.drop n)
    )

instance : Applicative (Bazaar α β) where
  pure x := ⟨0, #v[], λ_ => x⟩
  seq | ⟨n, xs, k⟩, f => match f () with
    | ⟨m, ys, c⟩ =>
      ⟨ n + m
      , xs ++ ys
      , fun v => match v.unappend n m with | (as, bs) => k as (c bs)
      ⟩

def Bazaar.sell (x : α) : Bazaar α β β :=
  { length := 1
  , elements := #v[x]
  , continuation := Vector.head
  }

/- end ofMniip -/

def Baz (τ β α) := Bazaar α β τ

instance : Functor (Baz τ β) where
  map := fun f g => {
    length := g.length
    elements := g.elements.map f
    continuation := g.continuation
    }

instance : Traversable (Baz τ β) where
  traverse := fun f ⟨length, elements, continuation⟩ =>
    have := Traversable.traverse (t := (Vector · length)) f elements
    Functor.map (fun x => ⟨length, x, continuation⟩) this

def Baz.sold
  (x : Baz τ α α)
  : τ
  := match x with
  | ⟨_, elements, continuation⟩ => continuation elements

def TraversalVL (α β ς τ) := (F : _) -> [Applicative F] -> (α -> F β) -> ς -> F τ

def TraversalVL' (α ς) := TraversalVL α α ς ς

namespace Tamb 

def TraversalVL.toTraversal
  (x : TraversalVL α β ς τ)
  : Traversal α β ς τ
  := Traversal.mk' (x (Bazaar α β) Bazaar.sell) Baz.sold







