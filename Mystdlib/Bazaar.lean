import Mystdlib.Traversable

/-
from Profunctor Optics : Modular Data Accessors

We say ς is traversable if the type ∀F, [Applicative F] -> (α -> f β) -> ς -> f τ is inhabited, where α is understood to be a focus of ς, and τ the result of reconstructing ς following the tranformation specifies by (α -> f β)

the Bazaar datatype is used to show that
[Inhabited (∀F, [Applicative F] -> (α -> f β) -> ς -> f τ is)]
<->
ς is isomorphic to FunList α β τ (which is itself isomorphic to Bazaar α β τ)


ς -> FunList α β τ is shown passing (FunList α β) as the applicative functor for (traversableWitness : (∀F, [Applicative F] -> (α -> f β) -> ς -> f τ is))
-/




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

def Bazaar.sale {α} β [Traversable t] : t α → Bazaar α β (t β) := traverse sell

/- end ofMniip -/

instance : Functor (Bazaar · β τ) where
  map := fun f g => {
    length := g.length
    elements := g.elements.map f
    continuation := g.continuation
    }

instance : Traversable (Bazaar · β τ) where
  traverse := fun f ⟨length, elements, continuation⟩ =>
    have := Traversable.traverse (t := (Vector · length)) f elements
    Functor.map (fun x => ⟨length, x, continuation⟩) this

def Bazaar.sold
  (x : Bazaar α α τ)
  : τ
  := match x with
  | ⟨_, elements, continuation⟩ => continuation elements

def Bazaar.ofArray (ar : Array α) : Bazaar α α (Array α) :=
  .mk ar.size ⟨ar, rfl⟩ Vector.toArray


