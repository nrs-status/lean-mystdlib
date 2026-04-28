import Mathlib.Control.Traversable.Basic
import Mathlib.Control.Functor

instance
  [Functor G]
  [Functor F]
  : Functor (G ∘ F) := (inferInstance : Functor (Functor.Comp G F))

instance
  [Traversable G]
  [Traversable F]
  : Traversable (G ∘ F) where
    traverse := fun f x => (Traversable.traverse (Traversable.traverse f)) x


instance : Functor (Prod α) where
  map := fun f x => (x.fst, f x.snd)

instance : Traversable (Prod.{u,u} α) where
  traverse :=
    fun f x => Functor.map (x.fst, ·) (f x.snd)

instance : Functor (Vector · n) where
  map := fun f ⟨l, h⟩ => ⟨Array.map f l, by grind⟩

def Array.traverse
  [Applicative t]
  (f : α -> t β)
  (xs : Array α)
  : t (Array β)
  := if h : xs.isEmpty
  then pure #[]
  else
    let := Array.traverse f xs.pop
    (fun a ar => ar.push a) <$> f (xs.back (by grind)) <*> this
termination_by xs.size
decreasing_by simp_all; grind

instance : Traversable Array where
  traverse := Array.traverse

def Vector.traverse 
  [Applicative t]
  (f : α -> t β)
  (xs : Vector α n)
  : t (Vector β n) :=
  match xs with
  | ⟨ar, h⟩ => match n with
    | .zero => pure ⟨#[], by grind⟩
    | .succ nn =>
      let : t (Vector β nn) := Vector.traverse f ⟨ar.pop, by grind⟩
      (fun a ⟨ar', h'⟩ => ⟨ar'.push a, by grind⟩) <$> f ar.back <*> this

instance : Traversable (Vector · n) where
  traverse := Vector.traverse



