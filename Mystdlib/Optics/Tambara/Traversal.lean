import Mystdlib.Optics.Tambara.Tambara
import Mystdlib.Optics.Tambara.Optics
import Mystdlib.Optics.Tambara.Combinators
import Mathlib.Control.Traversable.Basic
import Mystdlib.Optics.Tambara.Cons
import Mystdlib.Optics.Tambara.Bazaar

namespace Tamb

instance [Applicative F] : Profunctor (· -> F ·) where
  map := fun f g h => (Functor.map g ∘ h) ∘ f

instance {m : Type u -> Type u} [Applicative m] : Tamb ⟨App Traversable, App Traversable⟩ (· -> (ULift.{w, u} ∘ m) ·) where
  tamb := fun {α β xμ} f x => 
    have := xμ.snd.traverse (m := m) (α := α) (β := β)
    have := this (ULift.down ∘ f)
    .up (this x)

instance {F : _} [Applicative F] : Tamb ⟨App Traversable, App Traversable⟩ (· -> F ·) where
  tamb :=  fun {_ _ xμ} => xμ.snd.traverse

def Traversal.traverseOf
  {α β ς τ : Type v}
  (x : Traversal α β ς τ)
  : {F : Type v -> Type v} -> [Applicative F] -> (α -> F β) -> ς -> F τ 
  := fun {F _} => x (· -> F ·)

def Traversal.traverseOf' -- universe polymorphic version, needed when using ExOptic.toProfOptic
  {α β ς τ : Type u}
  (x : Traversal.{u, max w u} α β ς τ)
  : {F : Type u -> Type u} -> [Applicative F] -> (α -> F β) -> ς -> F τ 
  := fun {F _} f s =>
    have := x (· -> (ULift.{w, u} ∘ F) ·)
    have := this (ULift.up ∘ f) s
    ULift.down this


def traverseOfExtract -- for educational purposes; unpacking definitions
  [Applicative F]
  {α β ς τ : Type _}
  (extract : ς -> List α × (List β -> τ))
  : (α -> F β) -> ς -> F τ
  :=
    have f : (Split ς α -> F (Split ς β)) -> ς -> F τ := 
      Profunctor.map 
        (p := (· -> F ·)) 
        (fun s => ((extract s).fst, s))
        (fun (l, s) => (extract s).snd l)  
    have g := fun f (l, s) => Functor.map (·, s) (traverse f l)
    f ∘ g

def traverseOfExtract' -- for educational purposes
  [Applicative F]
  {α β ς τ : Type _}
  (extract : ς -> List α × (List β -> τ))
  : (α -> F β) -> ς -> F τ
  := fun f s =>
    have y₁ : Split ς α := (fun s => ((extract s).fst, s)) s
    have y₂ := Functor.map (·, y₁.snd) (traverse f y₁.fst)
    Functor.map (fun (l, s) => (extract s).snd l) y₂

def toListOf
  {α β ς τ : Type u}
  (x : Traversal α β ς τ)
  : ς -> List α
  := 
    let r := ProfOptic.toExOptic ⟨App Traversable, App Traversable⟩ NatTsfm traversableComp x
(fun ⟨fst, snd⟩ => have := fst.snd; Traversable.toList (t := fst.fst) snd) ∘ r.left
  
def partsOf
  {α ς τ : Type u}
  (x : Traversal α α ς τ)
  : Lens (List α) (List α) ς τ
  := 
    let update : α -> StateT (List α) Id α :=
      fun a => get >>= fun
        | .nil => pure a
        | .cons x xs => set xs >>= fun _ => pure x
    Lens.ofVL <| fun _ _ f s => 
      have := Traversal.traverseOf'.{u, u + 1} x update s
      have := (Prod.fst ∘ Id.run) ∘ this.run
      Functor.map this (f (toListOf x s))
      
def traversed
  [Traversable F]
  : Traversal α β (F α) (F β)
  :=
  Traversal.mk' (F := F) id id

def traversed'
  [Traversable F]
  : Traversal' α (F α)
  := traversed

def final
  (x : Traversal' α ς)
  := 
  have := partsOf x
  have thisa := last (α := α) (ς := List α)
  this.compose thisa


