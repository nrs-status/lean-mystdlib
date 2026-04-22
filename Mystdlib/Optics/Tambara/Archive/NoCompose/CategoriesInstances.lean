import Mystdlib.General
import Mystdlib.Optics.Tambara.Archive.NoCompose.Tambara
import Mathlib.Control.Traversable.Basic


open Tambara


abbrev NatTsfm.{u, v} := fun (f g : Type u -> Type v) => ∀α, f α -> g α

abbrev App.{u, v} := fun (f : Type u -> Type v) (α : Type u) => f α

instance appcat : Category (carrier := Type u -> Type v) Applicative NatTsfm where
  id := fun _ => id
  comp := fun f g _ => f _ ∘ g _

instance trvcat : Category (carrier := Type u -> Type u) Traversable NatTsfm where
  id := fun _ => id
  comp := fun f g _ => f _ ∘ g _


instance [Applicative f] : Obj Applicative f where
  is_obj := inferInstance

instance [inst : Obj Applicative f] : Applicative f := inst.is_obj

instance [Traversable f] : Obj Traversable f where
  is_obj := inferInstance

instance [inst : Obj Traversable f] : Traversable f := inst.is_obj

abbrev Trivial.{u} : Type u -> Type u := fun (_ : Type u) => PUnit

instance typecat : Category (carrier := Type u) Trivial (· -> ·) where
  id := id
  comp := fun f g => f ∘ g

instance {α : Type u} : Obj Trivial α where
  is_obj := .unit

instance {f} : Liftable obj obj' Trivial f where
  lift := .unit

def bimap
  [inst : Bifunctor Trivial (· -> ·) Trivial (· -> ·) Trivial (· -> ·) p]
  := @inst.map

instance : Bifunctor Trivial (· -> ·) Trivial (· -> ·) Trivial (· -> ·) Prod where
  map := fun f g h => (f h.1, g h.2)

instance : MonoidalCategory Trivial (· -> ·) Prod where
  tensorUnit := PUnit
  associator := Prod.assoc_inv
  associator_inv := Prod.assoc
  leftUnitor := Prod.snd
  leftUnitor_inv := (.unit, ·)
  rightUnitor := Prod.fst
  rightUnitor_inv := (·, .unit)

instance : Bifunctor Trivial (· -> ·) Trivial (· -> ·) Trivial (· -> ·) Sum where
  map := fun f g =>
    Sum.elim (.inl ∘ f) (.inr ∘ g)

instance : MonoidalCategory Trivial (· -> ·) Sum.{u, u} where
  tensorUnit := PEmpty
  associator := Sum.assoc_inv
  associator_inv := Sum.assoc
  leftUnitor := Sum.elim PEmpty.elim id
  leftUnitor_inv := .inr
  rightUnitor := Sum.elim id PEmpty.elim
  rightUnitor_inv := .inl

instance {o : α -> α -> α} {obj : α -> Type u} {hom : α -> α -> Type u} [Category obj hom] [MonoidalCategory obj hom o]  : MonoidalAction obj hom o obj hom o where
  unitor := MonoidalCategory.leftUnitor
  unitor_inv := MonoidalCategory.leftUnitor_inv
  multiplicator := MonoidalCategory.associator_inv obj
  multiplicator_inv := MonoidalCategory.associator obj

instance : MonoidalAction Trivial (· -> ·) Sum Trivial.{u} (· -> ·) Sum where
  unitor := fun x => x.elim PEmpty.elim id
  unitor_inv := .inr
  multiplicator := Sum.assoc
  multiplicator_inv := Sum.assoc_inv


instance : Liftable Applicative Applicative Applicative (· ∘ ·) where
  lift := fun {_ _ _ _} => inferInstance

instance : Bifunctor Applicative NatTsfm.{u,u} Applicative NatTsfm Applicative NatTsfm (· ∘ ·) where
  map := fun {_ _ _ k _ _ _ _} f g α h => (f (k α)) (fmap (g α) h)

instance : MonoidalCategory Applicative NatTsfm (· ∘ ·) where
  tensorUnit := Id
  associator := fun _ => id
  associator_inv := fun _ => id
  leftUnitor := fun _ => id
  leftUnitor_inv := fun _ => id
  rightUnitor := fun _ => id
  rightUnitor_inv := fun _ => id

instance : Liftable Traversable Traversable Traversable (· ∘ ·) where
  lift := fun {_ _ tva tvb} => ⟨fun f => tva.is_obj.traverse (tvb.is_obj.traverse f)⟩

instance : Bifunctor Traversable NatTsfm.{u,u} Traversable NatTsfm Traversable NatTsfm (· ∘ ·) where
  map := fun {_ _ _ k _ _ _ _} f g α h => (f (k α)) (fmap (g α) h)

instance : MonoidalCategory Traversable NatTsfm (· ∘ ·) where
  tensorUnit := Id
  associator := fun _ => id
  associator_inv := fun _ => id
  leftUnitor := fun _ => id
  leftUnitor_inv := fun _ => id
  rightUnitor := fun _ => id
  rightUnitor_inv := fun _ => id


instance : Bifunctor Applicative NatTsfm Trivial (· -> ·) Trivial (· -> ·) App where
  map := fun {_ _ a _ _ _ _ _} f g => (fmap g ∘ f a)

instance : MonoidalAction Applicative NatTsfm (· ∘ ·) Trivial (· -> ·) App where
  unitor := id
  unitor_inv := id
  multiplicator := id
  multiplicator_inv := id

instance : Bifunctor Traversable NatTsfm Trivial (· -> ·) Trivial (· -> ·) App where
  map := fun {_ _ a _ _ inst _ _} f g => 
    have := inst.is_obj
    fmap g ∘ (f a)

instance : MonoidalAction Traversable NatTsfm (· ∘ ·) Trivial (· -> ·) (· ·) where
  unitor := id
  unitor_inv := id
  multiplicator := id
  multiplicator_inv := id
