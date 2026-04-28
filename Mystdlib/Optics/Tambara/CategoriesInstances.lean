import Mystdlib.General
import Mystdlib.Optics.Tambara.Categories
import Mathlib.Control.Fold

namespace Tamb

-- Prod and Sum

instance : Bifunctor (· -> ·) (· -> ·) (· -> ·) Prod where
  map := fun f g (l, r) => (f l, g r)

instance : Bifunctor (· -> ·) (· -> ·) (· -> ·) Sum where
  map := fun f g xsum => match xsum with
  | .inl x => .inl (f x)
  | .inr x => .inr (g x)

instance : MonoidalCat (Type _) (· -> ·) Prod where
  tensorUnit := Unit
  associator := ⟨fun ((x, y), z) => (x, y, z), fun (x, y, z) => ((x, y), z)⟩
  leftUnitor := ⟨Prod.snd, fun x => (.unit, x)⟩
  rightUnitor := ⟨Prod.fst, fun x => (x, .unit)⟩


instance : MonoidalCat (Type _) (· -> ·) Sum where
  tensorUnit := Empty
  associator := { 
    hom := fun
    | .inl x => match x with
      | .inl x' => .inl x'
      | .inr x' => .inr (.inl x')
    | .inr x => .inr (.inr x)
    inv := fun
    | .inl x => .inl (.inl x)
    | .inr (.inl x) => .inl (.inr x)
    | .inr (.inr x) => .inr x
    }
  leftUnitor := {
    hom := fun
    | .inl x => x.rec
    | .inr x => x
    inv := fun x => .inr x
  }
  rightUnitor := {
    hom := fun
    | .inl x => x
    | .inr x => x.rec
    inv := fun x => .inl x
  }

instance [inst : MonoidalCat (Type _) (· -> ·) O] [Bifunctor (· -> ·) (· -> ·) (· -> ·) O] : MonoidalAction (· -> ·) O O where
  unitor := {
    hom := inst.leftUnitor.hom
    inv := inst.leftUnitor.inv
  }
  multiplicator := {
    hom := inst.associator.inv
    inv := inst.associator.hom
  }

-- Traversable

abbrev NatTsfm.{u, v} {C : (Type u -> Type u) -> Type v} := fun (σ σ' : ΣF, C F) => ∀α, σ.fst α -> σ'.fst α

abbrev traversableComp (G F : ΣF, Traversable F) : ΣF, Traversable F :=
  have _ := F.2
  have _ := G.2
  ⟨G.1 ∘ F.1, { 
    traverse := fun f x => (G.2.traverse (F.2.traverse f)) x
    }⟩

instance : Category (ΣF, Traversable F) NatTsfm where
  id := fun _ => id
  comp := fun f g α => Function.comp (f α) (g α)

instance : MonoidalCat (ΣF, Traversable F) NatTsfm traversableComp where
  tensorUnit := ⟨Id, inferInstance⟩
  associator := ⟨fun _ => id, fun _ => id⟩
  leftUnitor := fun {X} => ⟨fun _ => X.2.map Id.run, fun _ => X.2.map id⟩
  rightUnitor := fun {X} => ⟨fun _ => X.2.map id, fun _ => X.2.map Id.run⟩

instance : Bifunctor NatTsfm NatTsfm NatTsfm traversableComp where
  map := fun {a _ _ _ } f g α x => 
      have _ := a.snd
      (f _ (fmap (g α) x))

abbrev App (C : (Type u -> Type v) -> Type w) :=
  fun (σ : ΣF, C F) (α : _) => σ.fst α

instance : Bifunctor NatTsfm (· -> ·) (· -> ·) (App Traversable) where
  map := fun {_ b c _} f g x => b.snd.map g (f c x)

instance : MonoidalAction NatTsfm traversableComp (App Traversable) where
  unitor := ⟨Id.run, id⟩
  multiplicator := ⟨id, id⟩
