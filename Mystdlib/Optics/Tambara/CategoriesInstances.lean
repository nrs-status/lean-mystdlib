import Mystdlib.General
import Mystdlib.Misc
import Mystdlib.Traversable
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

-- Applicative and Traversable. their instances are copies of one another

abbrev NatTsfm.{u, v, w} {C : (Type u -> Type v) -> Type w} := fun (σ σ' : ΣF, C F) => ∀α, σ.fst α -> σ'.fst α

abbrev applicativeComp (G F : ΣF, Applicative F) : ΣF, Applicative F := 
  have _ := F.snd
  have _ := G.snd
  ⟨G.fst ∘ F.fst, inferInstance⟩

abbrev traversableComp (G F : ΣF, Traversable F) : ΣF, Traversable F :=
  have _ := F.snd
  have _ := G.snd
  ⟨G.fst ∘ F.fst, inferInstance⟩

instance : Category (ΣF, Applicative F) NatTsfm where
  id := fun _ => id
  comp := fun f g α => Function.comp (f α) (g α)

instance : Category (ΣF, Traversable F) NatTsfm where
  id := fun _ => id
  comp := fun f g α => Function.comp (f α) (g α)


instance : MonoidalCat (ΣF, Applicative F) NatTsfm applicativeComp where
  tensorUnit := ⟨Id, inferInstance⟩
  associator := ⟨fun _ => id, fun _ => id⟩
  leftUnitor := fun {X} => ⟨fun _ => X.2.map Id.run, fun _ => X.2.map id⟩
  rightUnitor := fun {X} => ⟨fun _ => X.2.map id, fun _ => X.2.map Id.run⟩


instance : MonoidalCat (ΣF, Traversable F) NatTsfm traversableComp where
  tensorUnit := ⟨Id, inferInstance⟩
  associator := ⟨fun _ => id, fun _ => id⟩
  leftUnitor := fun {X} => ⟨fun _ => X.2.map Id.run, fun _ => X.2.map id⟩
  rightUnitor := fun {X} => ⟨fun _ => X.2.map id, fun _ => X.2.map Id.run⟩

instance : Bifunctor NatTsfm NatTsfm NatTsfm applicativeComp where
  map := fun {a _ _ _ } f g α x => 
      have _ := a.snd
      (f _ (fmap (g α) x))

instance : Bifunctor NatTsfm NatTsfm NatTsfm traversableComp where
  map := fun {a _ _ _ } f g α x => 
      have _ := a.snd
      (f _ (fmap (g α) x))

abbrev App (C : (Type u -> Type v) -> Type w) :=
  fun (σ : ΣF, C F) (α : _) => σ.fst α

instance : Bifunctor NatTsfm (· -> ·) (· -> ·) (App Applicative) where
  map := fun {_ b c _} f g x => b.snd.map g (f c x)

instance : Bifunctor NatTsfm (· -> ·) (· -> ·) (App Traversable) where
  map := fun {_ b c _} f g x => b.snd.map g (f c x)

instance : MonoidalAction NatTsfm applicativeComp (App Applicative) where
  unitor := ⟨Id.run, id⟩
  multiplicator := ⟨id, id⟩

instance : MonoidalAction NatTsfm traversableComp (App Traversable) where
  unitor := ⟨Id.run, id⟩
  multiplicator := ⟨id, id⟩

instance : MonoidalActionPair ⟨App Traversable, App Traversable⟩ NatTsfm traversableComp where

-- category of algebras of a given monad, used to define algebraic lenses

class Algebra (m : Type u -> Type v) [Monad m] (α : Type u) where
  alg : m α -> α

instance [Monad m] : Algebra m (m α) where
  alg := Monad.join

instance [Monad m] : Algebra m PUnit where
  alg := fun _ => .unit

instance
  [Monad m]
  [alg : Algebra m α]
  [alg' : Algebra m β]
  : Algebra m (α × β) where
    alg := fun xm => (alg.alg (do pure (<- xm).fst), alg'.alg (do pure (<- xm).snd))

instance [Monad m] : Category (Σα, Algebra m α) (·.fst -> ·.fst) where
  id := id
  comp := fun f g => f ∘ g

def algProd {m : Type u -> Type v} [Monad m] : (α : Type u) × Algebra m α → (α : Type u) × Algebra m α → (α : Type u) × Algebra m α :=
  (fun σ σ' => ⟨σ.fst × σ'.fst, instAlgebraProd.{u,u,v} (alg := σ.snd) (alg' := σ'.snd)⟩)

instance {m : Type u -> Type v} 
  [Monad m] 
  : Bifunctor 
    (C₀ := (Σα, Algebra m α)) 
    (D₀ := (Σα, Algebra.{u,v} m α)) 
    (E₀ := (Σα, Algebra.{u,v} m α)) 
    (·.fst -> ·.fst) 
    (·.fst -> ·.fst) 
    (·.fst -> ·.fst) 
    algProd where
      map := fun f g x => ⟨f x.fst, g x.snd⟩

instance {m : Type u -> Type v} [Monad m] : MonoidalCat (Σα, Algebra m α) (fun σ₁ σ₂ => σ₁.1 -> σ₂.1) algProd where
  tensorUnit := ⟨PUnit, inferInstance⟩
  associator := {
    hom := Prod.assoc_inv
    inv := Prod.assoc
  }
  leftUnitor := {

    hom := Prod.snd
    inv := (.unit, ·)
  }
  rightUnitor := {

    hom := Prod.fst
    inv := (·, .unit)
  }

def algProdAction
  (m : Type u -> Type v)
  [Monad m]
  (xμ : Σα, Algebra m α)
  (x : Type _)
  : Type _
  := xμ.fst × x


instance [Monad m] : Bifunctor (·.fst -> ·.fst) (· -> ·) (· -> ·) (algProdAction m) where
  map := fun f g p => (f p.1, g p.2)

instance [Monad m] : MonoidalAction (·.fst -> ·.fst) algProd (algProdAction m) where
  unitor := {
    hom := Prod.snd
    inv := (.unit, ·)
  }
  multiplicator := {
    hom := Prod.assoc
    inv := Prod.assoc_inv
  }

