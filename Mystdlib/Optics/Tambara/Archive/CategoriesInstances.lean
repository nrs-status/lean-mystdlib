import Mystdlib.General
import Mystdlib.Optics.TambaraBundled.Categories
import Mathlib.Control.Traversable.Basic


instance : Category (Type u) (· -> ·) where
  id := id
  comp := Function.comp

def NatTsfmσ {C : (Type _ -> Type _) -> Type _} (σ₁ σ₂ : ΣF : Type _ -> Type _, C F) :=
  (α : Type _) -> σ₁.1 α -> σ₂.1 α

instance : Category (Type _ -> Type _) (fun f g => (α : Type _) -> f α -> g α) where
  id := fun _ => id
  comp := fun f g α => Function.comp (f α) (g α)

instance : Category (ΣF, Functor F) NatTsfmσ where
  id := fun _ => id
  comp := fun f g α => Function.comp (f α) (g α)

instance : Category (ΣF, Applicative F) NatTsfmσ where
  id := fun _ => id
  comp := fun f g α => Function.comp (f α) (g α)

instance : Category (ΣF, Traversable F) NatTsfmσ where
  id := fun _ => id
  comp := fun f g α => Function.comp (f α) (g α)


instance : Bifunctor (· -> ·) (· -> ·) (· -> ·) Prod where
  map := fun f g (l, r) => (f l, g r)

instance : Bifunctor (· -> ·) (· -> ·) (· -> ·) Sum where
  map := fun f g xsum => match xsum with
  | .inl x => .inl (f x)
  | .inr x => .inr (g x)

@[reducible]
def functorComp (G F : ΣF, Functor F) : ΣF, Functor F :=
  have _ := F.2
  have _ := G.2
  ⟨G.1 ∘ F.1, { map := (fun f xfg => (Functor.map (Functor.map f)) xfg) }⟩ 

@[reducible]
def applicativeComp (G F : ΣF, Applicative F) : ΣF, Applicative F := 
  have _ := F.2
  have _ := G.2
  ⟨G.1 ∘ F.1, { 
    pure := fun a => let aux := G.2.pure a; let r := fmap F.2.pure aux; r
    seq := fun f g =>   G.2.seq (fmap (fun f' g' => F.2.seq f' (fun _ => g')) f) g
    } ⟩

@[reducible]
def traversableComp (G F : ΣF, Traversable F) : ΣF, Traversable F :=
  have _ := F.2
  have _ := G.2
  ⟨G.1 ∘ F.1, { 
    traverse := fun f x => (G.2.traverse (F.2.traverse f)) x
    }⟩

instance : Bifunctor NatTsfmσ NatTsfmσ NatTsfmσ functorComp where
  map := fun {a b c d} f g α x => b.snd.map (g _) (f _ x)

instance : Bifunctor NatTsfmσ NatTsfmσ NatTsfmσ applicativeComp where
  map := 
    fun {_ b c d} f g α x =>
      have _ := b.snd
      have _ := (applicativeComp b d).2.toFunctor
      (fmap (g α) (f (c.fst α) x) : b.fst (d.fst α))

instance : Bifunctor NatTsfmσ NatTsfmσ NatTsfmσ traversableComp where
  map := fun {a _ _ _ } f g α x => 
      have _ := a.snd
      (f _ (fmap (g α) x))

@[reducible]
def Appσ (C : (Type u -> Type v) -> Type (max (u + 1) v)) (σ : ΣF : Type u -> Type v, C F) (α : Type u) :=
  σ.1 α

instance : Bifunctor NatTsfmσ (· -> ·) (· -> ·) (Appσ Functor) where
  map := fun {_ b c _} f g x => b.snd.map g (f c x)

instance : Bifunctor NatTsfmσ (· -> ·) (· -> ·) (Appσ Applicative) where
  map := fun {_ b c _} f g x => b.snd.map g (f c x)

instance : Bifunctor NatTsfmσ (· -> ·) (· -> ·) (Appσ Traversable) where
  map := fun {_ b c _} f g x => b.snd.map g (f c x)


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


instance : MonoidalCat (ΣF, Functor F) NatTsfmσ functorComp where
  tensorUnit := ⟨Id, inferInstance⟩
  associator := {
    hom := fun _ => id
    inv := fun _ => id
  }
  leftUnitor := fun {X} => {
    hom := fun _ => X.2.map Id.run
    inv := fun _ => X.2.map id
  }
  rightUnitor := fun {X} => {
    hom := fun _ => X.2.map id
    inv := fun _ => X.2.map Id.run
  }

instance : MonoidalCat (ΣF, Applicative F) NatTsfmσ applicativeComp where
  tensorUnit := ⟨Id, inferInstance⟩
  associator := {
    hom := fun _ => id
    inv := fun _ => id
  }
  leftUnitor := fun {X} => {
    hom := fun _ => X.2.map Id.run
    inv := fun _ => X.2.map id
  }
  rightUnitor := fun {X} => {
    hom := fun _ => X.2.map id
    inv := fun _ => X.2.map Id.run
  }

instance : MonoidalCat (ΣF, Traversable F) NatTsfmσ traversableComp where
  tensorUnit := ⟨Id, inferInstance⟩
  associator := ⟨fun _ => id, fun _ => id⟩
  leftUnitor := fun {X} => ⟨fun _ => X.2.map Id.run, fun _ => X.2.map id⟩
  rightUnitor := fun {X} => ⟨fun _ => X.2.map id, fun _ => X.2.map Id.run⟩

instance : MonoidalAction functorComp (Appσ Functor) where
  unitor := ⟨Id.run, id⟩
  multiplicator := ⟨id, id⟩

instance : MonoidalAction applicativeComp (Appσ Applicative) where
  unitor := ⟨Id.run, id⟩
  multiplicator := ⟨id, id⟩

instance : MonoidalAction traversableComp (Appσ Traversable) where
  unitor := ⟨Id.run, id⟩
  multiplicator := ⟨id, id⟩

instance [Category C₀ C₁] [MonoidalCat C₀ C₁ O] [Bifunctor _ _ _ O] : MonoidalAction O O where
  unitor := {
    hom := MonoidalCat.leftUnitor.hom
    inv := MonoidalCat.leftUnitor.inv
  }
  multiplicator := {
    hom := MonoidalCat.associator.inv
    inv := MonoidalCat.associator.hom
  }


class MonadAlg m [Monad m] (α : Type) where
  alg : m α -> α

instance [Monad m] : MonadAlg m (m α) where
  alg := Monad.join

instance [Monad m] : Category (Σα, m α) (fun σ₁ σ₂ => m σ₁.1 -> m σ₂.1) where
  id := id
  comp := Function.comp

instance [Monad m] : Category (Σα, MonadAlg m α) (·.1 -> ·.1) where
  id := id
  comp := Function.comp

@[reducible]
def monadAlgProd (m) [Monad m] (σ₁ σ₂ : Σα, MonadAlg m α) : Σα, MonadAlg m α :=
  ⟨σ₁.1 × σ₂.1, ⟨fun xm => (σ₁.2.alg (Functor.map Prod.fst xm), σ₂.2.alg (Functor.map Prod.snd xm))⟩⟩


instance [Monad m] : Bifunctor (Sigma.fst · -> Sigma.fst ·) (Sigma.fst · -> Sigma.fst ·) (Sigma.fst · -> Sigma.fst ·) (monadAlgProd m) where
  map := fun f g h => (f h.1, g h.2)

instance [Monad m] : MonadAlg m Unit where
  alg := fun _ => .unit

instance [Monad m] [MonadAlg m α] [MonadAlg m β] : MonadAlg m (α × β) where
  alg := fun xm => (MonadAlg.alg (Functor.map Prod.fst xm), MonadAlg.alg (Functor.map Prod.snd xm))

instance [Monad m] : MonoidalCat (Σα, MonadAlg m α) (fun σ₁ σ₂ => σ₁.1 -> σ₂.1) (monadAlgProd m) where
  tensorUnit := ⟨Unit, inferInstance⟩
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

def monadAlgProdAction [Monad m] := fun (σ : Σα, MonadAlg m α) (α : Type _) => σ.1 × α

instance [Monad m] : Bifunctor (Sigma.fst · -> Sigma.fst ·) (· -> ·) (· -> ·) (monadAlgProdAction (m := m)) where
  map := fun f g p => (f p.1, g p.2)


instance [Monad m] : MonoidalAction (monadAlgProd m) monadAlgProdAction where
  unitor := {
    hom := Prod.snd
    inv := (.unit, ·)
  }
  multiplicator := {
    hom := Prod.assoc
    inv := Prod.assoc_inv
  }


@[reducible]
def kleisliCat {m : Type u -> Type u} [Monad m] : Category (Type _) (· -> m ·) where
  id := pure
  comp := fun f g x => Monad.join (fmap f (g x))

@[reducible]
def kleisliBifunctor {m : Type u -> Type u} [Monad m] : @Bifunctor _ _ _ (· -> ·) (· -> m ·) (· -> m ·) _ kleisliCat kleisliCat Prod :=
  @Bifunctor.mk _ _ _ _ _ _ _ kleisliCat kleisliCat _
    fun f g x => fmap (fun d => (f x.1, d)) (g x.2)

/- @[reducible] -/
/- def kleisliMonoidalAction {m : Type u -> Type u} [Monad m] : @MonoidalAction (Type _) (· -> ·) (Type _) (· -> ·) _ _ Prod _ _ Prod _ := inferInstance -/

@[reducible]
def kleisliMonoidalAction {m : Type _ -> Type _} [Monad m] : @MonoidalAction (Type _) (· -> m ·) (Type _) (· -> ·) kleisliCat _ Prod _ _ _ kleisliBifunctor :=
  @MonoidalAction.mk _ _ _ _ kleisliCat _ _ _ _ _ kleisliBifunctor 
    (fun {X} => (@IsoStruct.mk _ _ kleisliCat _ _ (pure ∘ Prod.snd) (fun x => pure (.unit, x))))
    (fun {X P Q} => @IsoStruct.mk _ _ kleisliCat _ _ 
      (fun x => pure (Prod.assoc x)) 
      (fun x => pure (Prod.assoc_inv x)))

