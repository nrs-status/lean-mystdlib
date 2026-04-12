import Mystdlib.Optics.Categories
import Mystdlib.Optics.CategoriesInstances
import Mystdlib.Optics.Tambara

instance : Profunctor (· -> ·) where
  map := fun f g x => (g ∘ x) ∘ f

instance : Tambara _ _ Prod Prod Prod (· -> ·) where
  tambara := fun f x => (x.1, f x.2)

instance [Monad m] : Tambara (Σα, MonadAlg m α) (·.1 -> ·.1) (monadAlgProd m) monadAlgProdAction monadAlgProdAction (· -> ·)  where
  tambara := fun f x => (x.1, f x.2)

instance : Profunctor (· -> Option ·) where
  map := fun f g x => (fmap g ∘ x) ∘ f

instance : Tambara _ _ Prod Prod Prod (· -> Option ·) where
  tambara := fun f x => (f x.2) >>= fun b => pure (x.1, b)

instance : Tambara _ _ Sum Sum Sum (· -> Option ·) where
  tambara := fun f x => x.casesOn (pure ∘ Sum.inl) (fmap Sum.inr ∘ f)

def Setting (α β : Type u) := fun (ς τ : Type u) => (α -> β) -> ς -> τ

instance : Profunctor (Setting α β) where
  map := fun f g x h k => g (x h (f k))


instance : Tambara _ _ Prod Prod Prod (Setting α β) where
  tambara := fun f g x => (x.1, f g x.2)

instance : Tambara _ _ Sum Sum Sum (Setting α β) where
  tambara := fun f g x => x.casesOn Sum.inl (Sum.inr ∘ f g)

def Classifying (m β ς τ) := [Monad m] -> m ς -> β -> τ

instance {m : Type u -> Type v} [Monad m] {β : Type v} : Profunctor (Classifying m β) where
  map := fun f g x => fun xm => (g ∘ x (fmap f xm))

instance {m : Type -> Type v} [Monad m] {β : Type v} : Tambara _ _ (monadAlgProd m) monadAlgProdAction monadAlgProdAction (Classifying m β) where
  tambara := fun {_} _ μ f _ x b => (μ.snd.alg (fmap Prod.fst x), f (fmap Prod.snd x) b)

def Aggregating (α β ς τ) := List ς -> (List α -> β) -> τ 

instance {α β : Type u} : Profunctor (Aggregating α β) where
  map := fun f g x y z => g (x (fmap f y) z)

instance {α β : Type u} : Tambara (Σα, MonadAlg List α) _ (monadAlgProd List) monadAlgProdAction monadAlgProdAction (Aggregating α β) where
  tambara := fun {_} _ μ u l f => (μ.2.alg (fmap Prod.fst l), u (fmap Prod.snd l) f)

instance : Tambara _ _ applicativeComp (Appσ Applicative) (Appσ Applicative) (Aggregating α β) where
  tambara := fun {_} _ μ h u f =>
    have _ := μ.2
    Seq.seq (pure (flip h f)) (fun _ => sequence u)

def Updating (m β ς τ) := [Monad m] -> β -> ς -> m τ

instance {m : Type u -> Type v} {β : Type v} [Monad m] : Profunctor (Updating m β) where
  map := fun l r u _ b x => fmap r (u b (l x))

instance {m : Type v -> Type v} {β : Type v} [Monad m] : @Profunctor _ (· -> ·) _ (· -> m ·) _ kleisliCat (Updating m β) :=
  @Profunctor.mk _ _ _ _ _ kleisliCat _ <|
    fun l r u _ x y => fmap r (Monad.join (fmap (u x) (l y)))

instance {m : Type -> Type} {β : Type} [Monad m] : @Tambara _ _ _ (· -> m ·) _ kleisliCat _ _ _ Prod _ Prod Prod _ kleisliBifunctor _ kleisliMonoidalAction _ (Updating m β) _ :=
  @Tambara.mk _ _ _ _ _ kleisliCat _ _ _ _ _ _ _ _ kleisliBifunctor _ kleisliMonoidalAction _ _ _ <|
  fun u _ b (w, x) => fmap (w, ·) (u b x)

