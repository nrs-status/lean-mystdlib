import Mystdlib.General
import Mystdlib.Optics.Tambara.Tambara
import Mystdlib.Optics.Tambara.CategoriesInstances
import Mystdlib.Optics.Tambara.Optics

abbrev TypeProf (p : _) := Profunctor Trivial (· -> ·) Trivial (· -> ·) p

instance : TypeProf (· -> ·) where
  map := fun f g h => (g ∘ h) ∘ f

abbrev TypeTamb (tensorObj left_action right_action p) [MonoidalCategory Trivial (· -> ·) tensorObj] [MonoidalAction Trivial (· -> ·) tensorObj Trivial (· -> ·) left_action] [MonoidalAction Trivial (· -> ·) tensorObj Trivial (· -> ·) right_action] := Tambara Trivial (· -> ·) tensorObj Trivial (· -> ·) left_action right_action p

instance : TypeTamb Prod Prod Prod (· -> ·) where
  tambara := fun f x => (x.1, f x.2)

instance : TypeTamb Sum Sum Sum (· -> ·) where
  tambara := fun f x => x.elim .inl (.inr ∘ f)

instance : TypeProf (fun _ x => x) where
  map := fun _ g => g

instance : TypeTamb Sum Sum Sum (fun _ x => x) where
  tambara := Sum.inr

instance {α : Type u} : TypeProf (fun (x _ : Type u) => x -> α) where
  map := fun f _ h => h ∘ f

instance {α : Type u} : TypeTamb Prod Prod Prod (fun (x _ : Type u) => x -> α) where
  tambara := fun f x => f x.2

instance {α : Type u} : TypeProf (fun (s t : Type u) => s -> t ⊕ α) where
  map := fun f g h => (Sum.elim (.inl ∘ g) .inr ∘ h) ∘ f

instance {α : Type u} : TypeTamb Sum Sum Sum (fun (s t : Type u) => s -> t ⊕ α) where
  tambara := fun f x => x.elim (fun y => .inl (.inl y)) (Sum.elim (fun y => .inl (.inr y)) .inr ∘ f)

instance {α : Type u} {F : Type u -> Type v} : TypeProf (fun (x _ : Type v) => x -> F α) where
  map := fun f _ h => h ∘ f

instance {α : Type u} : TypeTamb Sum Sum Sum (fun (x _ : Type u) => x -> Option α) where
  tambara := fun f => Sum.elim (fun _ => .none) f

instance {α : Type u} : TypeTamb Prod Prod Prod (fun (x _ : Type u) => x -> Option α) where
  tambara := fun f => f ∘ Prod.snd

instance {F : Type u -> Type u} [Functor F] : TypeProf (· -> F ·) where
  map := fun f g h => (fmap g ∘ h) ∘ f

instance {F : Type u -> Type u} [Functor F] : TypeTamb Prod Prod Prod (· -> F ·) where
  tambara := fun f x => fmap (x.1, ·) (f x.2)


instance {F : Type u -> Type u} [inst : Applicative F] : TypeTamb Sum Sum Sum (· -> F ·) where
  tambara := fun f x => match x with
  | .inl x' => pure (.inl x')
  | .inr x' => fmap .inr (f x')

abbrev Setting (α β : Type u) := fun (ς τ : Type u) => (α -> β) -> ς -> τ

instance : TypeProf (Setting α β) where
  map := fun f g x h k => g (x h (f k))

instance : TypeTamb Prod Prod Prod (Setting α β) where
    tambara := fun f g x => (x.1, f g x.2)

instance : TypeTamb Sum Sum Sum (Setting α β) where
  tambara := fun f g x => x.elim .inl (.inr ∘ f g)

abbrev Replacing (α β ς τ : Type u) := (α -> β) -> ς -> τ

instance : TypeProf (Replacing α β) where
  map := fun l r u f => r ∘ u f ∘ l

instance : TypeTamb Prod Prod Prod (Replacing α β) where
  tambara := fun f g x => (x.1, f g x.2)

instance : TypeTamb Sum Sum Sum (Replacing α β) where
  tambara := fun u f x => x.casesOn Sum.inl (Sum.inr ∘ u f)

variable
 [MonoidalCategory monobj monhom tensorObj]
 [Liftable monobj Trivial Trivial actionₗ]
 [Liftable monobj Trivial Trivial actionᵣ]
 [MonoidalAction monobj monhom tensorObj Trivial (· -> ·) actionₗ]
 [MonoidalAction monobj monhom tensorObj Trivial (· -> ·) actionᵣ]
 {α β ς τ : Type u}
 (xprofopt : ProfOptic monobj monhom tensorObj Trivial (· -> ·) actionₗ actionᵣ α β ς τ)


def view
  [Tambara monobj monhom tensorObj Trivial (· -> ·) actionₗ actionᵣ (fun x _ => x -> α)]
  : ς -> α
  := xprofopt (fun x _ => x -> α) id

def preview
  [Tambara monobj monhom tensorObj Trivial (· -> ·) actionₗ actionᵣ (fun x _ => x -> Option α)]
  : ς -> Option α 
  := xprofopt (fun x _ => x -> Option α) Option.some

def build
  [Tambara monobj monhom tensorObj Trivial (· -> ·) actionₗ actionᵣ (fun _ x => x)]
  : β -> τ
  := xprofopt (fun _ x => x)

def matching
  [Tambara monobj monhom tensorObj Trivial (· -> ·) actionₗ actionᵣ (fun s t => s -> t ⊕ α)]
  : ς -> τ ⊕ α
  := xprofopt (fun s t => s -> t ⊕ α) .inr
  
def set
  [Tambara monobj monhom tensorObj Trivial (· -> ·) actionₗ actionᵣ (Setting α β)]
  : β -> ς -> τ
  := fun b => xprofopt (Setting α β) id (fun _ => b)

def over 
  [Tambara monobj monhom tensorObj Trivial (· -> ·) actionₗ actionᵣ (Replacing α β)]
  : (α -> β) -> ς -> τ
  := xprofopt (Replacing α β) id

