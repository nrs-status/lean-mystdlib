import Mystdlib.Optics.Tambara.Tambara

instance : Profunctor (· -> ·) where
  map := fun f g h => (g ∘ h) ∘ f

instance : Tamb ⟨Prod.{u,u}, Prod⟩ (· -> ·) where
  tamb := fun f => fun x => (x.1, f x.2)

instance : Tamb ⟨Sum.{u,u}, Sum⟩ (· -> ·) where
  tamb := fun f => Sum.elim .inl (.inr ∘ f)

instance {α : Type _} : Profunctor (fun (x _ : Type _) => x -> α) where
  map := fun f _ h => h ∘ f

instance {α : Type _} : Tamb ⟨Prod.{u, u}, Prod⟩ (fun x _ => x -> α) where
  tamb := fun f => fun (_, snd) => f snd

def view 
  (x : ProfOptic μ l α β ς τ)
  [Tambs l (fun x _ => x -> α)]
  : ς -> α :=
  (x (fun ξ _ => ξ -> α)) id

instance : Profunctor (fun _ x => x) where
  map := fun _ f => f

instance : Tamb ⟨Sum.{u, u}, Sum⟩ (fun _ x => x) where
  tamb := fun x => .inr x

def review
  (x : ProfOptic μ l α β ς τ)
  [Tambs l (fun _ x => x)]
  : β -> τ
  := x (fun _ x => x)
  
instance : Profunctor (fun x _ => x -> Option α) where
  map := fun f _ h => h ∘ f

instance : Tamb ⟨Sum.{u,u}, Sum⟩ (fun x _ => x -> Option α) where
  tamb := fun f => Sum.elim (fun _ => .none) f

def preview
  (x : ProfOptic μ l α β ς τ)
  [Tambs l (fun x _ => x -> Option α)]
  : ς -> Option α 
  := x (fun x _ => x -> Option α) Option.some


abbrev Setting (α β : Type u) := fun (ς τ : Type u) => (α -> β) -> ς -> τ

instance : Profunctor (Setting α β) where
  map := fun f g x h k => g (x h (f k))

instance : Tamb ⟨Prod.{u, u}, Prod⟩ (Setting α β) where
  tamb := fun f g x => (x.1, f g x.2)

instance : Tamb ⟨Sum.{u,u}, Sum⟩ (Setting α β) where
  tamb := fun f g x => x.elim .inl (.inr ∘ f g)

def set
  (x : ProfOptic μ l α β ς τ)
  [Tambs l (Setting α β)]
  : β -> ς -> τ
  := fun b => x (Setting α β) id (fun _ => b)

abbrev Replacing (α β ς τ : Type u) := (α -> β) -> ς -> τ

instance : Profunctor (Replacing α β) where
  map := fun l r u f => r ∘ u f ∘ l

instance : Tamb ⟨Prod.{u,u}, Prod⟩ (Replacing α β) where
  tamb := fun f g x => (x.1, f g x.2)

instance : Tamb ⟨Sum.{u,u}, Sum⟩ (Replacing α β) where
  tamb := fun u f x => x.casesOn Sum.inl (Sum.inr ∘ u f)

def over 
  (x : ProfOptic μ l α β ς τ)
  [Tambs l (Replacing α β)]
  : (α -> β) -> ς -> τ
  := x (Replacing α β) id




