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
  --[Tambara monobj monhom tensorObj Trivial (· -> ·) actionₗ actionᵣ (fun _ x => x)]
  (x : ProfOptic μ l α β ς τ)
  [Tambs l (fun _ x => x)]
  : β -> τ
  := x (fun _ x => x)


