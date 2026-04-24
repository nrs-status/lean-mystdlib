import Mathlib.Control.Traversable.Basic
import Mystdlib.Optics.Tambara.Tambara
import Mystdlib.Optics.Tambara.Optics
import Mathlib.Control.Fold

open Tamb

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

instance {α : Type _} : Tamb ⟨Prod.{u, u + 1}, Prod⟩ (fun x _ => x -> α) where
  tamb := fun f => fun (_, snd) => f snd

instance {α : Type _} [Mul α] [One α] : Tamb ⟨App Traversable, App Traversable⟩ (fun x _ => x -> α) where
  tamb := fun {ξ _ xμ} f x => @Traversable.foldMap (t := xμ.fst) xμ.snd ξ α _ _ f x

def view 
  (x : ProfOptic l α β ς τ)
  [Tambs l (fun x _ => x -> α)]
  : ς -> α :=
  (x (fun ξ _ => ξ -> α)) id

instance : Profunctor (fun _ x => x) where
  map := fun _ f => f

instance : Tamb ⟨Sum.{u, u}, Sum⟩ (fun _ x => x) where
  tamb := fun x => .inr x

def review
  (x : ProfOptic l α β ς τ)
  [Tambs l (fun _ x => x)]
  : β -> τ
  := x (fun _ x => x)
  
instance : Profunctor (fun x _ => x -> Option α) where
  map := fun f _ h => h ∘ f

instance : Tamb ⟨Sum.{u,u}, Sum⟩ (fun x _ => x -> Option α) where
  tamb := fun f => Sum.elim (fun _ => .none) f

instance : Tamb ⟨Prod.{u,u}, Prod⟩ (fun x _ => x -> Option α) where
  tamb := fun f x => f x.snd

instance : Tamb ⟨Affine, Affine⟩ (fun x _ => x -> Option α) where
  tamb := fun f x => x.elim (fun _ => .none) (f ∘ Prod.snd)


def preview
  (x : ProfOptic l α β ς τ)
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

instance : Tamb ⟨Affine, Affine⟩ (Setting α β) where
  tamb := fun f g => Sum.elim .inl (fun x => .inr (x.fst, f g x.snd))

def set
  (x : ProfOptic l α β ς τ)
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

instance : Tamb ⟨App Traversable, App Traversable⟩ (Replacing α β) where
  tamb := fun {_ _ xμ} f g => xμ.snd.toFunctor.map (f g)

instance : Tamb ⟨Affine, Affine⟩ (Replacing α β) where
  tamb := fun f g => Sum.elim .inl (fun x => .inr (x.fst, f g x.snd))

def over 
  (x : ProfOptic l α β ς τ)
  [Tambs l (Replacing α β)]
  : (α -> β) -> ς -> τ
  := x (Replacing α β) id


instance : Profunctor (fun s t => s -> t ⊕ α) where
  map := fun f g h => (Sum.elim (.inl ∘ g) .inr ∘ h) ∘ f

instance : Tamb ⟨Sum, Sum⟩ (fun (s t : Type u) => s -> t ⊕ α) where
  tamb := fun f => Sum.elim (fun xm => .inl (.inl xm)) (fun a => (f a).elim (fun b => .inl (.inr b)) .inr)

instance : Tamb ⟨Affine, Affine⟩ (fun (s t : Type u) => s -> t ⊕ α) where
  tamb := fun f => Sum.elim 
    (fun x => (.inl (.inl x))) 
    (fun (fst, snd) => f snd |>.elim 
      (fun y => .inl (.inr (fst, y))) 
      .inr)

def matching
  (x : ProfOptic l α β ς τ)
  [Tambs l (fun (s t : Type u) => s -> t ⊕ α)]
  : ς -> τ ⊕ α
  := x (fun s t => s -> t ⊕ α) .inr


