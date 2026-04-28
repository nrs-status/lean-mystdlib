import Mystdlib.Foldable
import Mathlib.Control.Traversable.Basic
import Mystdlib.Optics.Tambara.Tambara
import Mystdlib.Optics.Tambara.Optics
import Mathlib.Control.Fold

open Tamb

instance [inst : Tambs l p]  : Tambs (l ++ []) p where
  tambs := by
    observe : l = l ++ []
    rw [<- this]
    exact inst.tambs

instance : Profunctor (· -> ·) where
  map := fun f g h => (g ∘ h) ∘ f

instance : Tamb ⟨Prod.{u,u}, Prod⟩ (· -> ·) where
  tamb := fun f => fun x => (x.1, f x.2)

instance : Tamb ⟨Sum.{u,u}, Sum⟩ (· -> ·) where
  tamb := fun f => Sum.elim .inl (.inr ∘ f)

instance : Tamb ⟨App Traversable, App Traversable⟩ (· -> ·) where
  tamb := fun {xμ _ _} f => xμ.snd.toFunctor.map f



instance {α : Type _} : Profunctor (fun (x _ : Type _) => x -> α) where
  map := fun f _ h => h ∘ f

instance {α : Type _} : Tamb ⟨Prod.{u, u}, Prod⟩ (fun x _ => x -> α) where
  tamb := fun f => fun (_, snd) => f snd

instance {α : Type _} : Tamb ⟨Prod.{u, u + 1}, Prod⟩ (fun x _ => x -> α) where
  tamb := fun f => fun (_, snd) => f snd

instance {α : Type _} [Mul α] [One α] : Tamb ⟨App Traversable, App Traversable⟩ (fun x _ => x -> α) where
  tamb := fun {xμ _ _} f x => have := xμ.snd; Traversable.foldMap f x

open Foldable in
instance {α : Type u} [Mul α] [One α] : Tamb ⟨App Foldable, ax⟩ (fun x _ => x -> α) where
  tamb := fun {xμ _ _} f x => xμ.snd.foldMap f x

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

/-
Tamb.tamb {α β} {xμ : μ} : p α β -> p (axₗ α) (axᵣ β)
-/

instance : Tamb ⟨App Traversable, App Traversable⟩ (fun x _ => x -> Option α) where
  tamb := fun {xμ _ _} f x =>
  have := xμ.snd
  -- Monad.join $ this (fun x y => x.elim (f y) (Option.some ∘ Option.some)) .none x -- previous version
  --Monad.join $ this (fun x y => f y |>.elim (.some x) (Option.some ∘ Option.some)) .none x -- reversed direction
  Traversable.foldlm (t := xμ.fst) (m := Id)  
    (fun x => x.elim f fun a _ => .some a) .none x

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
  tamb := fun {xμ _ _} f g => xμ.snd.toFunctor.map (f g)

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

def Tamb.Prism.elim
  /- (x : ProfOptic l α β ς τ) -/
  /- [Tambs l (fun (s t : Type u) => s -> t ⊕ α)] -/
  (x : Prism α β ς τ)
  (f : τ -> γ)
  (g : α -> γ)
  : ς -> γ
  := fun s => match matching x s with
  | .inl x' => f x'
  | .inr x' => g x'

-- traversal downcast

instance {p : Type u -> Type _ -> Type _} [inst : Tamb ⟨App Traversable, App Traversable⟩ p] : Tamb ⟨Sum, Sum⟩ p where
  tamb := fun {μ α β} => @inst.tamb ⟨fun x => μ ⊕ x, inferInstance⟩ α β 

instance {p : Type u -> Type _ -> Type _} [inst : Tamb ⟨App Traversable, App Traversable⟩ p] : Tamb ⟨Prod, Prod⟩ p where
  tamb := fun {μ α β} => @inst.tamb ⟨fun x => μ × x, inferInstance⟩ α β 

--

section 

open Foldable 

-- m added to def lhs otherwise we get a universe bump
set_option linter.unusedVariables false in
abbrev Folding (m : Type u) [Mul m] [One m] (α β ς τ : Type u) := (α -> m) -> (ς -> m)



instance {α β : Type u} [Mul m] [One m] : Profunctor (Folding m α β) where
  map := fun f _ h p => h p ∘ f

instance {α β : Type u} [Mul m] [One m] : Tamb ⟨App Foldable, ax⟩ (Folding m α β) where
  tamb := fun {xμ _ _} f g => xμ.snd.foldMap (f g)

instance {α β : Type u} [Mul m] [One m] : Tamb ⟨App Traversable, ax⟩ (Folding m α β) where
  tamb := fun {xμ _ _} f g x =>
    have := @xμ.snd
    Traversable.foldMap id (Functor.map (f g) x)

instance {α β : Type u} [Mul m] [One m]: Tamb ⟨Prod, Prod⟩ (Folding m α β) where
  tamb := fun f g x => f g x.snd

def toListOf
  {α β ς τ : Type u}
  (x : ProfOptic l α β ς τ)
  [Tambs l (Folding (List α) α β)]
  : ς -> List α
  := x (Folding (List α) α β) id pure

end

def Aggregating (α β ς τ : Type u) := List ς -> (List α -> β) -> τ

instance : Profunctor (Aggregating α β) where
  map := fun f g h l p => g (h (l.map f) p)

instance : Tamb (μ := Σα, Algebra List α) ⟨algProdAction List, algProdAction List⟩ (Aggregating α β) where
  tamb := fun {xμ _ _} f l x => have ⟨fst, snd⟩ := l.unzip; (xμ.snd.alg fst, f snd x)


-- notation; most are taken from Control.Lens.Operators

infixr:90 "<∘>" => ProfOptic.compose

infixr:40 "%~" => over

infixr:40 ".~" => set

infixl:80 "^?" => flip preview

infixr:80 "#" => review

infixr:80 "^.." => flip toListOf
