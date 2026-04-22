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

instance : Tamb ⟨Prod.{u,u}, Prod⟩ (fun x _ => x -> Option α) where
  tamb := fun f x => f x.snd

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

instance : Tamb ⟨App Traversable, App Traversable⟩ (Replacing α β) where
  tamb := by simp [Replacing, App]; exact
    fun {_ _ xμ} f g => xμ.snd.toFunctor.map (f g)

def over 
  (x : ProfOptic μ l α β ς τ)
  [Tambs l (Replacing α β)]
  : (α -> β) -> ς -> τ
  := x (Replacing α β) id

instance [Applicative F] : Profunctor (· -> F ·) where
  map := fun f g h => (Functor.map g ∘ h) ∘ f

instance myinst {F : _} [Applicative F] : Tamb ⟨App Traversable, App Traversable⟩ (· -> F ·) where
  tamb := fun {_ _ xμ} => xμ.snd.traverse
  --(x✝¹ → F x✝) → App Traversable xμ x✝¹ → F (App Traversable xμ x✝)


def Traversal.traverse
  (x : Traversal α β ς τ)
  : {F : _} -> [Applicative F] -> (α -> F β) -> ς -> F τ 
  := fun {F _} => x (· -> F ·)

def traverseOfExtract -- for educational purposes; unpacking definitions
  [Applicative F]
  {α β ς τ : Type _}
  (extract : ς -> List α × (List β -> τ))
  : (α -> F β) -> ς -> F τ
  :=
    have f : (Split ς α -> F (Split ς β)) -> ς -> F τ := 
      Profunctor.map 
        (p := (· -> F ·)) 
        (fun s => ((extract s).fst, s))
        (fun (l, s) => (extract s).snd l)  
    have g := fun f (l, s) => Functor.map (·, s) (traverse f l)
    f ∘ g

def traverseOfExtract' -- for educational purposes
  [Applicative F]
  {α β ς τ : Type _}
  (extract : ς -> List α × (List β -> τ))
  : (α -> F β) -> ς -> F τ
  := fun f s =>
    have y₁ : Split ς α := (fun s => ((extract s).fst, s)) s
    have y₂ := Functor.map (·, y₁.snd) (traverse f y₁.fst)
    Functor.map (fun (l, s) => (extract s).snd l) y₂

instance : Profunctor (fun s t => s -> t ⊕ α) where
  map := fun f g h => (Sum.elim (.inl ∘ g) .inr ∘ h) ∘ f

instance : Tamb ⟨Sum, Sum⟩ (fun (s t : Type u) => s -> t ⊕ α) where
  tamb := fun f => Sum.elim (fun xm => .inl (.inl xm)) (fun a => (f a).elim (fun b => .inl (.inr b)) .inr)

def matching
  (x : ProfOptic μ l α β ς τ)
  [Tambs l (fun (s t : Type u) => s -> t ⊕ α)]
  : ς -> τ ⊕ α
  := x (fun s t => s -> t ⊕ α) .inr
