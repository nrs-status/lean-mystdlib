import Mathlib.Control.Traversable.Basic
import Mystdlib.FunList
import Mystdlib.Optics.Categories
import Mystdlib.Optics.CategoriesInstances
import Mystdlib.Optics.Tambara

instance : Category Type (· -> ·) := inferInstance
def Lens (α β ς τ : Type) := ProfOptic Type _ Prod Prod Prod α β ς τ 

def Lens.mk (get : ς -> α) (set : ς -> β -> τ) : Lens α β ς τ := 
  Optic.toProfOptic Prod Prod (Optic.mk (O := Prod) (fun s => (s, get s)) (fun (s, b) => set s b))

def Prism (α ς) := ProfOptic _ _ Sum Sum Sum α α ς ς

def Prism.mk (f : ς -> ς ⊕ α) (g : α -> ς) : Prism α ς :=
  Optic.toProfOptic Sum Sum (Optic.mk (O := Sum) f (·.casesOn id g))

def AlgebraicLens (m α ς) [Monad m] := ProfOptic (Σα, MonadAlg m α) (Sigma.fst · -> Sigma.fst ·) (MonadAlgProd m) (Sigma.fst · × ·) (Sigma.fst · × ·) α α ς ς

def AlgebraicLens.mk [Monad m] (α ς) (f : ς -> α) (g : m ς -> α -> ς) : AlgebraicLens m α ς :=
  have := Optic.mk 
    (O := MonadAlgProd m) 
    (μ := ⟨m ς, inferInstance⟩) 
    (actionₗ := (fun (x1 : (α : Type) × MonadAlg m α) x2 => x1.fst × x2)) 
    (actionᵣ := (fun (x1 : (α : Type) × MonadAlg m α) x2 => x1.fst × x2)) 
    (fun s => (pure s, f s)) 
    (fun ⟨sm, a⟩ => g sm a)
  Optic.toProfOptic _ _ this

def Kaleidoscope (α ς) := ProfOptic _ _ applicativeComp (Appσ Applicative) (Appσ Applicative) α α ς ς

def Kaleidoscope.mk (f : (Σn, { l : List α // l.length = n } -> α) -> (List ς -> ς)) : Kaleidoscope α ς :=
  let := @Optic.mk 
    _ _ _ _ _ _ _ _ _ 
    applicativeComp
    _ 
    (Appσ Applicative) 
    (Appσ Applicative)
    _ _ _ _ _ 
    α α ς ς 
    ⟨FunList _ _, inferInstance⟩
    (fun s => ⟨1, (⟨[s], !p⟩, id)⟩)
    (fun x => let ⟨n, p⟩ := FunList.unfold x; (f ⟨n, p.2⟩) p.1)
  Optic.toProfOptic _ _ this

def MonadicLens (m) [Monad m] (α β ς τ) := 
  @ProfOptic _ (· -> m ·) _ _ KleisliCat _ _ (· -> ·) Prod _ _ Prod Prod _ _ KleisliBifunctor (KleisliMonoidalAction (m := m)) KleisliMonoidalAction' α β ς τ

def MonadicLens.mk {m α β ς τ} [Monad m] (get : ς -> α) (set : ς -> β -> m τ) : MonadicLens m α β ς τ :=
  let := @Optic.mk
    _ (· -> m ·) _ (· -> ·) _ _ KleisliCat _ _ Prod _ Prod Prod _ _ KleisliBifunctor (KleisliMonoidalAction (m := m)) KleisliMonoidalAction' α β ς τ _ 
    (fun s => Prod.mk s (get s)) 
    (Function.uncurry set)
  @Optic.toProfOptic _ _ _ _ _ _ _ KleisliCat _ _ _ _ _ _ _ KleisliBifunctor _ KleisliMonoidalAction' _ _ _ _ this _ _ _

def Traversal (α ς) := ProfOptic _ _ traversableComp (Appσ Traversable) (Appσ Traversable) α α ς ς 

def Traversal.mk' {α ς F} [Traversable F] (f : ς -> F α) (g : F α -> ς) : Traversal α ς :=
  let := @Optic.mk
    _ (· -> ·) _ (· -> ·) (ΣF, Traversable F) NatTsfmσ _ _ _ traversableComp _ (Appσ Traversable) (Appσ Traversable) _ _ _ _ _ _ _ _ _ 
    ⟨F, inferInstance⟩ 
    f 
    g
  Optic.toProfOptic _ _ this

def Split ς α := List α × ς

instance : Functor (Split ς) where
  map := fun f (l, s) => (l.map f, s)

instance : Traversable (Split.{u, u} ς) where
  traverse := fun f (l, s) => fmap (flip Prod.mk s) (traverse f l)

def Traversal.mk {α ς} (f : ς -> List α × (List α -> ς)) : Traversal α ς :=
  Traversal.mk' (F := Split ς) 
    (fun s => (Prod.fst (f s), s)) 
    (fun (l, s) => (Prod.snd (f s)) l)





