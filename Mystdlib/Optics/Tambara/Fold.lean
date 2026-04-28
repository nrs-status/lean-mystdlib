import Mystdlib.Foldable
import Mystdlib.Optics.Tambara.Combinators

open Tamb
open Foldable 

class Contravariant (F : Type u -> Type v) where
  contramap : (β -> α) -> F α -> F β

def FoldVL (α ς) := (F : _) -> [Contravariant F] -> [Applicative F] -> (α -> F α) -> ς -> F ς

def ExFold1 (α ς) := ExOptic ⟨App Foldable.Foldable, fun _ _ => PUnit⟩ α PUnit ς PUnit

def ExFold1.mk
  [Foldable.Foldable F]
  (f : ς -> F α)
: ExFold1 α ς :=
  ExOptic.mk (xμ := ⟨F, inferInstance⟩) f id

def ExFold2 (α ς) := ExOptic (μ := PUnit) ⟨fun _ x => List x, fun _ _ => PUnit⟩ α PUnit ς PUnit

def ExFold2.mk
  (f : ς -> List α)
  : ExFold2 α ς
  := ExOptic.mk (xμ := .unit) f id

/- def foldMapOf -/
/-   {α β ς τ : Type u} -/
/-   (x : ProfOptic.{u+1, u} l α β ς τ) -/
/-   [Tambs l (Folding α β)] -/
/-   : (m : Type u) -> [Mul m] -> [One m] -> (α -> m) -> (ς -> m) -/
/-   := x (Folding α β) (fun _ _ _ f => f) -/

def Folding2 (α β ς τ : Type u) := [Mul α] -> [One α] -> ς -> α 

instance : Profunctor (Folding2 α β) where
  map := fun f _ x => x ∘ f

/- instance [Mul α] [One α] : Tamb ⟨App Foldable, app⟩ (Folding2 α β) where -/
/-   tamb := fun {_ _ xμ} f _ _ => xμ.snd.foldMap f -/

def foldOf
  (x : ProfOptic l α β ς τ)
  [Mul α] [One α]
  [Tambs l (Folding2 α β)]
  : ς -> α
  := x (Folding2 α β) id

/- def foldOf' -/
/-   {α β ς τ : Type u} -/
/-   (x : ProfOptic.{u+1,u} l α β ς τ) -/
/-   [Mul α] [One α] -/
/-   [Tambs l (Folding α β)] -/
/-   : ς -> α -/
/-   := x (Folding α β) (fun _ _ _ => id) α id -/

/- def foldrOf -/
/-   (x : ProfOptic l α β ς τ) -/
/-   [Tambs l (Folding α β)] -/
/-   : (α -> γ -> γ) -> γ -> ς -> γ -/
/-   := fun f y s => foldMapOf x (γ -> γ) f s y -/

/- def foldlOf -/
/-   (x : ProfOptic l α β ς τ) -/
/-   [Tambs l (Folding α β)] -/
/-   : (γ -> α -> γ) -> γ -> ς -> γ -/
/-   := fun f y s => foldrOf x (fun a z => f z a) y s -/


def traversed
  [Traversable F]
  : Traversal α β (F α) (F β)
  :=
  Traversal.mk' (F := F) id id

def folded 
  [Foldable F]
  : Fold α (F α)
  := .mk (F := F) id

