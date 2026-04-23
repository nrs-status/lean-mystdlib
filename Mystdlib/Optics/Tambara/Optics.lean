import Mystdlib.Foldable
import Mathlib.Control.Traversable.Basic
import Mystdlib.Optics.Tambara.Tambara
import Mystdlib.Optics.Tambara.CategoriesInstances

namespace Tamb

open Foldable

def ExGetter {μ} (α ς) := ExOptic (μ := μ) ⟨fun _ x => x, fun _ _ => PUnit⟩ α PUnit ς PUnit

def ExGetter.mk
  (xμ : μ)
  (get : ς -> α)
  : ExGetter (μ := μ) α ς
  := ExOptic.mk (xμ := xμ) get id

def Getter (α ς) := ProfOptic (μ := PUnit) [⟨fun _ x => x, fun _ _ => PUnit⟩] α PUnit ς PUnit

def Getter.mk
  (f : ς -> α)
  : Getter α ς
  := ExOptic.toProfOptic (ExGetter.mk .unit f)


def Fold (α ς) := ProfOptic [⟨App Foldable, App Foldable⟩] α Unit ς Unit 

def Fold.mk
  [Foldable F]
  (f : ς -> F α)
  : Fold α ς
  := ExOptic.toProfOptic (.mk (xμ := ⟨F, inferInstance⟩) f (Foldable.foldl (fun _ _ => .unit) .unit))


def Lens (α β ς τ : Type u) := ProfOptic [⟨Prod, Prod⟩] α β ς τ

def Lens.mk
  (get : ς -> α)
  (set : ς -> β -> τ)
  : Lens α β ς τ
  := ExOptic.toProfOptic (.mk (fun s => (s, get s)) (Function.uncurry set))

def Lens' (α ς) := Lens α α ς ς

def Prism (α β ς τ : Type u) := ProfOptic [⟨Sum, Sum⟩] α β ς τ

def ExPrism (α β ς τ : Type u) := ExOptic ⟨Sum, Sum⟩ α β ς τ

def Prism.mk
  (build : β -> τ)
  (matchfn : ς -> τ ⊕ α)
  : Prism α β ς τ
  := ExOptic.toProfOptic (.mk matchfn (Sum.elim id build))

def Prism' (α ς) := Prism α α ς ς


abbrev ExTraversal (α β ς τ) := ExOptic ⟨App Traversable, App Traversable⟩ α β ς τ

def ExTraversal.mk
  [Traversable F]
  (f : ς -> F α)
  (g : F β -> τ)
  : ExTraversal α β ς τ 
  := ExOptic.mk (xμ := ⟨F, inferInstance⟩) f g

def Split ς α := List α × ς

instance : Functor (Split ς) where
  map := fun f (l, s) => (l.map f, s)

instance : Traversable (Split.{u, u} ς) where
  traverse := fun f (l, s) => Functor.map (flip Prod.mk s) (traverse f l)

def Traversal  (α β ς τ : Type u) := ProfOptic [⟨App Traversable, App Traversable⟩] α β ς τ



def Traversal.mk
  (f : ς -> List α × (List β -> τ))
  : Traversal α β ς τ 
  := ExOptic.toProfOptic (ExTraversal.mk (F := Split ς) (fun s => (f s |>.fst, s)) (fun (l, s) => f s |>.snd l))

def Traversal' (α ς) := Traversal α α ς ς

-- Van Laarhoven encoding

def LensVL (α β ς τ) := (F : _) -> [Functor F] -> (α -> F β) -> ς -> F τ

inductive PStore α β τ 
| mk : (β -> τ) -> α -> PStore α β τ

instance {α β : Type u} : Functor (PStore α β) where
  map := fun g ⟨l, r⟩ => ⟨g ∘ l, r⟩

def Lens.ofVL
  (x : LensVL α β ς τ)
  : Lens α β ς τ
  := fun _ inst =>
    inst.map ((fun ⟨l, r⟩ => (l, r)) ∘ x _ (PStore.mk id)) (fun (f, b) => f b) ∘ (inst.tambs 0).tamb
