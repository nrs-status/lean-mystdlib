import Mystdlib.Bazaar
import Mystdlib.Foldable
import Mathlib.Control.Traversable.Basic
import Mystdlib.Optics.Tambara.Tambara
import Mystdlib.Optics.Tambara.CategoriesInstances
import Mystdlib.Traversable

namespace Tamb

open Foldable

def ExIso (α β ς τ : Type u) := ExOptic (μ := PUnit) ⟨fun _ x => x, fun _ x => x⟩ α β ς τ

def ExIso.mk
  {α β ς τ : Type u}
  (f : ς -> α)
  (g : β -> τ)
  : ExIso α β ς τ
  := ExOptic.mk (xμ := .unit) f g

def Iso (α β ς τ : Type u) := ProfOptic [] α β ς τ

def Iso.mk
  (f : ς -> α)
  (g : β -> τ)
  : Iso α β ς τ
  := fun _ tamb => tamb.map f g

abbrev Iso' (α ς) := Iso α α ς ς


def ExGetter {μ} (α ς) := ExOptic (μ := μ) ⟨fun _ x => x, fun _ _ => PUnit⟩ α PUnit ς PUnit

def ExGetter.mk
  (xμ : μ)
  (get : ς -> α)
  : ExGetter (μ := μ) α ς
  := ExOptic.mk (xμ := xμ) get id

def Getter (μ α ς) := ProfOptic  [Sigma.mk μ ⟨fun _ x => x, fun _ _ => PUnit⟩] α PUnit ς PUnit

def Getter.mk
  (f : ς -> α)
  : Getter PUnit α ς
  := ExOptic.toProfOptic (ExGetter.mk .unit f)


def Fold (α ς : Type u) := ProfOptic [Sigma.mk _ ⟨App Foldable, App Foldable⟩] α PUnit ς PUnit 

def Fold.mk
  [Foldable F]
  (f : ς -> F α)
  : Fold α ς
  := ExOptic.toProfOptic (.mk (xμ := ⟨F, inferInstance⟩) f (Foldable.foldl (fun _ _ => .unit) .unit))


def Lens (α β ς τ : Type u) := ProfOptic [Sigma.mk _ ⟨Prod, Prod⟩] α β ς τ

def Lens.mk
  (get : ς -> α)
  (set : ς -> β -> τ) 
  : Lens α β ς τ
  := ExOptic.toProfOptic (.mk (fun s => (s, get s)) (Function.uncurry set))

abbrev Lens' (α ς) := Lens α α ς ς

def Prism (α β ς τ : Type u) := ProfOptic [Sigma.mk _ ⟨Sum, Sum⟩] α β ς τ

def ExPrism (α β ς τ : Type u) := ExOptic ⟨Sum, Sum⟩ α β ς τ

def Prism.mk
  (build : β -> τ)
  (matchfn : ς -> τ ⊕ α)
  : Prism α β ς τ
  := ExOptic.toProfOptic (.mk matchfn (Sum.elim id build))

abbrev Prism' (α ς) := Prism α α ς ς


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

abbrev Traversal  (α β ς τ : Type u) := ProfOptic [Sigma.mk _ ⟨App Traversable, App Traversable⟩] α β ς τ

def Traversal.mk'
  [Traversable F]
  (f : ς -> F α)
  (g : F β -> τ)
  : Traversal α β ς τ
  := ExOptic.toProfOptic (ExTraversal.mk f g)

def Traversal.mk
  (f : ς -> List α × (List β -> τ))
  : Traversal α β ς τ 
  := Traversal.mk' (F := Split ς) (fun s => (f s |>.fst, s)) (fun (l, s) => f s |>.snd l)

def Traversal.mk'' 
  (f : ς -> Bazaar α β τ)
  : Traversal α β ς τ
  := fun _ inst =>
    have := inst.tambs 0 |>.tamb (xμ := ⟨(Bazaar · β τ), inferInstance⟩)  
    inst.map f Bazaar.sold ∘ this

abbrev Traversal' (α ς) := Traversal α α ς ς

def educational.Traversal.toExTraversal -- as in Pickering
  {α β ς τ : Type u}
  (x : Traversal.{u, u + 1} α β ς τ)
  : ExOptic ⟨App Traversable, App Traversable⟩ α β ς τ
  := 
    let : ExOptic ⟨App Traversable, App Traversable⟩ α β α β := 
      .mk (xμ := ⟨(Bazaar · β β), inferInstance⟩) Bazaar.sell Bazaar.sold
    x (ExOptic ⟨App Traversable, App Traversable⟩ α β) this

def ExTraversal.extract 
  (x : ExTraversal α β ς τ)
  : ς -> Bazaar α β τ
  := match x with
  | ExOptic.mk (xμ := xμ) l r => (Functor.map r) ∘ xμ.snd.traverse Bazaar.sell ∘ l




-- not sure which version of AffineTraversal is the correct one; defining both

def AffineTraversal (α β ς τ : Type u) := ProfOptic [Sigma.mk _ ⟨Prod, Prod⟩, Sigma.mk _ ⟨Sum, Sum⟩] α β ς τ

def AffineTraversal.mk
  {α β ς τ : Type u}
  (matchfn : ς -> τ ⊕ α)
  (set : ς -> β -> τ)
  : AffineTraversal α β ς τ
  := fun _ inst pab =>
    have y₀ := (inst.tambs 1).tamb (xμ := τ) pab
    have y₁ := (inst.tambs 0).tamb (xμ := ς) y₀
    have f := fun (s : ς) => (s, matchfn s)
    have g := fun (pair : ς × (τ ⊕ β)) => pair.snd.elim id (set pair.fst)
    inst.map f g y₁

abbrev AffineTraversal' (α ς : Type u) := AffineTraversal α α ς ς

abbrev Affine (xμ : Type u × Type u) (α : Type u) := xμ.fst ⊕ (xμ.snd × α)

def AffineTraversalb (α β ς τ : Type u) := ProfOptic [Sigma.mk _ ⟨Affine, Affine⟩] α β ς τ

def AffineTraversalb.mk
  {α β ς τ : Type u}
  (matchfn : ς -> τ ⊕ α)
  (set : ς -> β -> τ)
  : AffineTraversalb α β ς τ
  := fun _ inst pab =>
    inst.map 
      (fun s => (matchfn s).elim .inl (fun a => .inr (s, a))) 
      (Sum.elim id (Function.uncurry set)) 
      ((inst.tambs 0).tamb (xμ := (τ, ς)) pab)


abbrev AffineTraversalb' (α ς : Type u) := AffineTraversalb α α ς ς


def AlgebraicLens (m : Type u -> Type v) [Monad m] (α β ς τ : Type u) := 
  ProfOptic [Sigma.mk _ ⟨algProdAction m, algProdAction m⟩] α β ς τ

def AlgebraicLens.mk
  [Monad m]
  (get : ς -> α)
  (set : m ς -> β -> τ)
  : AlgebraicLens m α β ς τ
  := ExOptic.toProfOptic <| .mk 
    (xμ := ⟨m ς, inferInstance⟩) 
    (fun s => (pure s, get s)) 
    (fun (xms, b) => set xms b)

def Kaleidoscope (α β ς τ : Type u) :=
  ProfOptic [Sigma.mk _ ⟨App Applicative, App Applicative⟩] α β ς τ
    
def Kaleidoscope.mk
  (f : {n : Nat} -> ((Vector α n) -> β) -> Vector ς n -> τ)
  : Kaleidoscope α β ς τ
  := ExOptic.toProfOptic <| .mk
    (xμ := ⟨Bazaar ς α, inferInstance⟩)
    .sell
    (fun ⟨_, elms, cont⟩ => f cont elms)


--

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

def AffTraversalVL (α β ς τ) := (F : _) -> [Functor F] -> [Pure F] -> (α -> F β) -> ς -> F τ






