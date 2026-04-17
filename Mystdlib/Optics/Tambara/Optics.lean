import Mystdlib.Optics.Tambara.Tambara
import Mystdlib.Optics.Tambara.CategoriesInstances
import Mathlib.Control.Traversable.Basic


def ExLens (α β ς τ : Type u) := ExOptic Trivial (· -> ·) Prod Trivial (· -> ·) Prod Prod α β ς τ

def ExLens.mk
  (get : ς -> α)
  (set : ς -> β -> τ)
  : ExLens α β ς τ :=
  ExOptic.mk (fun s => (s, get s)) (fun (s, b) => set s b)

def Lens (α β ς τ) := ProfOptic Trivial (· -> ·) Prod Trivial (· -> ·) Prod Prod α β ς τ

abbrev Lens' (α ς) := Lens α α ς ς 

def Lens.mk
  (get : ς -> α)
  (set : ς -> β -> τ)
  : Lens α β ς τ :=
  ExOptic.toProfOptic (ExLens.mk get set)



def ExPrism (α β ς τ) := ExOptic Trivial (· -> ·) Sum Trivial (· -> ·) Sum Sum α β ς τ

def ExPrism.mk
  (match_ : ς -> τ ⊕ α)
  (build : β -> τ)
  : ExPrism α β ς τ
  := ExOptic.mk match_ (Sum.elim id build)

def Prism (α β ς τ) := ProfOptic Trivial (· -> ·) Sum Trivial (· -> ·) Sum Sum α β ς τ

abbrev Prism' (α ς) := Prism α α ς ς

def Prism.mk
  (match_ : ς -> τ ⊕ α)
  (build : β -> τ)
  : Prism α β ς τ := ExOptic.toProfOptic (ExPrism.mk match_ build)

def ExTraversal (α β ς τ) := ExOptic Traversable NatTsfm (· ∘ ·) Trivial (· -> ·) (· ·) (· ·) α β ς τ

def Traversal (α β ς τ) := ProfOptic Traversable NatTsfm (· ∘ ·) Trivial (· -> ·) (· ·) (· ·) α β ς τ

abbrev Traversal' (α ς) := Traversal α α ς ς

def ExTraversal.mk [Traversable F]  (f : ς -> F α) (g : F β -> τ) : ExTraversal α β ς τ  :=
  ExOptic.mk f g

def Split ς α := List α × ς

instance : Functor (Split ς) where
  map := fun f (l, s) => (l.map f, s)

instance : Traversable (Split.{u, u} ς) where
  traverse := fun f (l, s) => fmap (flip Prod.mk s) (traverse f l)

def Traversal.mk
  (f : ς -> List α × (List β -> τ))
  : Traversal α β ς τ
  := ExOptic.toProfOptic (ExTraversal.mk (F := Split ς) (fun s => (f s |>.fst, s)) (fun (l, s) => f s |>.snd l))



