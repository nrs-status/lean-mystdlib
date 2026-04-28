import Mystdlib.Bazaar
import Mystdlib.Comonad

def Lens α ς := ς -> Store α ς

def Lens.get
  (x : Lens α ς)
  : ς -> α
  := fun s => x s |>.pos

def Lens.set
  (x : Lens α ς)
  : ς -> α -> ς 
  := fun s => x s |>.peek

def Lens.mk
  (get : ς -> α)
  (set : ς -> α -> ς)
  : Lens α ς
  := fun s => ⟨set s, get s⟩

-- multiplate: lens are coalgebras for the store comonad

def Lens.compose
  (x : Lens α ς)
  (y : Lens ς τ)
  : Lens α τ
  := fun t => let ⟨v, b⟩ := y t; Functor.map v (x b)

def Biplate (α ς : Type u) := ς -> Bazaar α α ς
-- the above is the definition of the argument used to construct a Traversal in the tambara representation
-- multiplate calls Bazaar "cartesian store comonad"


instance : Comonad (Bazaar α α) where
  extract := Bazaar.sold
  duplicate := fun b => ⟨b.length, b.elements, fun v => ⟨_, v, b.continuation⟩⟩

def iso_store_1
  (x : Store α ς)
  : (F : _) -> [Functor F] -> (α -> F α) -> F ς
  := fun F inst f => inst.map x.peek (f x.pos)

def iso_store_2
  (f : (F : _) -> [Functor F] -> (α -> F α) -> F ς)
  : Store α ς
  := f (Store α) (fun a => ⟨id, a⟩)

def iso_bazaar_1
  (x : Bazaar α α ς)
  : (F : _) -> [Applicative F] -> (α -> F α) -> F ς
  := fun _ _ f => Functor.map Bazaar.sold (traverse (t := (Bazaar · α ς)) f x)

def iso_bazaar_2
  (f : (F : _) -> [Applicative F] -> (α -> F α) -> F ς)
  : Bazaar α α ς
  := f (Bazaar α α) .sell

-- which implies: Biplate α ς iso to (F : _) -> [Applicative F] -> (α -> F α) -> ς -> F ς
-- this is the type of TraversalVL


