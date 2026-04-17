import Mystdlib.FunList

class Profunctor (p : Type u -> Type u -> Type u) where
  map : (ς -> α) -> (β -> τ) -> p α β -> p ς τ

class Contravariant (F : Type u -> Type v) where
  map : (β -> α) -> F α -> F β


instance 
  {p : Type u -> Type u -> Type u} 
  [h : {ξ : Type u} -> Contravariant (p · ξ)] 
  [q : {ξ : Type u} -> Functor (p ξ)]
  : Profunctor p where
    map := fun f g => (h.map f) ∘ (q.map g)

instance : Profunctor (· -> ·) where
  map := fun f g h => (g ∘ h) ∘ f

instance : Profunctor (fun _ x => x) where
  map := fun _ => id

instance {F : Type u -> Type u} [Functor F] : Profunctor (· -> F ·) where
  map := fun f g h => (Functor.map g ∘ h) ∘ f

instance {α : Type u} : Profunctor (fun (x _ : Type u) => x -> α) where
  map := fun f _ h => h ∘ f

instance {α : Type u} : Profunctor (fun (_ x : Type u) => α -> x) where
  map := fun _ g h => g ∘ h

class Cartesian (p : Type u -> Type u -> Type u) extends Profunctor p where
  first : p α β -> p (α × γ) (β × γ)
  second : p α β -> p (γ × α) (γ × β)

instance {α : Type u} : Cartesian (fun (x _ : Type u) => x -> α) where
  first := fun f x => f x.1
  second := fun f x => f x.2

instance {F : Type u -> Type u} [Functor F] : Cartesian (· -> F ·) where
  first := fun f x => fmap (·, x.2) (f x.1)
  second := fun f x => fmap (x.1, ·) (f x.2)
  

class Cocartesian (p : Type u -> Type u -> Type u) extends Profunctor p where
  left : p α β -> p (α ⊕ γ) (β ⊕ γ)
  right : p α β -> p (γ ⊕ α) (γ ⊕ β)

instance : Cocartesian (· -> ·) where
  left := fun f => Sum.elim (Sum.inl ∘ f) Sum.inr
  right := fun f => Sum.elim Sum.inl (Sum.inr ∘ f)

instance : Cocartesian (fun _ x => x) where
  left := Sum.inl
  right := Sum.inr

instance {F : Type u -> Type u} [Applicative F] : Cocartesian (· -> F ·) where
  left := fun f => Sum.elim (Functor.map Sum.inl ∘ f) (Functor.map Sum.inr ∘ pure)
  right := fun f => Sum.elim (Functor.map Sum.inl ∘ pure) (Functor.map Sum.inr ∘ f)

instance {α : Type u} : Cocartesian (fun (_ x : Type u) => α -> x) where
  left := fun f => Sum.inl ∘ f
  right := fun f => Sum.inr ∘ f

instance : Applicative (· ⊕ α) where
  pure := Sum.inl
  seq := fun f g => f.elim (g .unit |>.elim (fun a f => .inl (f a)) (fun a _ => .inr a)) Sum.inr

class Monoidal (p : Type u -> Type u -> Type u) extends Profunctor p where
  par : p α β -> p γ δ -> p (α × γ) (β × δ)
  unit : p PUnit PUnit

instance : Monoidal (· -> ·) where
  par := fun f g x => (f x.1, g x.2)
  unit := id

instance {F : Type u -> Type u} [Applicative F] : Monoidal (· -> F ·) where
  par := fun f g x =>
    (fmap Prod.mk (f x.1)) <*> g x.2
  unit := pure


@[reducible]
def Optic (p : Type u -> Type u -> Type u) (α β ς τ) := p α β -> p ς τ

@[reducible]
def Prism (α β ς τ) := {p : _} -> [Cocartesian p] -> Optic p α β ς τ

instance [Profunctor p] : Profunctor (Optic p α β) where
  map := fun f g h x => Profunctor.map f g (h x)

instance [Cocartesian p] : Cocartesian (Optic p α β) where
  left := fun f x => Cocartesian.left (f x)
  right := fun f x => Cocartesian.right (f x)

def Prism.on (xprism : Prism α β ς τ) (p : Type u -> Type u -> Type u) [Cocartesian p] : Optic p α β ς τ := xprism (p := p)

def Prism.mk
  (build : β -> τ)
  (matchfn : ς -> τ ⊕ α)
  : Prism α β ς τ
  := fun {_p inst} =>
    (inst.map matchfn (Sum.elim id build)) ∘ inst.right

def Prism.build
  (xprism : Prism α β ς τ)
  : β -> τ
  := xprism.on (fun _ x => x)

def Prism.matching
  (xprism : Prism α β ς τ)
  : ς -> τ ⊕ α
  :=
  xprism.on (· -> · ⊕ α) Sum.inr

def Prism.preview
  (xprism : Prism α β ς τ)
  : ς -> Option α
  := fun s => match xprism.matching s with
  | .inl _ => .none
  | .inr x => x

@[reducible]
def Lens (α β ς τ) := {p : _} -> [Cartesian p] -> Optic p α β ς τ

def Lens.on (xlens : Lens α β ς τ) (p) [Cartesian p] : Optic p α β ς τ :=
  xlens (p := p)

def Lens.mk
  (get : ς -> α)
  (set : ς -> β -> τ)
  : Lens α β ς τ
  := fun {_p inst} =>
    (inst.map (fun s => (s, get s)) (Function.uncurry set)) ∘ inst.second

def Lens.view
  (xlens : Lens α β ς τ)
  : ς -> α
  := xlens.on (fun x _ => x -> α) id


