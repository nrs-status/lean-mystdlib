

class Comonad ω [Functor ω] where
  extract : ω α -> α
  duplicate : ω α -> ω (ω α) := extend id
  extend : (ω α -> γ) -> ω α -> ω γ := fun f x => Functor.map f (duplicate x)


structure Store (α : Type u) (ς : Type v) where
  peek : α -> ς
  pos : α

instance : Functor (Store α) where
  map := fun f x => ⟨f ∘ x.peek, x.pos⟩

instance : Comonad (Store α) where
  extract := fun x => x.peek x.pos
  duplicate := fun x => ⟨fun b => ⟨x.peek, b⟩, x.pos⟩
