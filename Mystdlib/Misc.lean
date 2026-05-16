
instance [Inhabited x] : Inhabited (x ⊕ y) where
  default := .inl default

instance [Inhabited y] : Inhabited (x ⊕ y) where
  default := .inr default

def Option.orDflt [Inhabited α] : Option α -> α
| .some a => a
| .none => default

def Prod.assoc : α × β × γ -> (α × β) × γ :=
  fun (a, b, c) => ((a, b), c)

def Prod.assoc_inv : (α × β) × γ -> α × β × γ :=
  fun ((a, b), c) => (a, b, c)

def Sum.assoc : α ⊕ β ⊕ γ -> (α ⊕ β) ⊕ γ :=
  Sum.elim (.inl ∘ .inl) (Sum.elim (.inl ∘ .inr) .inr)

def Sum.assoc_inv : (α ⊕ β) ⊕ γ -> α ⊕ β ⊕ γ :=
  Sum.elim (Sum.elim .inl (.inr ∘ .inl)) (.inr ∘ .inr)


def Monad.join [Monad m] : m (m α) -> m α :=
  fun xm => do (<- xm)

instance : Monad List where
  pure := ([·])
  bind := fun l f => List.flatten (Functor.map f l)


def mapA_attaching {m : Type u → Type v} [Applicative m] {α : Type w} {β : Type u} (f : α → m β) : { l : List α // l.length = n } -> m { l : List β // l.length = n } :=
  fun ⟨l, p⟩ => match l with
  | []    => pure ⟨∅, by simp at p; simpa⟩
  | .cons a as => 
    Functor.map (fun b x => ⟨.cons b x.1, by grind⟩) (f a) <*> mapA_attaching f ⟨as, rfl⟩


instance : HDiv Nat Nat Float where
  hDiv := fun x y => x.toFloat / y.toFloat
