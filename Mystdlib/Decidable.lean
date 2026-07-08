

instance {α : Sort u} {p q : α -> Prop} [Decidable (∀k, p k -> q k)] [Decidable (∀k, q k -> p k)] : Decidable (∀k, p k <-> q k) := by
  if h : ∀k, p k -> q k
  then if h' : ∀k, q k -> p k 
    then apply Decidable.isTrue; grind
    else apply Decidable.isFalse; grind
  else apply Decidable.isFalse; grind
