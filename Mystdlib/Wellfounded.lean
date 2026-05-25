
theorem acc_iff_forall_rel_acc 
  {rel : α -> α -> Prop}
  {a : α}
  : Acc rel a <-> ∀a', rel a' a -> Acc rel a' := by
    constructor
    · intro h a' h'
      cases h; grind
    · intro h
      constructor; grind

