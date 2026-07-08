import Mathlib.Data.Nat.Lattice
import Mathlib.Order.WellFounded

theorem acc_iff_forall_rel_acc 
  {rel : α -> α -> Prop}
  {a : α}
  : Acc rel a <-> ∀a', rel a' a -> Acc rel a' := by
    constructor
    · intro h a' h'
      cases h; grind
    · intro h
      constructor; grind

@[grind]
def CloserToBoundThan (bound a b : Nat) : Prop :=
  a ≤ bound ∧ bound - a < bound - b

instance : DecidableRel (CloserToBoundThan bound) := by
  unfold DecidableRel CloserToBoundThan
  infer_instance
      
theorem CloserToBoundThan_wellfounded
  : WellFounded (CloserToBoundThan bound) := by
    constructor
    intro a
    if a < bound
    then
      rw [(by grind : a = bound - (bound - a))]
      induction bound - a <;> grind [Acc]
    else grind [Acc]













