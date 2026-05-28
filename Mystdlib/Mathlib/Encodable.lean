import Mathlib.Data.FinEnum
import Mathlib.Logic.Equiv.Array

instance [inst : FinEnum α] : Encodable α where
  encode := fun x => inst.equiv.toFun x
  decode := fun n => if h : n < inst.card
  then inst.equiv.invFun ⟨n, by grind⟩
  else .none
  encodek := by intro x; split <;> simp_all

instance : Encodable ByteArray where
  encode := fun ⟨ar⟩ => Array.encodable.encode ar
  decode := fun n => (Array.encodable (α := UInt8)).decode n >>= fun ar => .some ⟨ar⟩
  encodek := by intro ar; simp

def string_equiv : Equiv String { x : ByteArray // x.IsValidUTF8 } where
  toFun := fun ⟨a, b⟩ => ⟨a, b⟩
  invFun := fun ⟨a, b⟩ => ⟨a, b⟩

instance : Encodable String := .ofEquiv _ string_equiv

instance [Encodable α] : Hashable α where
  hash := hash ∘ (inferInstance : Encodable α).encode

instance [inst : Encodable α] : Ord α where
  compare := fun x y => compare (inst.encode x) (inst.encode y)

instance [Encodable α] : Std.TransOrd α where
  eq_swap := by
    simp [compare, compareOfLessAndEq, Ordering.swap]
    grind
  isLE_trans := by
    simp [compare, compareOfLessAndEq, Ordering.isLE]
    grind
