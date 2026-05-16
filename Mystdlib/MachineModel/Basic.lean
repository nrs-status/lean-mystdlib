import Mystdlib.MachineModel.Units

structure MachineSpec : Type where
  address_bitlen : BitLen
  nontrivial : 1 < address_bitlen.toNat := by simp_all

namespace MachineSpec

def Address (spec : MachineSpec) : Type :=
  BitVec spec.address_bitlen.toNat

def addressableMemBitLen (spec : MachineSpec) : BitLen :=
  ⟨2 ^ spec.address_bitlen.toNat⟩

def AddressableMem (spec : MachineSpec) : Type :=
  Vector spec.Address (spec.addressableMemBitLen.toNat)

def AddrPos (spec : MachineSpec) : Type :=
  Fin spec.addressableMemBitLen.toNat
  deriving BEq, LawfulBEq, DecidableEq, Repr

instance : LT (AddrPos spec) where
  lt := fun x y => x.toNat < y.toNat

instance : LE (AddrPos spec) where
  le := fun x y => x < y ∨ x = y

@[simp] 
theorem AddrPos.lt_eq : ∀ {x y : AddrPos spec}, (x < y) = (x.toNat < y.toNat) := rfl

@[simp] 
theorem AddrPos.le_eq : ∀ {x y : AddrPos spec}, (x ≤ y) = (x < y ∨ x = y) := rfl

def firstPos (spec : MachineSpec) : spec.AddrPos :=
  ⟨0, by simp [addressableMemBitLen]; grind⟩

def lastPos (spec : MachineSpec) : spec.AddrPos := 
  ⟨spec.addressableMemBitLen.toNat.pred, by simp_all [addressableMemBitLen]; grind⟩

def getAddrAtPos (xmem : AddressableMem spec) (pos : AddrPos spec) : spec.Address :=
  xmem.get pos

instance : Max (AddrPos spec) where
  max := fun x y => if x.val < y.val then y else x

instance : Min (AddrPos spec) where
  min := fun x y => if x.val < y.val then x else y

instance : Std.IsPreorder (AddrPos spec) where
  le_refl := by simp
  le_trans := by simp; grind

instance : Std.IsPartialOrder (AddrPos spec) where
  le_antisymm := by simp; grind

instance : Std.IsLinearPreorder (AddrPos spec) where
  le_total := by simp; grind

instance : Std.IsLinearOrder (AddrPos spec) where

instance : Std.LawfulOrderMax (AddrPos spec) where
  max_eq_or := by simp [Max.max]; grind
  max_le_iff := by simp [Max.max]; grind

instance : Std.LawfulOrderMin (AddrPos spec) where
  min_eq_or := by simp [Min.min]; grind
  le_min_iff := by simp [Min.min]; grind

instance : Std.MinEqOr (AddrPos spec) where
  min_eq_or := by simp [Min.min]; grind

instance : DecidableLT (AddrPos spec) := by
  unfold DecidableLT DecidableRel
  intro a b
  have : ∀n m : Nat, Decidable (n < m) := inferInstance
  apply this

instance : DecidableLE (AddrPos spec) := by
  unfold DecidableLE DecidableRel
  intro a b
  have : ∀n m : Nat, Decidable (n < m ∨ a = b) := inferInstance
  apply this

instance  : Std.LawfulOrderBEq (AddrPos spec) where
  beq_iff_le_and_ge := by
    intro a b; grind

      

