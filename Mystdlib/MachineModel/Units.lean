import Mystdlib.Misc

structure BitLen where
  toNat : Nat
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq, Hashable, Inhabited, Ord

def BitVec.length (_ : BitVec n) : BitLen := ⟨n⟩

instance : HMod BitLen Nat Nat where
  hMod := fun ⟨x⟩ y => x.mod y

structure ByteLen where
  toNat : Nat
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq, Hashable, Inhabited, Ord

def BitLen.toByteLen (xbl : BitLen) (h : xbl % 8 = (0 : Nat)) : ByteLen := ⟨xbl.toNat / 8⟩

def BitLen.asByteLen (xbl : BitLen) : Float := xbl.toNat / 8

def ByteLen.toBitLen (xbyl : ByteLen) : BitLen := ⟨xbyl.toNat * 8⟩

def ByteLen.asKiB (xbyl : ByteLen) : Float := xbyl.toNat / 1024

def ByteLen.ofKiB (xkibs : Nat) : ByteLen := ⟨xkibs*1024⟩

def Byte := BitVec 8

def ByteVec (n : Nat) := Vector Byte n

def ByteVec.length (_ : ByteVec n) : ByteLen := ⟨n⟩

