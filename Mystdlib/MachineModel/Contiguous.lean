import Mystdlib.MachineModel.Slice
import Batteries

open MachineSpec

open AddressableMem

def Slice.Contiguous
  (x y : Slice mem)
  : Prop :=
   x.upperInclusiveLimit.val.succ = y.lowerInclusiveLimit.val

instance {mem : AddressableMem spec} : Std.Irrefl (Slice.Contiguous (mem := mem)) where
  irrefl := by
    intro a
    simp [Slice.Contiguous]
    have := a.wf
    cases this <;> simp_all; grind

def stackOrderingIsSafe (stackAllocs : List (Slice mem)) : Prop :=
  stackAllocs.IsChain (flip (Slice.Contiguous (mem := mem)))



