import Mystdlib.MachineModel.Basic
import Mathlib.Data.List.Basic
import Batteries.Data.List.Lemmas

open MachineSpec

namespace AddressableMem

structure Slice (xmem : AddressableMem spec) where
  upperInclusiveLimit : spec.AddrPos
  lowerInclusiveLimit : spec.AddrPos
  wf : lowerInclusiveLimit ≤ upperInclusiveLimit

@[simp]
def Slice.lowerWf {mem : AddressableMem spec} (x : Slice mem) := x.lowerInclusiveLimit.isLt

def toSlice (xmem : AddressableMem spec) : Slice xmem where
  upperInclusiveLimit := ⟨spec.addressableMemBitLen.toNat.pred, by simp [addressableMemBitLen]; grind⟩
  lowerInclusiveLimit := ⟨0, by simp [addressableMemBitLen]; grind⟩
  wf := by simp_all; grind

def Slice.range {mem : AddressableMem spec} (xslice : Slice mem) : List (spec.AddrPos) :=
  let finrange := List.finRange spec.addressableMemBitLen.toNat
  finrange.filter (fun x => xslice.lowerInclusiveLimit ≤ x ∧ x ≤ xslice.upperInclusiveLimit)

theorem Slice_range_llim_leq_mem
  {xslice : Slice mem}
  : x ∈ xslice.range -> xslice.lowerInclusiveLimit ≤ x := by
    intro ismem
    simp
    simp [Slice.range] at ismem
    grind

theorem Slice_range_mem_leq_ulim
  {xslice : Slice mem}
  : x ∈ xslice.range -> x ≤ xslice.upperInclusiveLimit := by
    intro ismem
    simp
    simp [Slice.range] at ismem
    grind

@[simp, grind! .]
theorem slice_range_not_empty
  {xslice : Slice mem}
  : ¬ xslice.range.isEmpty := by
    simp [Slice.range]
    exists xslice.lowerInclusiveLimit
    constructor
    · simp [List.finRange]; grind
    · simp
      intro h
      have := xslice.wf
      dsimp [LE.le] at this; grind

@[simp]
theorem slice_range_nodup
  {mem : AddressableMem spec}
  {x : Slice mem}
  : (Slice.range x).Nodup := by
    rw [Slice.range]
    grind [List.nodup_finRange]

variable {spec : MachineSpec} {mem : AddressableMem spec}

theorem slice_range_min_is_llim
  {xslice : Slice mem}
  : xslice.range.min (by grind) = xslice.lowerInclusiveLimit := by
  have thisa := List.le_min_iff (l := xslice.range) (x := xslice.lowerInclusiveLimit) (by grind)
  have : ∀b, b ∈ xslice.range -> xslice.lowerInclusiveLimit ≤ b := by
    intro b
    apply Slice_range_llim_leq_mem
  rw [<- thisa] at this
  have thisb : ∀b, b ∈ xslice.range -> xslice.range.min (by grind) ≤ b := by
    grind
  have thisc : xslice.range.min (by grind) ≤ xslice.lowerInclusiveLimit := by
    apply thisb
    simp [Slice.range]
    constructor
    · simp [List.finRange]; grind
    · have := xslice.wf
      simp_all
  grind

theorem slice_range_max_is_ulim
  {xslice : Slice mem}
  : xslice.range.max (by grind) = xslice.upperInclusiveLimit := by
    have thisa := List.max_le_iff (l := xslice.range) (x := xslice.upperInclusiveLimit) (by grind)
    have : ∀b, b ∈ xslice.range -> b ≤ xslice.upperInclusiveLimit := by
      intro b
      apply Slice_range_mem_leq_ulim
    rw [<- thisa] at this
    have thisb : ∀b, b ∈ xslice.range -> b ≤ xslice.range.max (by grind) := by
      grind
    have thisc : xslice.upperInclusiveLimit ≤ xslice.range.max (by grind) := by
      apply thisb
      simp [Slice.range]
      constructor
      · simp [List.finRange]; grind
      · have := xslice.wf
        simp_all
    grind

instance {mem : AddressableMem spec} : Membership (AddrPos spec) (Slice mem) where
  mem := fun xslice xpos => xpos ∈ xslice.range

def Slice.length {xmem : AddressableMem spec} (xslice : AddressableMem.Slice xmem) : Nat :=
  1 + xslice.upperInclusiveLimit.val - xslice.lowerInclusiveLimit.val

theorem length_leq_addressable
  {mem : AddressableMem spec}
  {x : Slice mem}
  : x.length ≤ spec.addressableMemBitLen.toNat := by
    simp [Slice.length]
    grind

theorem slice_length_1_iff_lims_eq
  : Slice.length x = 1 <-> x.upperInclusiveLimit = x.lowerInclusiveLimit := by
    simp [Slice.length]
    grind

def Slice.extendUpwardsBy 
  {xmem : AddressableMem spec}
  (xslice : AddressableMem.Slice xmem) 
  (n : Nat)  
  (h : xslice.upperInclusiveLimit.val + n < spec.addressableMemBitLen.toNat)
  : AddressableMem.Slice xmem where
  upperInclusiveLimit := ⟨xslice.upperInclusiveLimit.val + n, h⟩
  lowerInclusiveLimit := xslice.lowerInclusiveLimit
  wf := by have := xslice.wf; simp_all; grind

def Slice.extendUpwardsTo
  {mem : AddressableMem spec}
  (xslice : AddressableMem.Slice mem)
  (dest : spec.AddrPos)
  (h : xslice.upperInclusiveLimit.val ≤ dest.val)
  : Slice mem where
    upperInclusiveLimit := dest
    lowerInclusiveLimit := xslice.lowerInclusiveLimit
    wf := by cases xslice; simp_all; cases dest; simp_all; grind

def Slice.extendDownwardsBy
  (xslice : AddressableMem.Slice xmem)
  (n : Nat)
  (h : n < xslice.lowerInclusiveLimit.val)
  : AddressableMem.Slice xmem where
    upperInclusiveLimit := xslice.upperInclusiveLimit
    lowerInclusiveLimit := ⟨xslice.lowerInclusiveLimit.val - n, by grind⟩
    wf := by have := xslice.wf; simp_all; grind

def Slice.extendDownwardsTo
  {mem : AddressableMem spec}
  (xslice : AddressableMem.Slice mem)
  (dest : spec.AddrPos)
  (h : dest.val ≤ xslice.lowerInclusiveLimit.val)
  : Slice mem where
    upperInclusiveLimit := xslice.upperInclusiveLimit
    lowerInclusiveLimit := dest
    wf := by cases xslice; simp_all; cases dest; simp_all; grind

def Slice.retractTop
  (xslice : AddressableMem.Slice mem)
  (n : Nat)
  (h : xslice.lowerInclusiveLimit.val ≤ xslice.upperInclusiveLimit.val - n)
  : AddressableMem.Slice mem where
    upperInclusiveLimit := ⟨xslice.upperInclusiveLimit.val - n, by grind⟩
    lowerInclusiveLimit := xslice.lowerInclusiveLimit
    wf := by simp_all; grind

def Slice.retractBottom
  (xslice : AddressableMem.Slice mem)
  (n : Nat)
  (h : xslice.lowerInclusiveLimit.val + n ≤ xslice.upperInclusiveLimit.val)
  : AddressableMem.Slice mem where
    upperInclusiveLimit := xslice.upperInclusiveLimit
    lowerInclusiveLimit := ⟨xslice.lowerInclusiveLimit.val + n, by grind⟩
    wf := by simp_all; grind

structure Slice.Subslice (xslice yslice : AddressableMem.Slice xmem) : Prop where
  upperLimitLE : xslice.upperInclusiveLimit.val ≤ yslice.upperInclusiveLimit.val
  lowerLimitLE : yslice.lowerInclusiveLimit.val ≤ xslice.lowerInclusiveLimit.val

theorem subslice_trans {x y z : AddressableMem.Slice mem} : x.Subslice y ∧ y.Subslice z -> x.Subslice z :=
  fun ⟨h, h'⟩ => {
    upperLimitLE := have := And.intro h.upperLimitLE h'.upperLimitLE; by grind
    lowerLimitLE := have := And.intro h.lowerLimitLE h'.lowerLimitLE; by grind
  }

-- what kind of monotonicity property do we need to make a generic congr?
theorem subslice_extendUpwardsBy_congr
  {x y : AddressableMem.Slice mem}  {n hh hh'}
  (h : x.Subslice y)
  : (x.extendUpwardsBy n hh).Subslice (y.extendUpwardsBy n hh') where
    upperLimitLE := by simp [Slice.extendUpwardsBy]; cases h; grind
    lowerLimitLE := by simp [Slice.extendUpwardsBy]; cases h; grind

theorem subslice_extendDownwardsBy_congr
  {x y : AddressableMem.Slice mem} {n hh hh'}
  (h : x.Subslice y)
  : (x.extendDownwardsBy n hh).Subslice (y.extendDownwardsBy n hh') where
    upperLimitLE := by simp [Slice.extendDownwardsBy]; cases h; grind
    lowerLimitLE := by simp [Slice.extendDownwardsBy]; cases h; grind

theorem extend_downwards_subslice 
  {x : AddressableMem.Slice mem}
  {h}
  : x.Subslice (x.extendDownwardsBy n h) := by
    simp [Slice.extendDownwardsBy]
    constructor <;> simp

theorem extend_upwards_subslice
  {x : AddressableMem.Slice mem}
  {h}
  : x.Subslice (x.extendUpwardsBy n h) := by
    simp [Slice.extendUpwardsBy]
    constructor <;> simp

theorem retract_top_subslice
  {x : AddressableMem.Slice mem}
  {h}
  : (x.retractTop n h).Subslice x := by
    simp [Slice.retractTop]
    constructor <;> simp

theorem retract_bottom_subslice
  {x : AddressableMem.Slice mem} {h}
  : (x.retractBottom n h).Subslice x := by
    simp [Slice.retractBottom]
    constructor <;> simp

theorem subslice_implies_range_sublist
  : Slice.Subslice x y -> x.range.Sublist y.range := by
    intro h
    cases x; cases y; cases h; simp_all; expose_names
    simp [Slice.range]
    apply List.monotone_filter_right 
    intro a h
    simp_all
    grind


    

