import Mystdlib.MachineModel.Slice

open MachineSpec

open AddressableMem

namespace ProgramLayout

structure Raw (mem : AddressableMem spec)  where
  text : Slice mem
  data : Slice mem
  bss : Slice mem
  heap : Slice mem
  stack : Slice mem

def Raw.extendHeap 
  {mem : AddressableMem spec}
  (xraw : Raw mem) 
  (n : Nat) 
  (h : xraw.heap.upperInclusiveLimit.val + n < spec.addressableMemBitLen.toNat
) : Raw mem :=
  { xraw with heap := xraw.heap.extendUpwardsBy n h }

def Raw.retractHeap
  {mem : AddressableMem spec}
  (xraw : Raw mem)
  (n : Nat)
  (h : xraw.heap.lowerInclusiveLimit.val ≤ xraw.heap.upperInclusiveLimit.val - n)
  : Raw mem :=
  { xraw with heap := xraw.heap.retractTop n h }

def Raw.extendStack
  {mem : AddressableMem spec}
  (xraw : Raw mem)
  (n : Nat)
  (h : n < xraw.stack.lowerInclusiveLimit.val)
  : Raw mem :=
  { xraw with stack := xraw.stack.extendDownwardsBy n h }

def Raw.retractStack
  {mem : AddressableMem spec}
  (xraw : Raw mem)
  (n : Nat)
  (h : xraw.stack.lowerInclusiveLimit.val + n ≤ xraw.stack.upperInclusiveLimit.val)
  : Raw mem :=
  { xraw with stack := xraw.stack.retractBottom n h }

structure Raw.StaticsWF {mem : AddressableMem spec} (raw : Raw mem) : Prop where
  text_wrt_start : raw.text.lowerInclusiveLimit = spec.firstPos
  text_wrt_data : raw.data.lowerInclusiveLimit.val = raw.text.upperInclusiveLimit.succ
  data_wrt_bss : raw.bss.lowerInclusiveLimit.val = raw.data.upperInclusiveLimit.val.succ
  bss_wrt_heap : raw.heap.lowerInclusiveLimit.val = raw.bss.upperInclusiveLimit.val.succ
  stack_wrt_end : raw.stack.upperInclusiveLimit = spec.lastPos

structure _root_.ProgramLayout (mem : AddressableMem spec) where
  raw : Raw mem
  statics_wf : raw.StaticsWF

theorem layout_extendHeap_preserves_statics_wf
  {xpl : ProgramLayout mem} {n h}
  : (xpl.raw.extendHeap n h).StaticsWF := by
    simp [Raw.extendHeap, Slice.extendUpwardsBy]
    have := xpl.statics_wf.bss_wrt_heap
    exact { xpl.statics_wf with bss_wrt_heap := by grind }

theorem layout_retractHeap_preserves_statics_wf
  {xpl : ProgramLayout mem} {n h}
  : (xpl.raw.retractHeap n h).StaticsWF := by
    simp [Raw.retractHeap, Slice.retractTop]
    have := xpl.statics_wf.bss_wrt_heap
    exact { xpl.statics_wf with bss_wrt_heap := by grind }

theorem layout_extendStack_preserves_statics_wf
  {xpl : ProgramLayout mem} {n h}
  : (xpl.raw.extendStack n h).StaticsWF := by
    simp [Raw.extendStack, Slice.extendDownwardsBy]
    have := xpl.statics_wf.stack_wrt_end
    exact { xpl.statics_wf with stack_wrt_end := by grind }

theorem layout_retractStack_preserves_statics_wf
  {xpl : ProgramLayout mem} {n h}
  : (xpl.raw.retractStack n h).StaticsWF := by
    simp [Raw.retractStack, Slice.retractBottom]
    have := xpl.statics_wf.stack_wrt_end
    exact { xpl.statics_wf with stack_wrt_end := by grind }

def extendHeap 
  {mem : AddressableMem spec}
  (xpl : ProgramLayout mem) 
  (n : Nat) 
  (h : xpl.raw.heap.upperInclusiveLimit.val + n < spec.addressableMemBitLen.toNat)
  : ProgramLayout mem where
    raw := xpl.raw.extendHeap n h
    statics_wf := layout_extendHeap_preserves_statics_wf

def retractHeap
  {mem : AddressableMem spec}
  (xpl : ProgramLayout mem)
  (n : Nat)
  (h : xpl.raw.heap.lowerInclusiveLimit.val ≤ xpl.raw.heap.upperInclusiveLimit.val - n)
  : ProgramLayout mem where
    raw := xpl.raw.retractHeap n h
    statics_wf := layout_retractHeap_preserves_statics_wf

def extendStack
  {mem : AddressableMem spec}
  (xpl : ProgramLayout mem)
  (n : Nat)
  (h : n < xpl.raw.stack.lowerInclusiveLimit.val)
  : ProgramLayout mem where
    raw := xpl.raw.extendStack n h
    statics_wf := layout_extendStack_preserves_statics_wf

def retractStack
  {mem : AddressableMem spec}
  (xpl : ProgramLayout mem)
  (n : Nat)
  (h : xpl.raw.stack.lowerInclusiveLimit.val + n ≤ xpl.raw.stack.upperInclusiveLimit.val)
  : ProgramLayout mem where
    raw := xpl.raw.retractStack n h
    statics_wf := layout_retractStack_preserves_statics_wf

def heapAllocableSlice {mem : AddressableMem spec} (xpl : ProgramLayout mem) : Slice mem :=
  xpl.raw.heap.extendUpwardsBy (spec.lastPos.val - xpl.raw.heap.upperInclusiveLimit.val) (by simp [lastPos]; grind)

theorem heap_allocable_llim_is_heap_llim
  {xpl : ProgramLayout mem}
  : xpl.heapAllocableSlice.lowerInclusiveLimit = xpl.raw.heap.lowerInclusiveLimit := by
    simp [heapAllocableSlice, Slice.extendUpwardsBy]

theorem heap_allocable_ulim_is_lastPos
  {mem : AddressableMem spec}
  {xpl : ProgramLayout mem}
  : xpl.heapAllocableSlice.upperInclusiveLimit = spec.lastPos := by
    simp [heapAllocableSlice, lastPos, Slice.extendUpwardsBy]
    grind

end ProgramLayout

theorem heap_is_heapallocable {xpl : ProgramLayout mem} : xpl.raw.heap.Subslice xpl.heapAllocableSlice := by
  simp [ProgramLayout.heapAllocableSlice, extend_upwards_subslice]

