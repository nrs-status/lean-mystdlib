import Mystdlib.MachineModel.ProgramLayout
import Mystdlib.MachineModel.Contiguous

open MachineSpec AddressableMem ProgramLayout


structure ModelData (spec : MachineSpec) where
  mem : AddressableMem spec
  programLayout : ProgramLayout mem
  heapAllocs : List { x : Slice mem // x.Subslice programLayout.heapAllocableSlice }
  stackAllocs : List (Slice mem)

namespace MachineSpec.ModelData

def halloc
  (data : ModelData spec)
  (target : Slice data.mem)
  (h : target.Subslice data.programLayout.raw.heap)
  : ModelData spec :=
  { data with heapAllocs := data.heapAllocs.cons ⟨target, AddressableMem.subslice_trans ⟨h, heap_is_heapallocable⟩⟩ }

-- halloc! is less safe than halloc because the former extends the heap as needed
def halloc!_extendHeap
  (data : ModelData spec)
  (target : Slice data.mem)
  (h : target.Subslice data.programLayout.heapAllocableSlice)
  : ModelData spec := { 
    data with
    programLayout := data.programLayout.extendHeap (target.upperInclusiveLimit.val - data.programLayout.raw.heap.upperInclusiveLimit.val) (by grind)
    heapAllocs := data.heapAllocs.map fun ⟨val, p⟩ => .mk val <|
      AddressableMem.subslice_trans <| .intro p {
        upperLimitLE := by simp [heap_allocable_ulim_is_lastPos]
        lowerLimitLE := by simp [heap_allocable_llim_is_heap_llim, extendHeap, Raw.extendHeap, Slice.extendUpwardsBy]
      }
    }

--register the allocation after halloc!_extendHeap
def halloc!
  (data : ModelData spec)
  (target : Slice data.mem)
  (h : target.Subslice data.programLayout.heapAllocableSlice)
  : ModelData spec :=
    let extend_heap_and_cast_heapAllocs := halloc!_extendHeap data target h
    { extend_heap_and_cast_heapAllocs with heapAllocs := extend_heap_and_cast_heapAllocs.heapAllocs.cons <| .mk target <| 
        AddressableMem.subslice_trans <| .intro h {
          upperLimitLE := by simp [heap_allocable_ulim_is_lastPos]
          lowerLimitLE := by simp [heap_allocable_llim_is_heap_llim, extend_heap_and_cast_heapAllocs, halloc!_extendHeap, extendHeap, Raw.extendHeap, Slice.extendUpwardsBy]
        }
  }

-- push-alloc on stack
def salloc
  (data : ModelData spec)
  (push_size : Nat)
  (h : push_size < data.programLayout.raw.stack.lowerInclusiveLimit.val)
  (h' : push_size ≠ 0)
  : ModelData spec := { data with
    programLayout := data.programLayout.extendStack push_size h
    stackAllocs := data.stackAllocs.cons {
      upperInclusiveLimit := data.programLayout.raw.stack.upperInclusiveLimit
      lowerInclusiveLimit := ⟨data.programLayout.raw.stack.lowerInclusiveLimit.val - push_size, by grind⟩
      wf := by have := data.programLayout.raw.stack.wf; simp_all; grind
    }
  }

-- pop-free on stack

def sfree
  (data : ModelData spec)
  (h : ¬ data.stackAllocs.isEmpty)
  : ModelData spec := { data with
    programLayout := data.programLayout.retractStack (data.stackAllocs.head (by grind)).length sorry
  }

