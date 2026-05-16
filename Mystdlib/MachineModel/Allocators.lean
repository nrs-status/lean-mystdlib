import Mystdlib.List
import Mystdlib.MachineModel.ProgramLayout
import Mystdlib.MachineModel.SliceOfExtremes

open MachineSpec AddressableMem ProgramLayout

structure ModelData (spec : MachineSpec) where
  mem : AddressableMem spec
  programLayout : ProgramLayout mem

variable {spec : MachineSpec} {mem : AddressableMem spec} {allocs : List (Slice mem)}

class ExtensibleBy {γ α : Type u} (size : γ -> Nat) (condition : γ -> α -> Prop) (extend : (y : γ) -> (a : α) -> condition y a -> γ) : Prop where
  extendExtends : ∀y a, (h : condition y a) -> size y < size (extend y a h)

structure ExtensionOfBy {γ α : Type u} (size : γ -> Nat) (condition : γ -> α -> Prop) (extend) [ExtensibleBy size condition extend] (new : γ) (prev : γ) (a : α)  : Prop where
  satisfy_cond : condition prev a
  is_extended : new = extend prev a satisfy_cond

class RetractableBy {γ α : Type u} (size : γ -> Nat) (condition : γ -> α -> Prop) (retract : (y : γ) -> (a : α) -> condition y a -> γ) : Prop where
  retractRetracts : ∀y a, (h : condition y a) -> size (retract y a h) < size y

structure Retraction {γ α} (size condition) (retract : (y : γ) -> (a : α) -> condition y a -> γ) [RetractableBy size condition retract] (prev : γ) (a : α) (new : γ) : Prop where
  satisfy_cond : condition prev a
  is_retracted : new = retract prev a satisfy_cond

structure AllocatorSpec (mem : AddressableMem spec) where
  sizedef : List (Slice mem) -> Nat
  allocation_cond : List (Slice mem) -> Slice mem -> Prop
  allocate : (allocations : List (Slice mem)) -> (allochion : Slice mem) -> allocation_cond allocations allochion -> List (Slice mem)
  allocates : ExtensibleBy sizedef allocation_cond allocate

def ExtensionOfByAllocator (allspec : AllocatorSpec mem) (allocs : List (Slice mem)) (prev_allocs : List (Slice mem)) (last_alloc : Slice mem) : Prop :=
  have := allspec.allocates
  ExtensionOfBy allspec.sizedef allspec.allocation_cond allspec.allocate allocs prev_allocs last_alloc

structure Allocator 
  (allspec : AllocatorSpec mem)
  where
    previous_allocations : List (Slice mem)
    last_allocation : Slice mem
    allocations : List (Slice mem)
    allocations_is_extension : ExtensionOfByAllocator allspec allocations previous_allocations last_allocation

def UnsafeBoundedHeapAllocatorSpec : AllocatorSpec mem where
  sizedef := List.length
  allocation_cond := fun l x => if h : l.isEmpty then False else minAddressPos l h ≤ x.lowerInclusiveLimit
  allocate := fun l x _ => l.cons x
  allocates := by constructor; grind

def CoveringHeapAllocator : AllocatorSpec mem where
  sizedef := fun l => if h : l.isEmpty then 0 else (sliceOfExtremes l h).length - (gapPositions l).length
  allocation_cond := fun l x => if h : l.isEmpty then False 
    else (gapPositions <| l.cons x).length < (gapPositions l).length
  allocate := fun l x _ => l.cons x
  allocates := sorry
    
    

    










