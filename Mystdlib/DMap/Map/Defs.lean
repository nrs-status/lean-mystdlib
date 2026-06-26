import Mystdlib.DMap.Defs

structure Map (α : Type u) [BEq α] (β : Type v) where
  inner : DMap α (fun (_ : α) => β)

namespace Map

variable {α : Type u} {β : Type v} [BEq α] 

def toList 
  (m : Map α β)
  : List (α × β) :=
  DMap.Const.toList m.inner

def keys (m : Map α β) : List α := 
  m.inner.keys


instance : EmptyCollection (Map α β) where
  emptyCollection := ⟨[], by simp⟩

@[grind]
def containsKey (a : α) (m : Map α β) : Bool := 
  m.inner.containsKey a


instance : Membership α (Map α β) where
  mem := fun m a => m.containsKey a

def insertEntryIfNew
  [PartialEquivBEq α]
  (k: α) (v : β) (m : Map α β) : Map α β :=
  ⟨m.inner.insertEntryIfNew k v⟩

def insertEntry [PartialEquivBEq α] (k : α) (v : β) (m : Map α β) : Map α β :=
  ⟨m.inner.insertEntry k v⟩

def length (m : Map α β) := m.inner.length

def getValueCast? [LawfulBEq α]  (a : α) (m : Map α β) : Option β :=
  m.inner.getValueCast? a

abbrev get? [LawfulBEq α]  (a : α) (m : Map α β) : Option β :=
  m.getValueCast? a

def getValueCast [LawfulBEq α]  (a : α) (m : Map α β) (h : a ∈ m) : β :=
  m.inner.getValueCast a (by simp_all [Membership.mem, containsKey])

abbrev get [LawfulBEq α] (m : Map α β) (a : α) (h : a ∈ m) : β :=
  m.getValueCast a h

def getValueCast! [LawfulBEq α] (a : α) [Inhabited β] (m : Map α β) : β :=
  m.inner.getValueCast! a

abbrev get! [LawfulBEq α] (a : α) [Inhabited β] (m : Map α β) : β :=
  m.getValueCast! a

def getEntry? (m : Map α β) (a : α) : Option (α × β) :=
  DMap.Const.getEntry? m.inner a

def getEntry (m : Map α β) (a : α) (h : a ∈ m) : α × β :=
  DMap.Const.getEntry m.inner a h


def modifyKey [LawfulBEq α] (k : α) (f : β -> β) (m : Map α β) : Map α β :=
  ⟨m.inner.modifyKey k f⟩


def replaceEntry [PartialEquivBEq α] (k : α) (v : β) (m : Map α β) : Map α β :=
  ⟨m.inner.replaceEntry k v⟩

def values (m : Map α β) : List β := 
  m.inner.values

def isEmpty (m : Map α β) : Prop :=
  m.inner.isEmpty

def head (m : Map α β) (h : ¬ m.isEmpty) : (_ : α) × β := 
  m.inner.head (by grind [isEmpty])

def tail [PartialEquivBEq α] (m : Map α β) : Map α β :=
  ⟨m.inner.tail⟩

def Equiv (m m' : Map α β) : Prop :=
  m.inner.Equiv m'.inner

def forM {m : Type w -> Type w'} [Monad m]  (f : α -> β -> m PUnit) (mp : Map α β) : m PUnit := mp.inner.forM f

def foldl (f : γ -> α -> β -> γ) (y : γ) (m : Map α β) : γ :=
  m.inner.foldl f y

def foldlM {m : Type w -> Type w'} [Monad m] (f : γ -> α -> β -> m γ) (y : γ) (mp : Map α β) : m γ :=
  mp.inner.foldl (fun xmy k v => do f (<- xmy) k v) (pure y)

def insertList
  [PartialEquivBEq α]
  (m : Map α β) (toInsert : List (α × β)) : Map α β :=
  ⟨DMap.Const.insertList m.inner toInsert⟩

def ofList
  [PartialEquivBEq α]
  (l : List (α × β)) : Map α β :=
  ⟨DMap.Const.ofList l⟩


def union
  [PartialEquivBEq α]
  (m m' : Map α β) : Map α β :=
  ⟨m.inner ∪ m'.inner⟩

instance [PartialEquivBEq α] : Union (Map α β) where
  union := union

def Disjoint (m m' : Map α β) : Prop :=
  m.inner.Disjoint m'.inner

def map {γ : Type w} (m : Map α β) (f : α -> β -> γ) : Map α γ :=
  ⟨m.inner.map f⟩

namespace Unit

def toList
  (m : Map α Unit) : List α :=
  DMap.Unit.toList m.inner

def distinctKeys
  (m : Map α Unit) :=
  DMap.Unit.distinctKeys m.inner

def insertListIfNew
  [PartialEquivBEq α]
  (m : Map α Unit) (l : List α)
  : Map α Unit :=
  ⟨DMap.Unit.insertListIfNew m.inner l⟩

def ofList
  [PartialEquivBEq α]
  (l : List α) : Map α Unit :=
  ⟨DMap.Unit.ofList l⟩

end Unit
