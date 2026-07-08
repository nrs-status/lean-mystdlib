import Std
import Mystdlib.DMap.Map.Defs


structure Map.Set (α : Type u) [BEq α] where
  inner : Map α Unit

namespace Map.Set

variable [BEq α]

def toList (m : Set α) : List α :=
  Map.Unit.toList m.inner

instance : EmptyCollection (Set α) where
  emptyCollection := ⟨∅⟩

instance : Singleton α (Set α) where
  singleton := fun x => ⟨{(x, .unit)}⟩

@[grind]
def containsKey (a : α) (m : Set α) : Bool := 
  m.inner.containsKey a

instance : Membership α (Set α) where
  mem := fun s a => s.containsKey a

def insertEntryIfNew
  [PartialEquivBEq α]
  (k : α) (m : Set α) : Set α :=
  ⟨m.inner.insertEntryIfNew k .unit⟩

def insertEntry [PartialEquivBEq α] (k : α) (m : Set α) : Set α :=
  ⟨m.inner.insertEntry k .unit⟩

def length (m : Set α) := 
  m.inner.length

def isEmpty (m : Set α) : Prop :=
  m.inner.isEmpty

def head (m : Set α) (h : ¬ m.isEmpty) : α := 
  (m.inner.head (by grind [isEmpty])).fst

def tail [PartialEquivBEq α] (m : Set α) : Set α :=
  ⟨m.inner.tail⟩

def Equiv (s s' : Set α) : Prop :=
  s.inner.Equiv s'.inner

def forM {m : Type w -> Type w'} [Monad m]  (f : α -> m PUnit) (s : Set α) : m PUnit :=
  s.inner.forM (fun a _ => f a)

def foldl (f : γ -> α -> γ) (y : γ) (s : Set α) : γ :=
  s.inner.foldl (fun y a _ => f y a) y

def foldlM {m : Type w -> Type w'} [Monad m] (f : γ -> α -> m γ) (y : γ) (s : Set α) : m γ :=
  s.inner.foldl (fun xmy a _ => do f (<- xmy) a) (pure y)

def insertListIfNew
  [PartialEquivBEq α]
  (m : Set α) (toInsert : List α) : Set α :=
  ⟨Map.Unit.insertListIfNew m.inner toInsert⟩

def ofList
  [PartialEquivBEq α]
  (l : List α) : Set α :=
  ⟨Map.Unit.ofList l⟩

def union
  [PartialEquivBEq α]
  (s s' : Set α) : Set α :=
  ⟨s.inner ∪ s'.inner⟩

instance [PartialEquivBEq α] : Union (Set α) where
  union := union

def Disjoint (s s' : Set α) : Prop :=
  s.inner.Disjoint s'.inner

def mapDedup  [BEq β] [PartialEquivBEq β] (s : Set α) (f : α -> β) : Set β :=
  insertListIfNew ∅ (s.toList.map f)

def replaceEntry [PartialEquivBEq α] (k : α) (s : Set α) : Set α :=
  ⟨s.inner.replaceEntry k .unit⟩

def filter (f : α -> Bool) (s : Set α) : Set α :=
  ⟨s.inner.filter fun a _ => f a⟩

def concatIfNew [PartialEquivBEq α] (s : Set α) (a : α) : Set α :=
  ⟨s.inner.concatIfNew (a, .unit)⟩

instance [Repr α] : Repr (Set α) where
  reprPrec := fun s _ => repr s.toList
