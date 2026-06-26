import Std.Data.Internal.List.Defs
import Std.Data.Internal.List.Associative
import Mystdlib.List.DistinctKeys

open Std Internal

structure DMap (α : Type u) [BEq α] (β : α -> Type v) where
  toList : List ((a : α) × β a)
  distinctKeys : toList.DistinctKeys

namespace DMap

variable {α : Type u} [BEq α] {β : α → Type v}  

instance : EmptyCollection (DMap α β) where
  emptyCollection := ⟨[], by simp⟩

def keys (m : DMap α β) : List α := 
  m.toList.keys

@[grind]
def containsKey (m : DMap α β) (a : α) : Bool := 
  List.containsKey a m.toList

instance : Membership α (DMap α β) where
  mem := fun m a => m.containsKey a

def insertEntryIfNew
  [PartialEquivBEq α]
  (k: α) (v : β k) (m : DMap α β) : DMap α β :=
  ⟨List.insertEntryIfNew k v m.toList, List.DistinctKeys.insertEntryIfNew m.distinctKeys⟩

def insertEntry [PartialEquivBEq α] (k : α) (v : β k) (m : DMap α β) : DMap α β :=
  ⟨List.insertEntry k v m.toList, List.DistinctKeys.insertEntry m.distinctKeys⟩

def length (m : DMap α β) := 
  m.toList.length

def getEntry? (m : DMap α β) (a : α) : Option ((a : α) × β a) :=
  m.toList.getEntry? a

def getEntry (m : DMap α β) (a : α) (h : a ∈ m) : (a : α) × β a :=
  m.toList.getEntry a (by simp_all [Membership.mem, containsKey])

def getValueCast? [LawfulBEq α]  (a : α) (m : DMap α β) : Option (β a) :=
  m.toList.getValueCast? a

abbrev get? [LawfulBEq α]  (a : α) (m : DMap α β) : Option (β a) :=
  m.getValueCast? a

def getValueCast [LawfulBEq α]  (a : α) (m : DMap α β) (h : a ∈ m) : β a :=
  m.toList.getValueCast a (by simp_all [Membership.mem, containsKey])

abbrev get [LawfulBEq α] (a : α) (m : DMap α β) (h : a ∈ m) : β a :=
  m.getValueCast a h


def getValueCast! [LawfulBEq α] (a : α) [Inhabited (β a)] (m : DMap α β) : β a :=
  m.toList.getValueCast! a

abbrev get! [LawfulBEq α] (a : α) [Inhabited (β a)] (m : DMap α β) : β a :=
  m.getValueCast! a

def modifyKey [LawfulBEq α] (k : α) (f : β k -> β k) (m : DMap α β) : DMap α β :=
  ⟨m.toList.modifyKey k f, List.DistinctKeys.modifyKey m.distinctKeys⟩

def replaceEntry [PartialEquivBEq α] (k : α) (v : β k) (m : DMap α β) : DMap α β :=
  ⟨m.toList.replaceEntry k v, List.DistinctKeys.replaceEntry m.distinctKeys⟩

def values {β : Type v} (m : DMap α (fun (_ : α) => β)) : List β := 
  m.toList.values

def isEmpty (m : DMap α β) : Prop :=
  m.toList.isEmpty


def head (m : DMap α β) (h : ¬ m.isEmpty) : (a : α) × β a := 
  m.toList.head (by grind [isEmpty])

def tail [PartialEquivBEq α] (m : DMap α β) : DMap α β :=
  .mk m.toList.tail <| by
    match m with
    | ⟨.nil, _⟩ => simp
    | ⟨.cons x xs, p⟩ => apply Std.Internal.List.DistinctKeys.tail p

def Equiv (m m' : DMap α β) : Prop :=
  m.toList.Perm m'.toList


def forM {m : Type w -> Type w'} [Monad m]  (f : (a : α) -> β a -> m PUnit) (mp : DMap α β) : m PUnit := mp.toList.forM (fun ⟨k, v⟩ => f k v)

def foldl (f : γ -> (a : α) -> β a -> γ) (y : γ) (m : DMap α β) : γ :=
  m.toList.foldl (fun y ⟨k, v⟩ => f y k v) y

def foldlM {m : Type w -> Type w'} [Monad m] (f : γ -> (a : α) -> β a -> m γ) (y : γ) (mp : DMap α β) : m γ :=
  mp.toList.foldl (fun xmy ⟨k, v⟩ => do f (<- xmy) k v) (pure y)

  

def insertList
  [PartialEquivBEq α]
  (m : DMap α β) (toInsert : List ((a : α) × β a)) : DMap α β :=
  ⟨List.insertList m.toList toInsert, List.DistinctKeys.insertList m.distinctKeys⟩

def insertListIfNew
  [PartialEquivBEq α]
  (m : DMap α β) (toInsert : List ((a : α) × β a)) : DMap α β :=
  ⟨List.insertListIfNew m.toList toInsert, List.DistinctKeys.insertListIfNew m.distinctKeys⟩

def union
  [PartialEquivBEq α]
  (m m' : DMap α β) : DMap α β :=
  m.insertList m'.toList

def reverse
  [PartialEquivBEq α]
  (m : DMap α β)
  : DMap α β :=
  ⟨m.toList.reverse, List.DistinctKeys.reverse m.distinctKeys⟩

def ofList
  [PartialEquivBEq α]
  (l : List ((a : α) × β a)) : DMap α β :=
  (insertList ∅ l).reverse

instance [PartialEquivBEq α] : Union (DMap α β) where
  union := union

def Disjoint (m m' : DMap α β) : Prop :=
  ∀x, x ∈ m -> ¬ x ∈ m'


def map {γ : α -> Type w} (m : DMap α β) (f : (a : α) -> β a -> γ a) : DMap α γ :=
  ⟨m.toList.map fun p => ⟨p.fst, f p.fst p.snd⟩, List.DistinctKeys.map m.distinctKeys⟩

end DMap

namespace DMap.Const

variable {α : Type u} [BEq α] {β : Type v}  

def toList
  (m : DMap α (fun (_ : α) => β)) : List (α × β) :=
  m.toList.map (fun ⟨a, b⟩ => (a, b))

def insertList
  [PartialEquivBEq α]
  (m : DMap α (fun (_ : α) => β)) (l : List (α × β)) : DMap α (fun (_ : α) => β) :=
  ⟨m.toList.insertListConst l, List.DistinctKeys.insertList m.distinctKeys⟩

def ofList
  [PartialEquivBEq α]
  (l : List (α × β)) : DMap α (fun (_ : α) => β) :=
  (DMap.Const.insertList ∅ l).reverse

def getEntry? (m : DMap α fun _ => β) (a : α) : Option (α × β) :=
  (m.getEntry? a).map fun x => (x.fst, x.snd)

def getEntry (m : DMap α fun _ => β) (a : α) (h : a ∈ m) : α × β :=
  let ⟨fst, snd⟩ := m.getEntry a h
  (fst, snd)


end DMap.Const

namespace DMap.Unit

variable {α : Type u} [BEq α]

def toList
  (m : DMap α (fun (_ : α) => Unit)) : List α :=
  (DMap.Const.toList m).map (fun (a, _) => a)

def distinctKeys
  (m : DMap α (fun (_ : α) => Unit)) : ((DMap.Unit.toList m).map (fun a => ⟨a, Unit.unit⟩)).DistinctKeys := by
    rw [List.DistinctKeys.def, toList, Const.toList, List.pairwise_map, List.pairwise_map]
    apply List.pairwise_fst_eq_false_map_toProd m.distinctKeys

def insertListIfNew
  [PartialEquivBEq α]
  (m : DMap α (fun (_ : α) => Unit)) (l : List α)
  : DMap α (fun (_ : α) => Unit) :=
  ⟨m.toList.insertListIfNewUnit l, Std.Internal.List.DistinctKeys.insertListIfNewUnit m.distinctKeys⟩

def ofList 
  [PartialEquivBEq α]
  (l : List α) : DMap α (fun (_ : α) => Unit) :=
  (DMap.Const.ofList (l.map fun a => (a, .unit)))

end DMap.Unit
