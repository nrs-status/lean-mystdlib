

structure NEList (α : Type u) where
  toList : List α
  not_empty : ¬ toList.isEmpty := by grind

namespace NEList

instance : Membership α (NEList α) where
  mem := fun l a => a ∈ l.toList

instance : Singleton α (NEList α) where
  singleton := fun a => ⟨[a], by grind⟩

def cons (a : α) (l : NEList α) : NEList α where
  toList := .cons a l.toList
  not_empty := by grind

def head (l : NEList α) : α :=
  l.toList.head (by grind [NEList])

def length (l : NEList α) : Nat :=
  l.toList.length

@[elab_as_elim]
def rec'
  {motive : (l : NEList α) -> Sort u}
  (singleton : ∀x, motive {x})
  (cons : ∀(x : α) (l : NEList α), motive l -> motive (cons x l))
  (l : NEList α)
  : motive l :=
  match l with
  | ⟨[x], _⟩ => singleton x
  | ⟨x :: y :: xs, _⟩ => cons x ⟨y :: xs, by grind⟩ (rec' singleton cons ⟨y :: xs, by grind⟩)

def tail (l : NEList α) (h : 1 < l.length) : NEList α :=
  ⟨l.toList.tail, by grind [length, List.isEmpty_iff_length_eq_zero]⟩

def dropLast (l : NEList α) (h : 1 < l.length) : NEList α :=
  ⟨l.toList.dropLast, by grind [length, List.isEmpty_iff_length_eq_zero]⟩

def getLast (l : NEList α) : α :=
  l.toList.getLast (by grind [NEList])

def get! [Inhabited α] (l : NEList α) (n : Nat) : α :=
  l.toList[n]!

def get? (l : NEList α) (n : Nat) : Option α :=
  l.toList[n]?

def get (l : NEList α) (idx : Fin l.length) : α :=
  l.toList.get idx

instance : GetElem (NEList α) Nat α (fun l n => n < l.length) where
  getElem := fun l i h => l.get ⟨i, h⟩
  
instance : GetElem? (NEList α) Nat α (fun l n => n < l.length) where
  getElem? := fun l n => if h : n < l.length then .some l[n] else .none

def map (f : α -> β) (l : NEList α) : NEList β :=
  ⟨l.toList.map f, by cases l; simp_all⟩
