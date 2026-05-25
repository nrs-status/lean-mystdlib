import Mystdlib.DFinVec

def TypeList.{u} := {l : List (Type u) // ¬ l.isEmpty }

namespace TypeList

@[grind =_]
theorem eta
  {l : TypeList.{u}}
  : l = ⟨l.val, l.property⟩ := by
    unfold TypeList at l
    grind

@[simp, grind .]
theorem never_empty
  {l : TypeList.{u}}
  : l.val.isEmpty -> False := by
    simp [l.property]

@[grind]
def length (l : TypeList.{u}) := l.val.length

def head (l : TypeList.{u}) : Type u :=
  l.val.head (by grind)

def tail (l : TypeList.{u}) (h : 1 < l.length) : TypeList.{u} :=
  ⟨l.val.tail, by rw [List.isEmpty_iff_length_eq_zero]; grind⟩

def cons (α : Type u) (l : TypeList.{u}) : TypeList.{u} :=
  ⟨α :: l.val, by grind⟩

def concat (l : TypeList.{u}) (α : Type u) : TypeList.{u} :=
  ⟨l.val.concat α, by simp⟩

def dropLast (l : TypeList.{u}) (h : 1 < l.length) : TypeList.{u} := .mk
  l.val.dropLast <| by
    simp [length] at h
    rw [List.isEmpty_iff_length_eq_zero]
    grind

def getLast (l : TypeList.{u}) : Type u :=
  l.val.getLast (by grind [l.property])

def get (l : TypeList.{u}) (idx : Fin l.length) : Type u :=
  l.val.get idx

def ofList (l : List (Type u)) (h : ¬ l.isEmpty := by grind) : TypeList.{u} := 
  ⟨l, h⟩

@[grind .]
theorem cons_eq_cons
  {l : TypeList.{u}}
  {α : Type u}
  : cons α l = ⟨α :: l.val, by grind⟩ := by
    simp [cons]

@[grind .]
theorem length_decreasing 
  {l : TypeList.{u}}
  : l.length < (cons α l).length := by
    simp [length, cons]

@[simp, grind .]
theorem getLast_singleton_eq_elm
  {α : Type u}
  : getLast ⟨[α], by grind⟩ = α := rfl

instance : Singleton (Type u) TypeList.{u} where
  singleton := fun α => ⟨[α], by grind⟩

@[simp, grind =]
theorem singleton_def 
  {α : Type u}
  : ({α} : TypeList.{u}) = (⟨[α], by grind⟩ : TypeList.{u}) := rfl

@[induction_eliminator]
def ind 
  {motive : TypeList.{u} -> Sort v}
  (singleton : (α : Type u) -> motive {α})
  (cons : (α : Type u) -> (tail : TypeList.{u}) -> motive tail -> motive (cons α tail))
  (l)
  : motive l := 
  let ⟨α :: l', p⟩ := l
  match l' with
  | .nil => singleton α
  | .cons β l'' => by
    have := ind singleton cons ⟨β :: l'', by grind⟩
    have thisa := cons_eq_cons (α := α) (l := ⟨β :: l'', by grind⟩)
    rw [<- thisa]
    exact cons _ _ this
termination_by l.length
decreasing_by grind



@[grind .]
theorem dropLast_shift
  : dropLast ⟨α :: β :: l, by grind⟩ h = if l.isEmpty then {α} else (cons α ⟨β :: l, by grind⟩).dropLast (by grind) := by
    split; simp [Singleton.singleton, dropLast]; grind
    simp [dropLast, cons]

macro_rules
| `(tactic|decreasing_trivial) => `(tactic|grind)

def toProdType (typs : TypeList.{u}) : Type u :=
  let ⟨t :: ts, _⟩ := typs
  if h : ts.isEmpty then t else t × toProdType ⟨ts, h⟩
termination_by typs.length

def toFunType (typs : TypeList.{u}) : Type u :=
  let ⟨t :: ts, _⟩ := typs
  if h : ts.isEmpty then t else t -> toFunType ⟨ts, h⟩
termination_by typs.length

@[simp]
theorem toFunType_singleton
  : toFunType {α} = α := by
    simp [toFunType]

@[simp]
theorem toFunType_cons
  : toFunType (cons α typs) = (α -> toFunType typs) := by
    rw [cons, toFunType]
    grind

@[simp]
theorem toFunType_two
  : toFunType (cons α {β}) = (α -> β) := by
    simp [toFunType]

@[simp, grind =]
theorem toProdType_singleton
  : toProdType {α} = α := by
    simp [toProdType]

theorem toProdType_cons
  : toProdType (cons α typs) = (α × toProdType typs) := by
    simp [cons]
    rw [toProdType]
    grind

def apply (typs : TypeList.{u}) (h : 1 < typs.length) 
  : toFunType typs -> toProdType (typs.dropLast h) -> typs.getLast :=
  fun f x =>
    let ⟨t :: ts, _⟩ := typs
    let β :: tts := ts
    if h' : 1 < tts.length 
    then by
      have := apply ⟨β :: tts, by grind⟩ (by grind)
      simp [toFunType] at f
      simp [dropLast, toProdType] at x
      split at x
      · exfalso
        induction tts; grind; grind
      · split at f; grind
        rw [<- toFunType_cons] at f
        exact this (f x.fst) x.snd
    else
      have : tts.length < 2 := by grind
      match tts with
      | .nil => by 
        simp [toFunType] at f
        simp [getLast]
        simp [dropLast, toProdType] at x
        exact f x
      | .cons x' .nil => by
        simp [getLast]
        simp [toFunType] at f
        simp [dropLast, toProdType] at x
        exact f x.fst x.snd
termination_by typs.length

def toDFinVec (l : TypeList.{u}) := DFinVec l.length l.get

class OfTuple (l : List (Type u)) (n : outParam Nat) (prod : outParam (Type u)) where
  wf : n = l.length := by grind
  ofTuple : prod -> (i : Fin n) -> l[i]

instance : OfTuple [α] 1 α where
  ofTuple := fun a i => by simp; exact a

instance [inst : OfTuple l n ξ] : OfTuple (α :: l) n.succ (α × ξ) where
  wf := by cases inst; grind
  ofTuple := fun (a, e) ⟨n, _⟩ => match h : n with
  | 0 => a
  | .succ nn => by simp; exact inst.ofTuple e ⟨nn, by grind⟩

def toDFinVecFunType (l l' : TypeList.{u}) : Type u :=
  toFunType (l.concat l'.toDFinVec)
