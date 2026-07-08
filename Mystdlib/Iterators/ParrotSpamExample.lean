import Std

open Std Iterators

structure Cycler (α : Type) where
  target : List α
  pos : Fin target.length

def Cycler.next (c : Cycler α) : α :=
  c.target[c.pos]

def Cycler.shift (c : Cycler α) : Cycler α :=
  if h : 1 < c.target.length
  then { c with pos := c.pos.add ⟨1, h⟩ }
  else c

instance [Pure m] : Iterator (Cycler α) m α where
  IsPlausibleStep it
  | .yield it' a =>
    a = it.internalState.next ∧ it'.internalState.next = it.internalState.shift.next
  | _ => False
  step it :=
    let a := it.internalState.next
    pure <| .deflate <| .yield { it with internalState := it.internalState.shift } a (by grind)

instance [Pure m] [Monad n] : IteratorLoop (Cycler α) m n :=
  .defaultImplementation

instance [Pure m] : Productive (Cycler α) m where
  wf := .intro <| fun _ => .intro _ nofun

def cyclerIter (l : List α) (h : 0 < l.length := by decide) : Iter (α := Cycler α) α :=
  Iter.mk ⟨l, ⟨0, by grind⟩⟩

def cyclerIterM (l : List α) (h : 0 < l.length := by decide) : IterM (α := Cycler α) m α :=
  IterM.mk ⟨l, ⟨0, by grind⟩⟩

/-- info: ["a", "b", "c", "a", "b", "c", "a", "b", "c", "a"] -/
#guard_msgs in
#eval Iter.take 10 (cyclerIter ["a", "b", "c"]) |>.toList

def mytake := IterM.takeWhileM 
  (fun _ => do return .up <| (<- get) ≤ 10) 
  <| (cyclerIterM ["a", "b", "c"]).mapM
    (m := StateM Nat)
    (n := StateM Nat) 
    fun s => do modify (· + s.length); return s

/-- info: (["a", "b", "c", "a", "b", "c", "a", "b", "c", "a"], 11) -/
#guard_msgs in
#eval mytake.toList 0

def myiter (l : List α) (h : 1 < l.length) :=
  let aux := Iter.repeat (· + ⟨1, by grind⟩) (⟨0, by grind⟩ : Fin l.length)
  aux.map (l[·])

/-- info: ["a", "b", "c", "a", "b"] -/
#guard_msgs in
#eval (myiter ["a", "b", "c"] (by decide)).take 5 |>.toList



