

class IsElm (l : List α) (a : α) where
  i : Fin l.length
  wf : List.get _ i = a := by grind

instance : IsElm [a] a where
  i := 0

instance [inst : IsElm l a] : IsElm (a' :: l) a where
  i := inst.i.succ
  wf := have := inst.wf; by simp_all

class IsEq (a a' : α) where
  eq : a = a'

class IsNotEq (a a' : α) where
  noteq : a ≠ a'

class IsListHead (l : List α) (a : α) where
  wf : l.head? = .some a

instance : IsListHead [a] a where
  wf := by grind

instance : IsEq a a where
  eq := rfl

instance [IsEq a' a] [IsListHead (a' :: xs) a] : IsListHead (a' :: a'' :: xs) a where
  wf := by simp; exact IsEq.eq

instance [inst : IsListHead l a] : IsElm l a where
  i := ⟨0, by have := inst.wf; grind⟩
  wf := have := inst.wf; by simp; have := List.head?_eq_getElem? (l := l); grind

class IsInListBody (l : List α) (a : α)  where
  [iselm : IsElm l a]
  wf : ¬ l.head? = Option.some a

instance [IsNotEq a a']  : IsInListBody (a :: a' :: xs) a' where
  iselm := ⟨1, by simp⟩
  wf := by simp; exact IsNotEq.noteq

instance [inst : IsInListBody l a] : IsElm l a := inst.iselm

instance [inst : IsNotEq a a'] : IsNotEq a' a where
  noteq := have := inst.noteq; by grind

instance [IsInListBody l a] [IsNotEq a a'] : IsInListBody (a' :: l) a where
  wf := by simp; exact IsNotEq.noteq

