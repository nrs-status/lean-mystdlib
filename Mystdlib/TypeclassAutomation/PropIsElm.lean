class IsElm (l : List α) (a : α) (i : outParam Nat) : Prop where
  i_wf : i < l.length := by grind
  wf : List.get _ ⟨i, i_wf⟩ = a := by grind

instance : IsElm [a] a 0 where

instance [inst : IsElm l a n] : IsElm (a' :: l) a n.succ where
  i_wf := by simp [inst.i_wf]
  wf := by grind [inst.wf]

class IsEq (a a' : α) : Prop where
  wf : a = a' := by simp

instance : IsEq a a where

instance [inst : IsEq a a'] : IsEq a' a where
  wf := by simp [inst.wf]

class IsNotEq (a a' : α) : Prop where
  wf : ¬ a = a' := by simp

instance [inst : IsNotEq a a'] : IsNotEq a' a where
  wf := by grind [inst.wf]

class IsListHead (l : List α) (a : α) : Prop where
  wf : l.head? = .some a := by grind

instance : IsListHead [a] a where

instance [inst : IsEq a a'] [IsListHead (a' :: xs) a] : IsListHead (a' :: a'' :: xs) a where
  wf := by simp [inst.wf]

instance {a : α} [inst : IsListHead l a] : IsElm l a 0 where
  i_wf := by grind [inst.wf]
  wf := have := inst.wf; by grind [List.head?_eq_getElem?]

class IsTailElm (head : α) (tail : List α) (tailelm : α) (head_plus_tail_pos : Fin tail.length.succ) : Prop where
  [iselm : IsElm (head :: tail) tailelm head_plus_tail_pos]
  wf : head ≠ tailelm

instance [IsNotEq a a'] : IsTailElm a (a' :: xs) a' 1 where
  iselm := ⟨by simp, by simp⟩
  wf := by simp [IsNotEq.wf]

instance [inst : IsTailElm head tail tailelm head_plus_tail_pos] [IsNotEq new_head tailelm] : IsTailElm new_head (head :: tail) tailelm head_plus_tail_pos.succ where
  iselm := ⟨by simp, have := inst.iselm.wf; by grind⟩
  wf := by simp_all [IsNotEq.wf]

