
namespace IsElm

class IsElm (l : List α) (a : α) where
  wf : a ∈ l := by grind

instance : IsElm [a] a where

instance
  [IsElm as a]
  : IsElm (a' :: as) a where
    wf := by grind [IsElm.wf]

instance 
  [IsElm (a :: as) a]
  : IsElm (a' :: (a :: as)) a' where

/- abbrev myuniv := [("Nat", Nat), ("Bool", Bool)] -/
/- #synth IsElm myuniv ("Bool", Bool) -/
/- #synth IsElm [("Bool", Bool)] ("Bool", Bool) -/

/- #synth IsElm [0, 1, 2, 3, 4] 0 -/
/- #synth IsElm [0, 1, 2, 3, 4] 1 -/
/- #synth IsElm [0, 1, 2, 3, 4] 2 -/
/- #synth IsElm [0, 1, 2, 3, 4] 3 -/

namespace Indexed

class IsElm (l : List α) (a : α) where
  i : Fin l.length
  wf : List.get _ i = a := by grind

instance : IsElm [a] a where
  i := 0

instance
  [inst : IsElm as a]
  : IsElm (a' :: as) a where
    i := inst.i.succ
    wf := have := inst.wf; by grind

instance 
  [IsElm (a :: as) a]
  : IsElm (a' :: (a :: as)) a' where
    i := 0
    wf := by grind


/- #synth IsElm [0, 1, 2, 3, 4] 0 -/
/- #synth IsElm [0, 1, 2, 3, 4] 1 -/
/- #synth IsElm [0, 1, 2, 3, 4] 2 -/
/- #synth IsElm [0, 1, 2, 3, 4] 3 -/

end Indexed

namespace IndexedProp

class IsElm (l : List α) (a : α) (i : outParam (Fin l.length)) : Prop where
  wf : List.get _ i = a := by grind

instance : IsElm [a] a 0 where

instance 
  [inst : IsElm as a i]
  : IsElm (a' :: as) a i.succ where
    wf := have := inst.wf; by grind

instance 
  [IsElm (a :: as) a i]
  : IsElm (a' :: (a :: as)) a' 0 where
