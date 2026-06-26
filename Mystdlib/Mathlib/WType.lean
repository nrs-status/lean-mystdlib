import Mystdlib.Mathlib.Encodable
import Mathlib.Data.W.Basic

namespace WType

def head {β : α -> Type u} : WType β -> α
| ⟨a, _⟩ => a

def tail {β : α -> Type u} : (w : WType β) -> β w.head -> WType β
| ⟨_, b⟩ => b

def Free (α : Type u) := WType fun x : α × Nat => Fin x.snd 

inductive NodewiseEq {α β} : @WType α β -> @WType α β -> Prop
| intro {a a' : α} {cont : β a -> @WType α β} {cont' : β a' -> @WType α β} : (h : a = a') -> (∀(ba : β a), NodewiseEq (cont ba) (cont' (h ▸ ba))) -> NodewiseEq ⟨a, cont⟩ ⟨a', cont'⟩


theorem ext
  {w w' : @WType α β}
  : w = w' <-> w.NodewiseEq w' := by
    constructor
    · intro h
      subst h
      induction w with | mk a f ih => ?_
      constructor <;> grind
    · intro h
      induction h with | intro eq hcont => ?_
      subst eq
      simp only [mk.injEq, heq_eq_eq, true_and]
      funext x
      grind

instance [Encodable α] : DecidableEq (WType.Free α) :=
  Encodable.decidableEqOfEncodable (WType fun (x : α × Nat) => Fin x.snd)





      
