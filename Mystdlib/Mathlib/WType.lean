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

def decidableEq [DecidableEq α] [∀a, Fintype (β a)] : DecidableEq (@WType α β) := by
  rintro ⟨head, tail⟩ ⟨head', tail'⟩
  if head_eq : head = head'
  then
    if tails_eq : ∀i, (decidableEq (tail i) (tail' (head_eq ▸ i))).decide = true
    then
      apply Decidable.isTrue
      subst head_eq
      congr
      funext i
      grind
    else
      apply Decidable.isFalse
      simp only [decide_eq_true_eq, not_forall] at tails_eq
      subst head_eq
      grind
  else
    apply Decidable.isFalse
    grind
termination_by x => x.depth
decreasing_by
  all_goals (apply WType.depth_lt_depth_mk)

instance [DecidableEq α] [∀a, Fintype (β a)] : DecidableEq (@WType α β) := decidableEq

/- instance [Encodable α] : DecidableEq (WType.Free α) := -/
/-   Encodable.decidableEqOfEncodable (WType fun (x : α × Nat) => Fin x.snd) -/

