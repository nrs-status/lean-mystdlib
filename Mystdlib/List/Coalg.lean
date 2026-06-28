
namespace List

inductive RecCoalg
  (c : α -> List α)
  : α -> Prop
  | intro x : (∀x' ∈ c x, RecCoalg c x') -> RecCoalg c x

namespace RecCoalg

def rel
  (c : α -> List α)
  : α -> α -> Prop :=
  fun a a' =>
    a ∈ c a' ∧ RecCoalg c a

theorem acc
  : ∀x, RecCoalg c x -> Acc (RecCoalg.rel c) x := by
    intro x H
    induction H; expose_names
    constructor
    intro y hrel
    obtain ⟨iselm, eq⟩ := hrel
    apply a_ih
    assumption

theorem wellfounded
  : WellFounded (RecCoalg.rel c) := by
    constructor
    intros
    constructor
    grind [acc, rel]

end List.RecCoalg


inductive AnaCoalg
  (p : β -> Bool)
  (c : β -> α × β)
  : β -> Prop -- boolean index indicates continuable
  | ptrue b : p b -> AnaCoalg p c b
  | pfalse b : ¬ p b -> AnaCoalg p c (Prod.snd (c b)) -> AnaCoalg p c b

namespace AnaCoalg 


def rel
  (p : β -> Bool)
  (c : β -> α × β)
  : β -> β -> Prop :=
  fun b b' =>
    if p b' then False
    else b = (c b').snd ∧ AnaCoalg p c b

theorem acc
  : ∀x, AnaCoalg p c x -> Acc (rel p c) x := by
    intro x H
    if h : p x
    then grind [Acc, rel]
    else induction H <;> grind [Acc, rel]

theorem wellfounded
  : WellFounded (rel p c) := by
    grind [WellFounded, Acc, acc, rel]

end AnaCoalg
  
def ana (p : β -> Bool) (c : β -> α × β) : (b : β) -> AnaCoalg p c b -> List α :=
  fun b H =>
    if h : p b
    then .nil
    else
      let (eq := h') (a, b') := c b
      a :: ana p c b' ?_
termination_by b => @AnaCoalg.wellfounded.wrap β (AnaCoalg.rel p c) b
decreasing_by
  simp [AnaCoalg.rel]
  grind [AnaCoalg]
where finally
  grind [AnaCoalg.rel, AnaCoalg]

def hylo (d : γ) (p : α -> Bool) (alg : β × γ -> γ) (coalg : α -> β × α) : (a : α) -> AnaCoalg p coalg a -> γ :=
  fun a H => if h : p a then d
  else
    let (eq := h') (b, a') := coalg a
    alg (b, hylo d p alg coalg a' ?_)
termination_by a => @AnaCoalg.wellfounded.wrap α (AnaCoalg.rel p coalg) a
decreasing_by
  simp [AnaCoalg.rel]
  grind [AnaCoalg]
where finally
  grind [AnaCoalg.rel, AnaCoalg]

def hyloFactorial (n : Nat) := 
  hylo 
    1 
    (fun n => n = 0) 
    (Function.uncurry Nat.mul) 
    (fun | .zero => (.zero, .zero) | .succ nn => (.succ nn, nn)) 
    n 
    (by induction n <;> grind [AnaCoalg])


