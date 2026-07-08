import Mathlib.Data.PFunctor.Univariate.Basic

inductive RecCoalg 
  {F : PFunctor.{uA, uB}} 
  {X : Type u} 
  (coalg : X -> F X) : X -> Prop
| fold x : (∀e, RecCoalg coalg ((coalg x).2 e)) -> RecCoalg coalg x

def RecCoalg.rel
  {F : PFunctor.{uA, uB}}
  {X : Type u} 
  (c : X -> F X)
  (x x' : X)
  : Prop :=
  ∃e, (c x').2 e = x ∧ RecCoalg c x

theorem RecCoalg.acc
  {F : PFunctor.{uA, uB}}
  {X : Type u} 
  (c : X -> F X)
  : ∀x, RecCoalg c x -> Acc (RecCoalg.rel c) x := by
    intro x H
    induction H; expose_names
    constructor
    intro y hrel
    obtain ⟨e, eq, H'⟩ := hrel
    subst eq
    apply a_ih

-- note : induction tactic doesn't tend to work well unless you either make the Acc declaration ∀x, P x -> Acc rel x or you generalize during the proof
theorem RecCoalg.rel.wellfounded
  {F : PFunctor.{uA, uB}}
  {X : Type u} 
  (c : X -> F X)
  : WellFounded (RecCoalg.rel c) := by
    constructor
    intro x
    constructor
    intro y hrel
    obtain ⟨e, eq, H⟩ := hrel
    apply RecCoalg.acc
    assumption

theorem RecCoalg.inv
  {F : PFunctor.{uA, uB}}
  {X : Type u} 
  (c : X -> F X)
  : ∀x, RecCoalg c x -> ∀e, RecCoalg c ((c x).2 e) :=
  fun x H =>
    match H with
    | .fold .(x) f => fun e => .fold _ (RecCoalg.inv c _ (f e))

def hylo
  {F : PFunctor.{uA, uB}} 
  (a : F B -> B)
  (c : A -> F A)
  : (x : A) -> RecCoalg c x -> B :=
  fun x H =>
    a ⟨(c x).fst, fun e => hylo a c ((c x).snd e) (H.inv c _ e)⟩
termination_by x => (RecCoalg.rel.wellfounded c).wrap x
decreasing_by
  simp [RecCoalg.rel]
  constructor
  · exists e
  · expose_names
    apply RecCoalg.inv
    assumption



