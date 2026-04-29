import Mystdlib.Optics.Tambara.Optics
import Mystdlib.Optics.Tambara.Combinators
import Mystdlib.Optics.Tambara.Tuple

open Tamb

class Cons (α β ς τ : Type u) where
  prism : Prism (α × ς) (β × τ) ς τ

class Cons' (α : outParam (Type u)) (ς : Type u) where
  prism : Prism (α × ς) (α × ς) ς ς

instance : Cons' α (List α) where
  prism := Prism.mk 
    (Function.uncurry List.cons)
    (fun | .cons a as => .inr (a, as) | .nil => .inl .nil)

instance : Cons' α (Array α) where
  prism := Prism.mk
    (fun (a, as) => #[a] ++ as)
    (fun ar => if h : ar.isEmpty then .inl #[] else .inr (ar[0]'(by grind), ar.drop 1))


def cons 
  {α ς : Type u}
  [inst : Cons' α ς] : α -> ς -> ς :=
  Function.curry inst.prism.review

def head
  {α ς : Type u}
  [inst : Cons' α ς]
  := inst.prism.compose (tuple' 0)

def head_affinetraversalb -- for educational purposes
  {α ς : Type u}
  [inst : Cons' α ς]
  : AffineTraversalb' α ς 
  := AffineTraversalb.mk
    (fun s => match inst.prism.matching s with
      | .inl x => .inl x
      | .inr x => .inr x.fst)
    (flip cons)

def tail
  {α ς : Type u}
  [inst : Cons' α ς]
  := inst.prism.compose (tuple' 1)

class Snoc (α β ς τ : Type u) where
  prism : Prism (ς × α) (τ × β) ς τ

class Snoc' (α : outParam (Type u)) (ς : Type u) where
  prism : Prism (ς × α) (ς × α) ς ς

instance : Snoc' α (List α) where
  prism := Prism.mk
    (fun (l, a) => l ++ [a])
    (fun l => if h : l.isEmpty then .inl l else .inr (l.dropLast, l.getLast (by grind)))

instance : Snoc' α (Array α) where
  prism := Prism.mk
    (fun (ar, a) => ar.push a)
    (fun ar => if h : ar.isEmpty then .inl ar else .inr (ar.pop, ar.back (by grind)))

def snoc [inst : Snoc' α ς] : ς -> α -> ς :=
  Function.curry inst.prism.review

def init
  [inst : Snoc' α ς]
  := inst.prism.compose (tuple' 0)

def last
  [inst : Snoc' α ς]
  := inst.prism.compose (tuple' 1)


