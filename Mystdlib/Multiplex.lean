

-- misc

inductive MultiplexStore (src : Type u) : List (Type u) -> Type _
| init : (src -> α) -> MultiplexStore src [α]
| extend : (src -> β) -> MultiplexStore src l -> MultiplexStore src (.cons β l)

abbrev TypeList.toProd (head : Type u) (tail : List (Type u)) :=
  match tail with
  | .nil => head
  | .cons x xs => head × (TypeList.toProd x xs)

def MultiplexStore.consume
  (store : MultiplexStore src (.cons α l))
  (a : src)
  : TypeList.toProd α l
  := match l, store with
  | .nil, .init f => f a
  | .cons .., .extend f store' =>
    (f a, store'.consume a)


-- main

abbrev genMultiplexType
  (src : Type u)
  (target : Type u)
  (todo : List (Type u))
  := match todo with
  | .nil => src -> target
  | .cons t ts => (src -> t) -> genMultiplexType src target ts

class Multiplex (src : Type u) (target : Type u) (l : outParam (List (Type u))) where
  multiplex : genMultiplexType src target l

instance : Multiplex src target [target] where
  multiplex := id

def instMultiplexProdCons_aux 
  (l)
  (x : genMultiplexType ς target l)
  (g : ς -> γ)
  : genMultiplexType ς (γ × target) l
  := match l with
  | .nil => fun s => (g s, x s)
  | .cons _ ts => fun f => instMultiplexProdCons_aux ts (x f) g

instance
  [inst : Multiplex src target l]
  : Multiplex src (γ × target) (.cons γ l) where
    multiplex := fun f => instMultiplexProdCons_aux _ inst.multiplex f

/-
Multiplex works but does not manage to infer the instance without an explicit target annotation

def myterm : Nat -> Nat × Nat := @Multiplex.multiplex Nat (Nat × Nat) _ _ _ _
def xxmyterm : Nat -> Nat × Nat := Multiplex.multiplex (target := Nat × Nat) _ _


what follows are various attempts at helping Multiplex unify. the main problem is, if the goal has the form
ς -> ξ
where ξ is some product type, there is no way for Multiplex.multiplex to unify `genMultiplexType` with it. genUncurriedMultiplexType fixes the issue by making the unification goal be μ -> ς -> ξ, where μ is an application of TypeList.toProd. I then try to lift genMultiplexType to the typeclass system
-/


abbrev genUncurriedMultiplexType
  (src : Type u)
  (target : Type u)
  (head : Type u)
  (tail : List (Type u))
  := TypeList.toProd head tail -> src -> target

class NoCurryMultiplex (src : Type u) (target : Type u) (head : outParam (Type u)) (tail : outParam (List (Type u))) where
  multiplex : genUncurriedMultiplexType src target head tail

instance : NoCurryMultiplex α β (α -> β) .nil where
  multiplex := id

instance 
  [inst : NoCurryMultiplex src target head l]
  : NoCurryMultiplex src (γ × target) (src -> γ) (.cons head l)
  where
    multiplex := fun x y => (x.fst y, inst.multiplex x.snd y)


-- lifting genMultiplexType to the typeclass system

namespace Lifted

class TypelistToArrow (elms : List (Type u)) (arrow : outParam (Type u)) where

abbrev typelistToArrow (elms : List (Type u)) [TypelistToArrow elms arrow] := arrow

instance {α β : Type u} : TypelistToArrow [α, β] (α -> β) where

instance
  {α β ξ γ δ: Type u}
  [TypelistToArrow (.cons (α -> β) l) ((α -> β) -> ξ)]
  : TypelistToArrow (.cons (γ -> δ) (.cons (α -> β) l)) ((γ -> δ) -> (α -> β) -> ξ) where


abbrev reverse_abbrev_aux (acc : List α) : List α -> List α 
| .nil => acc
| .cons x xs => reverse_abbrev_aux (x :: acc) xs

abbrev _root_.List.reverse_abbrev (l : List α) := reverse_abbrev_aux [] l

class GenTypelist (src target : Type u) (elms : outParam (List (Type u))) where

abbrev genTypelist (src target : Type u) [GenTypelist src target elms] := elms

instance : GenTypelist ς ξ [ς -> ξ] where

instance 
  [GenTypelist src ξ l]
  : GenTypelist src (α × ξ) (.cons (src -> α) l) where 

class GenMultiplexType (src target : Type u) (arrow : outParam (Type u)) where
  multiplex : arrow

abbrev genMultiplexType (src target : Type u) [GenMultiplexType src target arrow] := arrow

instance 
  : GenMultiplexType src target ((src -> target) -> src -> target) where
    multiplex := id

abbrev _root_.List.droplast_abbrev : List α -> List α
| .nil => .nil
| .cons _ .nil => .nil
| .cons x xs => .cons x (List.droplast_abbrev xs)


abbrev _root_.List.replacelast_abbrev (a : α) : List α -> List α
| .nil => .nil
| .cons _ .nil => .cons a .nil
| .cons x xs => .cons x (List.replacelast_abbrev a xs)

abbrev _root_.List.snoc_abbrev (a : α) : List α -> List α
| .nil => .cons a .nil
| .cons x xs => .cons x (List.snoc_abbrev a xs)


abbrev genArrowExtension
  (src target γ : Type u)
  [GenTypelist src target l]
  [TypelistToArrow (l.snoc_abbrev (src -> γ × target)) arrow']
  := (src -> γ) -> arrow'

class ArrowExtension (src target γ prev : Type u) (new : outParam (Type u)) where
  wf1 : prev = genMultiplexType src target
  wf2 : new = genArrowExtension src target γ

instance  : ArrowExtension src target γ (genMultiplexType src target) (genArrowExtension src target γ) where
  wf1 := rfl
  wf2 := rfl

class ArrowToTypelist (arrow : Type u) (l : outParam (List (Type u))) where

instance : ArrowToTypelist (α -> β) [α, β] where

instance
  [ArrowToTypelist ξ l]
  : ArrowToTypelist (α -> ξ) (α :: l) where

instance 
  [inst : GenMultiplexType src target arrow]
  [ext : ArrowExtension src target γ arrow arrow']
  : GenMultiplexType src (γ × target) arrow' where
    multiplex := by 
      have wfa := ext.wf1
      have wfb := ext.wf2
      subst wfa
      subst wfb
      exact fun f g x => (f x, g x)

