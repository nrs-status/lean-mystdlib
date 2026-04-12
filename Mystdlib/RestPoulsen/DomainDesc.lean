

structure DomainDesc.{o, m} : Type ((max o m) + 1) where
  obj : (T : Type) -> Type o
  hom {T} (V : T -> obj T) (X Y : obj T) : Type m
  id {T V} (X : obj T) : hom V X X
  comp {T V} {X Y Z : obj T} : hom V Y Z -> hom V X Y -> hom V X Z

open DomainDesc

namespace DomainDesc

structure Endo (C : DomainDesc.{o, m}) {T : Type} {V : T -> C.obj T} : Type ((max o m) + 1) where
  F₀ : C.obj T -> C.obj T
  F₁ {X Y : C.obj T} : C.hom V X Y -> C.hom V (F₀ X) (F₀ Y)

open Endo

class Monad {C : DomainDesc.{o, m}} {T V} (M : Endo C (T := T) (V := V))  : Type ((max o m) + 1) where
  η {X} : C.hom (T := T) V X (M.F₀ X)
  μ {X} : C.hom (T := T) V (M.F₀ (M.F₀ X)) (M.F₀ X)

open Monad

structure Cartesian (C : DomainDesc.{o, m}) : Type ((max o m) + 1) where
  top {X} : C.obj X
  prod {X} : C.obj X -> C.obj X -> C.obj X

open Cartesian

def Kleisli (C : DomainDesc.{o, m}) (M : {T : Type} -> (V : T -> C.obj T) -> Endo C) [inst : {T : _} -> {V : T -> C.obj T} -> Monad (V := V) (M V)] : DomainDesc.{o, m} where
  obj := C.obj
  hom := fun V X Y => C.hom V X ((M V).F₀ Y)
  -- id := fun X => inst.η (X := X)
  id := fun _ => Monad.η
  comp := fun g f => C.comp Monad.μ (C.comp ((M _).F₁ g) f)

variable
  (C : DomainDesc.{o, m})

structure Iso {T} (X Y : C.obj T) : Type ((max o m) + 1) where
  to {V} : C.hom V X Y
  inv {V} : C.hom V Y X

open Iso
