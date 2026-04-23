import Mathlib.Control.Bifunctor

namespace Tamb

class Category (C₀ : Type _) (C₁ : C₀ -> C₀ -> Type _) where
  id {X} : C₁ X X
  comp {X Y Z} : C₁ Y Z -> C₁ X Y -> C₁ X Z

instance : Category (Type u) (· -> ·) where
  id := id
  comp := Function.comp

class Bifunctor 
  (C₁ D₁ E₁)
  [Category C₀ C₁] 
  [Category D₀ D₁] 
  [Category E₀ E₁] 
  (F : C₀ -> D₀ -> E₀) where
  map {c₁ c₂ : C₀} {d₁ d₂ : D₀} : C₁ c₁ c₂ -> D₁ d₁ d₂ -> E₁ (F c₁ d₁) (F c₂ d₂) 

instance 
  [inst : Bifunctor (· -> ·) (· -> ·) (· -> ·) f]
  : _root_.Bifunctor f where
    bimap := inst.map

class IsoStruct 
  [Category C₀ C₁]
  (X Y : C₀) where
  hom : C₁ X Y
  inv : C₁ Y X


class MonoidalCat (C₀ : Type _) (C₁ : C₀ -> C₀ -> Type _) [Category C₀ C₁] (tensorObj : C₀ -> C₀ -> C₀)
  where
    tensorUnit : C₀
    associator {X Y Z : C₀} : IsoStruct (C₁ := C₁) (tensorObj (tensorObj X Y) Z) (tensorObj X (tensorObj Y Z))
    leftUnitor {X : C₀} : IsoStruct (C₁ := C₁) (tensorObj tensorUnit X) X
    rightUnitor {X : C₀} : IsoStruct (C₁ := C₁) (tensorObj X tensorUnit) X 


abbrev ActionBifunctor  
  (M₁ O)
  [Category M₀ M₁]
  [MonoidalCat M₀ M₁ O]
  (P)
  := Bifunctor M₁ (· -> ·) (· -> ·) P


class MonoidalAction
  (M₁ O)
  [Category M₀ M₁]
  [mon_cat_inst : MonoidalCat M₀ M₁ O]
  [Bifunctor M₁ M₁ M₁ O]
  (action : M₀ -> Type u -> Type u)
  extends ActionBifunctor M₁ O action
where
  unitor {X : Type u} : IsoStruct (C₁ := (· -> ·)) (action (MonoidalCat.tensorUnit M₁ O) X) X
  multiplicator {X : Type u} {P Q : M₀} : IsoStruct (C₁ := (· -> ·)) (action P (action Q X)) (action (O P Q) X)

structure ActionPair (M₀ : Type u) where
  left : M₀ -> Type v -> Type v
  right : M₀ -> Type v -> Type v

class MonoidalActionPair (pair : ActionPair M₀) (M₁ O) where
  [cat : Category M₀ M₁]
  [moncat : MonoidalCat M₀ M₁ O]
  [tensorObj_bif : Bifunctor M₁ M₁ M₁ O]
  [left_ax : MonoidalAction M₁ O pair.left]
  [right_ax : MonoidalAction M₁ O pair.right]


instance 
  [Category M₀ M₁]
  [Bifunctor M₁ M₁ M₁ O]
  [MonoidalCat M₀ M₁ O]
  [left_ax : MonoidalAction M₁ O left]
  [right_ax : MonoidalAction M₁ O right]
  : MonoidalActionPair ⟨left, right⟩ M₁ O where




