
class Category (C₀ : Type _) (C₁ : outParam (C₀ -> C₀ -> Type _)) where
  id {X} : C₁ X X
  comp {X Y Z} : C₁ Y Z -> C₁ X Y -> C₁ X Z


class Bifunctor 
  (C₁ D₁ E₁)
  [Category C₀ C₁] 
  [Category D₀ D₁] 
  [Category E₀ E₁] 
  (F : C₀ -> D₀ -> E₀) where
  map {c₁ c₂ : C₀} {d₁ d₂ : D₀} : C₁ c₁ c₂ -> D₁ d₁ d₂ -> E₁ (F c₁ d₁) (F c₂ d₂) 


class Profunctor 
  [Category C₀ C₁] 
  [Category D₀ D₁] 
  (P : D₀ -> C₀ -> Type _) where
  map {d₂ d₁ : D₀} {c₁ c₂ : C₀}  : D₁ d₂ d₁ -> C₁ c₁ c₂ -> P d₁ c₁ -> P d₂ c₂


class IsoStruct 
  [Category C₀ C₁]
  (X Y : C₀) where
  hom : C₁ X Y
  inv : C₁ Y X


class MonoidalCat (C₀ : Type _) (C₁ : outParam (C₀ -> C₀ -> Type _)) [Category C₀ C₁] (tensorObj : C₀ -> C₀ -> C₀)
  where
    tensorUnit : C₀
    associator {X Y Z : C₀} : IsoStruct (tensorObj (tensorObj X Y) Z) (tensorObj X (tensorObj Y Z))
    leftUnitor {X : C₀} : IsoStruct (tensorObj tensorUnit X) X
    rightUnitor {X : C₀} : IsoStruct (tensorObj X tensorUnit) X 


class MonoidalAction
  [Category C₀ C₁] 
  [Category M₀ M₁]
  (O)
  [mon_cat_inst : MonoidalCat M₀ M₁ O]
  [Bifunctor _ _ _ O]
  (action : M₀ -> C₀ -> C₀)
  [Bifunctor _ _ _ action]
where
  unitor {X : C₀} : IsoStruct (action (MonoidalCat.tensorUnit O) X) X
  multiplicator {X : C₀} {P Q : M₀} : IsoStruct (action P (action Q X)) (action (O P Q) X)





