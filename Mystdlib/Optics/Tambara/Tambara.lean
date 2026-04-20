namespace Tambara

class Quiver (carrier : Type u) where
  obj : carrier -> Type v
  hom : carrier -> carrier -> Type v

class Obj (obj : α -> Type v) (x : α) where
  is_obj : obj x

class Category {carrier : Type u} (obj : carrier -> Type v) (hom : carrier -> carrier -> Type v) where
  id {X : carrier} [Obj obj X] : hom X X
  comp [Obj obj X] [Obj obj Y] [Obj obj Z] : hom Y Z -> hom X Y -> hom X Z

class Liftable 
  (obja : α -> Type u)
  (objb : β -> Type v)
  (objc : γ -> Type w)
  (F : α -> β -> γ)
  where
    lift [Obj obja x] [Obj objb y] : objc (F x y)

abbrev Liftable_aux (obja : α -> Type u) (objb : β -> Type v) (objc : γ -> Type w) (F : α -> β -> γ) (x y : _) := F x y

instance
  {x : α}
  {y : β}
  [Obj obja x]
  [Obj objb y]
  {F : α -> β -> γ}
  [Liftable obja objb objc F]
  : Obj objc (Liftable_aux obja objb objc F x y) where
    is_obj := Liftable.lift obja objb

class Bifunctor
  {α β γ : Type _}
  (obja : α -> Type _) (homa) (objb : β -> Type _) (homb) (objc : γ -> Type _) (homc)
  [a_cat : Category obja homa] [b_cat : Category objb homb] [c_cat : Category objc homc]
  (F : α -> β -> γ)
  [Liftable obja objb objc F]
  where
    map [Obj obja c₁] [Obj obja c₂] [Obj objb d₁] [Obj objb d₂] : homa c₁ c₂ -> homb d₁ d₂ -> homc (F c₁ d₁) (F c₂ d₂)

class Profunctor
  (objd : α -> Type u) (homd) (objc : β -> Type u) (homc)
  [d_cat : Category objd homd] [c_cat : Category objc homc]
  (p : α -> β -> Type u)
  where
    map [Obj objd d₂] [Obj objd d₁] [Obj objc c₁] [Obj objc c₂] : homd d₂ d₁ -> homc c₁ c₂ -> p d₁ c₁ -> p d₂ c₂


class MonoidalCategory  (obj : α -> Type v) (hom) (tensorObj : α -> α -> α) [Category obj hom] extends Liftable obj obj obj tensorObj, Bifunctor obj hom obj hom obj hom tensorObj where
  tensorUnit : α
  [tensorUnit_obj : Obj obj tensorUnit]
  associator : hom (tensorObj (tensorObj X Y) Z) (tensorObj X (tensorObj Y Z))
  associator_inv : hom (tensorObj X (tensorObj Y Z)) (tensorObj (tensorObj X Y) Z)
  leftUnitor : hom (tensorObj tensorUnit X) X
  leftUnitor_inv : hom X (tensorObj tensorUnit X)
  rightUnitor : hom (tensorObj X tensorUnit) X
  rightUnitor_inv : hom X (tensorObj X tensorUnit)

instance 
  [Category obj hom]
  [moncat : MonoidalCategory obj hom tensorObj] : Obj obj moncat.tensorUnit := moncat.tensorUnit_obj

class MonoidalAction
  (monobj monhom)
  (tensorObj : μ -> μ -> μ)
  [Category monobj monhom]
  [moncat : MonoidalCategory monobj monhom tensorObj]
  (obj : γ -> Type _)
  (hom)
  [Category obj hom]
  (action : μ -> γ -> γ)
  [Liftable monobj obj obj action]
  extends Bifunctor monobj monhom obj hom obj hom action
  where
    unitor [Obj obj X] : hom (action moncat.tensorUnit X) X
    unitor_inv [Obj obj X] : hom X (action moncat.tensorUnit X)
    multiplicator [Obj obj X] [Obj monobj P] [Obj monobj Q] : hom (action P (action Q X)) (action (tensorObj P Q) X)
    multiplicator_inv [Obj obj X] [Obj monobj P] [Obj monobj Q] : hom (action (tensorObj P Q) X) (action P (action Q X)) 

variable
  (monobj monhom)
  (tensorObj : μ -> μ -> μ)
  [Category monobj monhom]
  [moncat : MonoidalCategory monobj monhom tensorObj]
  (obj : γ -> Type _)
  (hom)
  [cat : Category obj hom]
  (actionₗ : μ -> γ -> γ)
  [Liftable monobj obj obj actionₗ]
  [MonoidalAction monobj monhom tensorObj obj hom actionₗ]
  (actionᵣ : μ -> γ -> γ)
  [Liftable monobj obj obj actionᵣ]
  [MonoidalAction monobj monhom tensorObj obj hom actionᵣ]
  (α β ς τ : γ)
  [Obj obj α] [Obj obj β] [Obj obj ς] [Obj obj τ]

class Tambara
  [MonoidalAction monobj monhom tensorObj obj hom actionₗ]
  [MonoidalAction monobj monhom tensorObj obj hom actionᵣ]
  (P : γ -> γ -> Type u)
  extends Profunctor obj hom obj hom P where
    tambara {x y : γ} {xμ : μ} [Obj monobj xμ] : P x y -> P (actionₗ xμ x) (actionᵣ xμ y)


inductive ExOptic
  [MonoidalAction monobj monhom tensorObj obj hom actionₗ]
  [MonoidalAction monobj monhom tensorObj obj hom actionᵣ]
  (α β ς τ : γ)
| mk {xμ : μ} [Obj obj α] [Obj obj β] [Obj obj ς] [Obj obj τ] [Obj monobj xμ] : hom ς (actionₗ xμ α) -> hom (actionᵣ xμ β) τ -> ExOptic α β ς τ

def ProfOptic
  [MonoidalAction monobj monhom tensorObj obj hom actionₗ]
  [MonoidalAction monobj monhom tensorObj obj hom actionᵣ]
  (α β ς τ : γ)
  := (p : _) -> [Tambara monobj monhom tensorObj obj hom actionₗ actionᵣ p] -> p α β -> p ς τ

variable {monobj monhom obj hom tensorObj actionₗ actionᵣ α β ς τ} in
def ExOptic.toProfOptic
  : ExOptic monobj monhom tensorObj obj hom actionₗ actionᵣ α β ς τ -> ProfOptic monobj monhom tensorObj obj hom actionₗ actionᵣ α β ς τ := fun xopt => match xopt with
  | ExOptic.mk l r => fun _ inst =>
    inst.map l r ∘ inst.tambara

instance 
  : Profunctor obj hom obj hom (ExOptic monobj monhom tensorObj obj hom actionₗ actionᵣ α β) where
    map := fun f g xopt => match xopt with
    | ExOptic.mk l r =>
      ExOptic.mk 
        (Category.comp obj l f) 
        (Category.comp obj g r)

instance 
  : Tambara monobj monhom tensorObj obj hom actionₗ actionᵣ (ExOptic monobj monhom tensorObj obj hom actionₗ actionᵣ α β) where
    tambara := fun {_ _ xμ _} xopt => match xopt with
    | ExOptic.mk l r =>
      ExOptic.mk (xμ := tensorObj xμ _)
        (Category.comp 
          obj
          (MonoidalAction.multiplicator monobj monhom obj)
          (Bifunctor.map monobj obj obj (Category.id (hom := monhom) monobj) l)) 
        (Category.comp 
          obj
          (Bifunctor.map monobj obj obj (Category.id (hom := monhom) monobj) r)
          (MonoidalAction.multiplicator_inv monobj monhom obj))


variable {monobj monhom obj hom tensorObj actionₗ actionᵣ α β ς τ} in
def ProfOptic.toExOptic
  : ProfOptic monobj monhom tensorObj obj hom actionₗ actionᵣ α β ς τ -> ExOptic monobj monhom tensorObj obj hom actionₗ actionᵣ α β ς τ
  := fun xprofopt =>
    xprofopt _ (ExOptic.mk (MonoidalAction.unitor_inv (tensorObj := tensorObj) (monhom := monhom) obj) (MonoidalAction.unitor (tensorObj := tensorObj) (monobj := monobj) obj))
