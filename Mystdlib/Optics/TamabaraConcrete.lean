import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

class ConCatStruct (C : Type _) [CategoryStruct C] (FC : outParam (C -> C -> Type*)) {CC : outParam (C → Type _)}  [outParam (∀ X Y, FunLike (FC X Y) (CC X) (CC Y))] where
  hom {X Y : C} : Quiver.Hom X Y -> FC X Y
  ofHom : ∀ {X Y}, FC X Y → Quiver.Hom X Y

def ConCatStruct.comp
  {Ccc : C₀ -> Type _}
  [CategoryStruct C₀]
  [∀ X Y, FunLike (C₁ X Y) (Ccc X) (Ccc Y)]
  [ConCatStruct C₀ C₁]
  : C₁ β γ -> C₁ α β -> C₁ α γ := 
  fun f g => ConCatStruct.hom (CategoryStruct.comp (ConCatStruct.ofHom g) (ConCatStruct.ofHom f))


class BifunctorStruct
  {C₁ : C₀ -> C₀ -> Type _}
  {Ccc : C₀ -> Type _}
  [CategoryStruct C₀]
  [∀ X Y, FunLike (C₁ X Y) (Ccc X) (Ccc Y)]

  [CategoryStruct D₀]
  {Dcc : D₀ -> Type _}
  [∀ X Y, FunLike (D₁ X Y) (Dcc X) (Dcc Y)]
  [ConCatStruct D₀ D₁]

  [CategoryStruct E₀]
  {Ecc : E₀ -> Type _}
  [∀ X Y, FunLike (E₁ X Y) (Ecc X) (Ecc Y)]
  [ConCatStruct E₀ E₁]

  (F : C₀ -> D₀ -> E₀) where
    map {c₁ c₂ : C₀} {d₁ d₂ : D₀} : C₁ c₁ c₂ -> D₁ d₁ d₂ -> E₁ (F c₁ d₁) (F c₂ d₂)


variable
  [CategoryStruct C₀]
  {C₁ : C₀ -> C₀ -> Type*}
  {Ccc : C₀ -> Type w}
  [∀ X Y, FunLike (C₁ X Y) (Ccc X) (Ccc Y)]
  
abbrev ToType [ConCatStruct C₀ C₁] := Ccc

variable
  [CategoryStruct C₀]
  {C₁ : C₀ -> C₀ -> Type*}
  {Ccc : C₀ -> Type w}
  [∀ X Y, FunLike (C₁ X Y) (Ccc X) (Ccc Y)]
  [CategoryStruct D₀]
  {Dcc : D₀ -> Type v}
  [∀ X Y, FunLike (D₁ X Y) (Dcc X) (Dcc Y)]
  [ConCatStruct D₀ D₁]

class Profunctor
  [ConCatStruct D₀ D₁]
  [ConCatStruct C₀ C₁]
  (P : D₀ -> C₀ -> Type*)
  where
    map {d₂ d₁ : D₀} {c₁ c₂ : C₀} : D₁ d₂ d₁ -> C₁ c₁ c₂ -> P d₁ c₁ -> P d₂ c₂

variable
  [ConCatStruct D₀  D₁]
  [ConCatStruct C₀ C₁]

class ConcreteIsoStruct 
  [CategoryStruct C₀] 
  [ConCatStruct C₀ C₁] 
  (X Y : C₀) where
  hom : C₁ X Y
  inv : C₁ Y X

class PreMonCatPreStruct (C₀ : Type u) where
  tensorUnit : C₀
  tensorObj : C₀ -> C₀ -> C₀

class MonCatPreStruct (C₀ : Type u) (C₁ : C₀ -> C₀ -> Type*) 
  [CategoryStruct C₀] 
  {Ccc : C₀ -> Type w}
  [∀ X Y, FunLike (C₁ X Y) (Ccc X) (Ccc Y)]
  [ConCatStruct C₀ C₁] extends PreMonCatPreStruct C₀
  where
    associator : (X Y Z : C₀) -> ConcreteIsoStruct (tensorObj (tensorObj X Y) Z) (tensorObj X (tensorObj Y Z))
    leftUnitor : (X : C₀) -> ConcreteIsoStruct (tensorObj tensorUnit X) X
    rightUnitor : (X : C₀) -> ConcreteIsoStruct (tensorObj X tensorUnit) X

class MonoidalAction
  (action : M₀ -> C₀ -> C₀)
  [CategoryStruct M₀]
  {M₁ : M₀ -> M₀ -> Type*}
  {Mcc : M₀ -> Type p}
  [∀ X Y, FunLike (M₁ X Y) (Mcc X) (Mcc Y)]
  [ConCatStruct M₀ M₁]
  [MonCatPreStruct M₀ M₁]
  [BifunctorStruct (C₁ := M₁) (Ccc := Mcc) action]
  where
    unitor (X : C₀) : ConcreteIsoStruct (action PreMonCatPreStruct.tensorUnit X) X
    multiplicator (X : C₀) (P Q : M₀) : ConcreteIsoStruct (action P (action Q X)) (action (PreMonCatPreStruct.tensorObj P Q) X)

variable
  [CategoryStruct M₀]
  {M₁ : M₀ -> M₀ -> Type*}
  {Mcc : M₀ -> Type w}
  [∀ X Y, FunLike (M₁ X Y) (Mcc X) (Mcc Y)]
  [ConCatStruct M₀ M₁]
  [MonCatPreStruct M₀ M₁]

variable
  (actionₗ : M₀ -> D₀ -> D₀)
  (actionᵣ : M₀ -> C₀ -> C₀)
  {M₁ : M₀ -> M₀ -> Type*}
  {Mcc : M₀ -> Type p}
  [∀ X Y, FunLike (M₁ X Y) (Mcc X) (Mcc Y)]
  [ConCatStruct M₀ M₁]
  [MonCatPreStruct M₀ M₁]
  [BifunctorStruct (C₁ := M₁) (Ccc := Mcc) actionₗ]
  [BifunctorStruct (C₁ := M₁) (Ccc := Mcc) actionᵣ]
  [MonoidalAction actionₗ]
  [MonoidalAction actionᵣ]

inductive Optic 
  [ConCatStruct D₀ D₁]
  [ConCatStruct C₀ C₁]
  (α : D₀) (β : C₀) (ς : D₀) (τ : C₀)
| mk : {μ : M₀} -> D₁ ς (actionₗ μ α) -> C₁ (actionᵣ μ β) τ -> Optic α β ς τ


class Tambara (P : D₀ -> C₀ -> Type _) [Profunctor P] where
  tambara  {α : D₀} {β : C₀} {μ : M₀} : P α β -> P (actionₗ μ α) (actionᵣ μ β)

def ProfOptic
  (α β ς τ)
  := {P : D₀ -> C₀ -> Type _} -> [Profunctor P] -> [Tambara actionₗ actionᵣ P] -> P α β -> P ς τ


def Optic.toProfOptic
  {α ς : D₀}
  {β τ : C₀}
  : Optic actionₗ actionᵣ α β ς τ -> ProfOptic actionₗ actionᵣ α β ς τ :=
  fun xopt {_ prof_inst tamb_inst} =>
    match xopt with
    | .mk l r =>
      prof_inst.map l r ∘ tamb_inst.tambara

instance : Profunctor (Optic actionₗ actionᵣ α β) where
  map := fun x y ⟨l, r⟩ =>
    .mk (ConCatStruct.comp l x) (ConCatStruct.comp y r)

def ProfOptic.toOptic
  (actionₗ : M₀ -> D₀ -> D₀)
  (actionᵣ : M₀ -> C₀ -> C₀)
  {M₁ : M₀ -> M₀ -> Type*}
  {Mcc : M₀ -> Type p}
  [∀ X Y, FunLike (M₁ X Y) (Mcc X) (Mcc Y)]
  [ConCatStruct M₀ M₁]
  [MonCatPreStruct M₀ M₁]
  [BifunctorStruct (C₁ := M₁) (Ccc := Mcc) actionₗ]
  [BifunctorStruct (C₁ := M₁) (Ccc := Mcc) actionᵣ]
  [insta : MonoidalAction actionₗ]
  [instb : MonoidalAction actionᵣ]
  [Tambara actionₗ actionᵣ (Optic actionₗ actionᵣ α β)]
  : ProfOptic actionₗ actionᵣ α β ς τ -> Optic actionₗ actionᵣ α β ς τ := 
    fun xprofopt => 
      xprofopt (Optic.mk (insta.unitor _).inv (instb.unitor _).hom)

instance : CategoryStruct Type where
  Hom := fun α β => α -> β
  id := fun _ => id
  comp := fun f g => Function.comp g f

instance : (X Y : Type) → FunLike ((fun x1 x2 => x1 → x2) X Y) (id X) (id Y) := 
  fun X Y => ⟨id, by rw [Function.Injective]; intros; grind⟩

instance : ConCatStruct Type (· -> ·) (CC := id) where
  hom := id
  ofHom := id

instance : BifunctorStruct (fun (α β : Type) => α ⊕ β) where


