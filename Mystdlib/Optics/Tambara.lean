import Mystdlib.Optics.Categories

inductive Optic 
  [Category C₀ C₁] 
  [Category D₀ D₁] 
  [Category M₀ M₁]
  (O)
  [MonoidalCat M₀ M₁ O]
  (actionₗ : M₀ -> D₀ -> D₀)
  (actionᵣ : M₀ -> C₀ -> C₀)
  [Bifunctor _ _ _ O]
  [Bifunctor _ _ _ actionₗ]
  [Bifunctor _ _ _ actionᵣ]
  [monaxa : MonoidalAction O actionₗ]
  [monaxb : MonoidalAction O actionᵣ]
  (α : D₀) (β : C₀) (ς : D₀) (τ : C₀)
| mk : {μ : M₀} -> D₁ ς (actionₗ μ α) -> C₁ (actionᵣ μ β) τ -> Optic O actionₗ actionᵣ α β ς τ

class Tambara 
  [Category C₀ C₁] 
  [Category D₀ D₁] 
  (M₀ M₁)
  [Category M₀ M₁]
  (O)
  [MonoidalCat M₀ M₁ O]
  (actionₗ : M₀ -> D₀ -> D₀)
  (actionᵣ : M₀ -> C₀ -> C₀)
  [Bifunctor _ _ _ O]
  [Bifunctor _ _ _ actionₗ]
  [Bifunctor _ _ _ actionᵣ]
  [MonoidalAction O actionₗ]
  [MonoidalAction O actionᵣ]
  (P : D₀ -> C₀ -> Type _) [Profunctor P] where
  tambara  {α : D₀} {β : C₀} {μ : M₀} : P α β -> P (actionₗ μ α) (actionᵣ μ β)

def ProfOptic
  [Category C₀ C₁] 
  [Category D₀ D₁] 
  (M₀ M₁)
  (O : M₀ -> M₀ -> M₀)
  [Category M₀ M₁]
  [MonoidalCat M₀ M₁ O]
  (actionₗ : M₀ -> D₀ -> D₀)
  (actionᵣ : M₀ -> C₀ -> C₀)
  [Bifunctor _ _ _ O]
  [Bifunctor _ _ _ actionₗ]
  [Bifunctor _ _ _ actionᵣ]
  [MonoidalAction O actionₗ]
  [MonoidalAction O actionᵣ]
  (α β ς τ)
  := {P : D₀ -> C₀ -> Type _} -> [Profunctor P] -> [Tambara _ _ O actionₗ actionᵣ P] -> P α β -> P ς τ

def Optic.toProfOptic
  [Category C₀ C₁] 
  [Category D₀ D₁] 
  [Category M₀ M₁]
  [MonoidalCat M₀ M₁ O]
  (actionₗ : M₀ -> D₀ -> D₀)
  (actionᵣ : M₀ -> C₀ -> C₀)
  [Bifunctor _ _ _ O]
  [Bifunctor _ _ _ actionₗ]
  [Bifunctor _ _ _ actionᵣ]
  [MonoidalAction O actionₗ]
  [MonoidalAction O actionᵣ]
  {α ς : D₀}
  {β τ : C₀}
  : Optic O actionₗ actionᵣ α β ς τ -> ProfOptic M₀ M₁ O actionₗ actionᵣ α β ς τ :=
  fun xopt {_ prof_inst tamb_inst} =>
    match xopt with
    | .mk l r =>
      prof_inst.map l r ∘ tamb_inst.tambara

instance 
  [Category C₀ C₁] 
  [Category D₀ D₁] 
  [Category M₀ M₁]
  [MonoidalCat M₀ M₁ O]
  (actionₗ : M₀ -> D₀ -> D₀)
  (actionᵣ : M₀ -> C₀ -> C₀)
  [Bifunctor _ _ _ O]
  [Bifunctor _ _ _ actionₗ]
  [Bifunctor _ _ _ actionᵣ]
  [MonoidalAction O actionₗ]
  [MonoidalAction O actionᵣ]
  : Profunctor (Optic O actionₗ actionᵣ α β) where
  map := fun x y ⟨l, r⟩ =>
    .mk (Category.comp l x) (Category.comp y r)

instance 
  [Category C₀ C₁] 
  [Category D₀ D₁] 
  [Category M₀ M₁]
  [MonoidalCat M₀ M₁ O]
  (actionₗ : M₀ -> D₀ -> D₀)
  (actionᵣ : M₀ -> C₀ -> C₀)
  [Bifunctor _ _ _ O]
  [Bifunctor _ _ _ actionₗ]
  [Bifunctor _ _ _ actionᵣ]
  [insta : MonoidalAction O actionₗ]
  [MonoidalAction O actionᵣ]
  : Tambara _ _ O actionₗ actionᵣ (Optic O actionₗ actionᵣ α β) where
    tambara := fun {α' β' μ} xopt => match xopt with
    | .mk (μ := μ') l r =>
      have thisa := @MonoidalAction.multiplicator _ _ _ M₁ inferInstance inferInstance O inferInstance inferInstance _ inferInstance _ _ _ _
      have thisb := Bifunctor.map (C₁ := M₁) (D₁ := D₁) (E₁ := D₁) (F := actionₗ) Category.id l
      have thisc := Bifunctor.map (C₁ := M₁) (E₁ := C₁) (F := actionᵣ) Category.id r
      have thisd := @MonoidalAction.multiplicator _ _ _ M₁ inferInstance inferInstance O inferInstance inferInstance _ inferInstance _ _ _ _
      .mk (Category.comp thisa.hom thisb) (Category.comp thisc thisd.inv)

def ProfOptic.toOptic
  [Category C₀ C₁] 
  [Category D₀ D₁] 
  [Category M₀ M₁]
  [mon_cat_inst : MonoidalCat M₀ M₁ O]
  {actionₗ : M₀ -> D₀ -> D₀}
  {actionᵣ : M₀ -> C₀ -> C₀}
  [Bifunctor _ _ _ O]
  [Bifunctor _ _ _ actionₗ]
  [Bifunctor _ _ _ actionᵣ]
  [monaxa : MonoidalAction O actionₗ]
  [monaxb : MonoidalAction O actionᵣ]
  : ProfOptic M₀ M₁ O actionₗ actionᵣ α β ς τ -> Optic O actionₗ actionᵣ α β ς τ := 
    fun xprofopt => 
      xprofopt (Optic.mk monaxa.unitor.inv monaxb.unitor.hom)


def test := 7
