

/-
Given [Category objc c],
objc selects objects from a category
c selects morphisms from the same category
-/
class Category (C₀ : Type -> Type) (C₁ : Type -> Type -> Type) where
  unit : C₀ α -> C₁ α α
  comp : C₁ β γ -> C₁ α β  -> C₁ α γ

variable 
  (A₀ C₀ D₀ E₀ : Type -> Type) 
  (A₁ C₁ D₁ E₁ : Type -> Type -> Type) 
  [Category A₀ A₁] [Category C₀ C₁] [Category D₀ D₁] [Category E₀ E₁]


class Bifunctor (F : Type -> Type -> Type) where
  lift {bf₁ : C₀ α} {bf₂ : D₀ β} : E₀ (F α β)
  bimap : C₀ α₁ -> C₀ α₂ -> D₀ β₁ -> D₀ β₂ -> C₁ α₁ α₂ -> D₁ β₁ β₂ -> E₁ (F α₁ β₁) (F α₂ β₂)


universe u

class Profunctor (P : Type -> Type -> Type u) where
  dimap {pf₁ : C₀ α₁} {pf₂ : C₀ α₂} {pf₃ : D₀ β₁} {pf₄ : D₀ β₂} : C₁ α₂ α₁ -> D₁ β₁ β₂ -> P α₁ β₁ -> P α₂ β₂

variable 
  (O : Type -> Type -> Type) 
  [Bifunctor A₀ A₀ A₀ A₁ A₁ A₁ O]

class MonoidalCategory (ι) where
  iota_obj : A₀ ι
  alpha : A₀ α -> A₀ β -> A₀ γ -> A₁ (O α (O β γ)) (O (O α β) γ)
  alphainv : A₀ α -> A₀ β -> A₀ γ -> A₁ (O (O α β) γ) (O α (O β γ))
  lambda : A₀ α -> A₁ (O α ι) α
  lambdainv : A₀ α -> A₁ α (O α ι)
  rho : A₀ α -> A₁ (O ι α) α
  rhoinv : A₀ α -> A₁ α (O ι α)

variable
  [MonoidalCategory A₀ A₁ O ι]
  (G : Type -> Type -> Type)
  [temp_bif_inst_id : Bifunctor A₀ C₀ C₀ A₁ C₁ C₁ G]


class MonoidalAction where
  unitor : C₀ α -> C₁ (O ι α) α
  unitorinv : C₀ α -> C₁ α (O ι α)
  multiplicator : C₀ α -> A₀ β -> A₀ γ -> C₁ (G β (G γ α)) (G (O β γ) α)
  multiplicatorinv : C₀ α -> A₀ β -> A₀ γ -> C₁ (G (O β γ) α) (G β (G γ α))

variable 
  [MonoidalAction A₀ C₀ C₁ O G]
  (H : Type -> Type -> Type)
  [MonoidalAction A₀ D₀ D₁ O H]

inductive Optic (α β ς τ : Type)
| mk {o₁ : C₀ α} {o₂ : C₀ ς} {o₃ : D₀ β} {o₄ : D₀ τ} {e : A₀ ξ} : C₁ ς (G ξ α) -> D₁ (H ξ β) τ -> Optic α β ς τ

def Optic.left (xopt : Optic A₀ C₀ D₀ C₁ D₁ G H α β ς τ) : (ξ : Type) × C₁ ς (G ξ α) :=
  match xopt with
  | .mk left _ => ⟨_, left⟩

def Optic.right (xopt : Optic A₀ C₀ D₀ C₁ D₁ G H α β ς τ) : (ξ : Type) × D₁ (H ξ β) τ :=
  match xopt with
  | .mk _ right => ⟨_, right⟩


variable
  (P : Type -> Type -> Type u)
  [temp_profunctor_inst_id : Profunctor C₀ D₀ C₁ D₁ P]

class Tambara where
  tambara {tm₁ : C₀ ξ} {tm₂ : D₀ γ} {tm₃ : A₀ ω} : P ξ γ -> P (O ω ξ) (G ω γ)

/--
info: class Tambara.{u} (A₀ C₀ D₀ : Type → Type) (O G : Type → Type → Type) (P : Type → Type → Type u) : Type (max 1 u)
number of parameters: 6
fields:
  Tambara.tambara : {ξ γ ω : Type} → {tm₁ : C₀ ξ} → {tm₂ : D₀ γ} → {tm₃ : A₀ ω} → P ξ γ → P (O ω ξ) (G ω γ)
constructor:
  Tambara.mk.{u} {A₀ C₀ D₀ : Type → Type} {O G : Type → Type → Type} {P : Type → Type → Type u}
    (tambara : {ξ γ ω : Type} → {tm₁ : C₀ ξ} → {tm₂ : D₀ γ} → {tm₃ : A₀ ω} → P ξ γ → P (O ω ξ) (G ω γ)) :
    Tambara A₀ C₀ D₀ O G P
-/
#guard_msgs in
#print Tambara
variable
  [temp_tambara_inst_id : Tambara A₀ C₀ D₀ O G P]

def ProfOptic (α β ς τ : Type) : Type u := {po₁ : C₀ α} -> {po₂ : D₀ β} -> {po₃ : C₀ ς} -> {po₄ : D₀ τ} -> P α β -> P ς τ

/--
info: inductive Optic : (Type → Type) →
  (Type → Type) →
    (Type → Type) →
      (Type → Type → Type) →
        (Type → Type → Type) → (Type → Type → Type) → (Type → Type → Type) → Type → Type → Type → Type → Type 1
number of parameters: 11
constructors:
Optic.mk : {A₀ C₀ D₀ : Type → Type} →
  {C₁ D₁ G H : Type → Type → Type} →
    {α β ς τ ξ : Type} →
      {o₁ : C₀ α} →
        {o₂ : C₀ ς} →
          {o₃ : D₀ β} → {o₄ : D₀ τ} → {e : A₀ ξ} → C₁ ς (G ξ α) → D₁ (H ξ β) τ → Optic A₀ C₀ D₀ C₁ D₁ G H α β ς τ
-/
#guard_msgs in
#print Optic

/--
info: def ProfOptic.{u} : (Type → Type) → (Type → Type) → (Type → Type → Type u) → Type → Type → Type → Type → Type u :=
fun C₀ D₀ P α β ς τ => {po₁ : C₀ α} → {po₂ : D₀ β} → {po₃ : C₀ ς} → {po₄ : D₀ τ} → P α β → P ς τ
-/
#guard_msgs in
#print ProfOptic

/--
info: class Tambara.{u} (A₀ C₀ D₀ : Type → Type) (O G : Type → Type → Type) (P : Type → Type → Type u) : Type (max 1 u)
number of parameters: 6
fields:
  Tambara.tambara : {ξ γ ω : Type} → {tm₁ : C₀ ξ} → {tm₂ : D₀ γ} → {tm₃ : A₀ ω} → P ξ γ → P (O ω ξ) (G ω γ)
constructor:
  Tambara.mk.{u} {A₀ C₀ D₀ : Type → Type} {O G : Type → Type → Type} {P : Type → Type → Type u}
    (tambara : {ξ γ ω : Type} → {tm₁ : C₀ ξ} → {tm₂ : D₀ γ} → {tm₃ : A₀ ω} → P ξ γ → P (O ω ξ) (G ω γ)) :
    Tambara A₀ C₀ D₀ O G P
-/
#guard_msgs in
#print Tambara

/--
info: class Profunctor.{u} (C₀ D₀ : Type → Type) (C₁ D₁ : Type → Type → Type) (P : Type → Type → Type u) : Type (max 1 u)
number of parameters: 5
fields:
  Profunctor.dimap : {α₁ α₂ β₁ β₂ : Type} →
      {pf₁ : C₀ α₁} → {pf₂ : C₀ α₂} → {pf₃ : D₀ β₁} → {pf₄ : D₀ β₂} → C₁ α₂ α₁ → D₁ β₁ β₂ → P α₁ β₁ → P α₂ β₂
constructor:
  Profunctor.mk.{u} {C₀ D₀ : Type → Type} {C₁ D₁ : Type → Type → Type} {P : Type → Type → Type u}
    (dimap :
      {α₁ α₂ β₁ β₂ : Type} →
        {pf₁ : C₀ α₁} → {pf₂ : C₀ α₂} → {pf₃ : D₀ β₁} → {pf₄ : D₀ β₂} → C₁ α₂ α₁ → D₁ β₁ β₂ → P α₁ β₁ → P α₂ β₂) :
    Profunctor C₀ D₀ C₁ D₁ P
-/
#guard_msgs in
#print Profunctor

/-
[Bifunctor objm m objm m objm m o h] [Bifunctor objm m objc c objc c f h'] [Bifunctor objm m objd d objd d g h'']
-/

variable
  [Bifunctor A₀ C₀ C₀ A₁ C₁ C₁ O]
  [Bifunctor A₀ D₀ D₀ A₁ D₁ D₁ G]

def Optic.toProfOptic : Optic A₀ C₀ D₀ C₁ D₁ O G α β ς τ -> ProfOptic C₀ D₀ P α β ς τ 
| .mk (ξ := ξ) l r =>
  Function.comp
    (Profunctor.dimap C₀ D₀ 
      (pf₁ := Bifunctor.lift (bf₁ := ‹_›) (bf₂ := ‹_›) A₀ C₀ A₁ C₁ C₁) 
      (pf₂ := ‹_›) 
      (pf₃ := Bifunctor.lift (bf₁ := ‹_›) (bf₂ := ‹_›) A₀ D₀ A₁ D₁ D₁) 
      (pf₄ := ‹_›) l r) 
    (Tambara.tambara 
      (tm₁ := ‹_›) 
      (tm₂ := ‹_›) 
      (tm₃ := ‹_›))

def Optic_aux_type (α β : Type) := {ς τ : Type} -> Optic A₀ C₀ D₀ C₁ D₁ O G α β ς τ

def ProfOptic.toOptic : ProfOptic C₀ D₀ (Optic A₀ C₀ D₀ C₁ D₁ O G α β) α β ς τ -> Optic A₀ C₀ D₀ C₁ D₁ O G α β ς τ := fun xpo =>
  xpo (Optic.mk (MonoidalAction.unitorinv A₀ _ _) (MonoidalAction.unitor A₀ (C₀ := D₀) (C₁ := D₁) _ _))




