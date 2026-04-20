import Mystdlib.General
import Mystdlib.Optics.Tambara.Tambara
import Mathlib.Control.Traversable.Basic


open Tambara


abbrev NatTsfm.{u, v} := fun (f g : Type u -> Type v) => ∀α, f α -> g α

abbrev App.{u, v} := fun (f : Type u -> Type v) (α : Type u) => f α

instance appcat : Category (carrier := Type u -> Type v) Applicative NatTsfm where
  id := fun _ => id
  comp := fun f g _ => f _ ∘ g _

instance trvcat : Category (carrier := Type u -> Type u) Traversable NatTsfm where
  id := fun _ => id
  comp := fun f g _ => f _ ∘ g _


instance [Applicative f] : Obj Applicative f where
  is_obj := inferInstance

instance [inst : Obj Applicative f] : Applicative f := inst.is_obj

instance [Traversable f] : Obj Traversable f where
  is_obj := inferInstance

instance [inst : Obj Traversable f] : Traversable f := inst.is_obj

abbrev Trivial.{u} : Type u -> Type u := fun (_ : Type u) => PUnit

instance typecat : Category (carrier := Type u) Trivial (· -> ·) where
  id := id
  comp := fun f g => f ∘ g

instance {α : Type u} : Obj Trivial α where
  is_obj := .unit

instance {f} : Liftable obj obj' Trivial f where
  lift := .unit

def bimap
  [inst : Bifunctor Trivial (· -> ·) Trivial (· -> ·) Trivial (· -> ·) p]
  := @inst.map

instance : Bifunctor Trivial (· -> ·) Trivial (· -> ·) Trivial (· -> ·) Prod where
  map := fun f g h => (f h.1, g h.2)

instance : MonoidalCategory Trivial (· -> ·) Prod where
  tensorUnit := PUnit
  associator := Prod.assoc_inv
  associator_inv := Prod.assoc
  leftUnitor := Prod.snd
  leftUnitor_inv := (.unit, ·)
  rightUnitor := Prod.fst
  rightUnitor_inv := (·, .unit)

instance : Bifunctor Trivial (· -> ·) Trivial (· -> ·) Trivial (· -> ·) Sum where
  map := fun f g =>
    Sum.elim (.inl ∘ f) (.inr ∘ g)

instance : MonoidalCategory Trivial (· -> ·) Sum.{u, u} where
  tensorUnit := PEmpty
  associator := Sum.assoc_inv
  associator_inv := Sum.assoc
  leftUnitor := Sum.elim PEmpty.elim id
  leftUnitor_inv := .inr
  rightUnitor := Sum.elim id PEmpty.elim
  rightUnitor_inv := .inl

instance {o : α -> α -> α} {obj : α -> Type u} {hom : α -> α -> Type u} [Category obj hom] [MonoidalCategory obj hom o]  : MonoidalAction obj hom o obj hom o where
  unitor := MonoidalCategory.leftUnitor
  unitor_inv := MonoidalCategory.leftUnitor_inv
  multiplicator := MonoidalCategory.associator_inv obj
  multiplicator_inv := MonoidalCategory.associator obj

instance : MonoidalAction Trivial (· -> ·) Sum Trivial.{u} (· -> ·) Sum where
  unitor := fun x => x.elim PEmpty.elim id
  unitor_inv := .inr
  multiplicator := Sum.assoc
  multiplicator_inv := Sum.assoc_inv


instance : Liftable Applicative Applicative Applicative (· ∘ ·) where
  lift := fun {_ _ _ _} => inferInstance

instance : Bifunctor Applicative NatTsfm.{u,u} Applicative NatTsfm Applicative NatTsfm (· ∘ ·) where
  map := fun {_ _ _ k _ _ _ _} f g α h => (f (k α)) (fmap (g α) h)

instance : MonoidalCategory Applicative NatTsfm (· ∘ ·) where
  tensorUnit := Id
  associator := fun _ => id
  associator_inv := fun _ => id
  leftUnitor := fun _ => id
  leftUnitor_inv := fun _ => id
  rightUnitor := fun _ => id
  rightUnitor_inv := fun _ => id

instance : Liftable Traversable Traversable Traversable (· ∘ ·) where
  lift := fun {_ _ tva tvb} => ⟨fun f => tva.is_obj.traverse (tvb.is_obj.traverse f)⟩

instance : Bifunctor Traversable NatTsfm.{u,u} Traversable NatTsfm Traversable NatTsfm (· ∘ ·) where
  map := fun {_ _ _ k _ _ _ _} f g α h => (f (k α)) (fmap (g α) h)

instance : MonoidalCategory Traversable NatTsfm (· ∘ ·) where
  tensorUnit := Id
  associator := fun _ => id
  associator_inv := fun _ => id
  leftUnitor := fun _ => id
  leftUnitor_inv := fun _ => id
  rightUnitor := fun _ => id
  rightUnitor_inv := fun _ => id


instance : Bifunctor Applicative NatTsfm Trivial (· -> ·) Trivial (· -> ·) App where
  map := fun {_ _ a _ _ _ _ _} f g => (fmap g ∘ f a)

instance : MonoidalAction Applicative NatTsfm (· ∘ ·) Trivial (· -> ·) App where
  unitor := id
  unitor_inv := id
  multiplicator := id
  multiplicator_inv := id

instance : Bifunctor Traversable NatTsfm Trivial (· -> ·) Trivial (· -> ·) App where
  map := fun {_ _ a _ _ inst _ _} f g => 
    have := inst.is_obj
    fmap g ∘ (f a)

instance : MonoidalAction Traversable NatTsfm (· ∘ ·) Trivial (· -> ·) (· ·) where
  unitor := id
  unitor_inv := id
  multiplicator := id
  multiplicator_inv := id

section productCategory

instance 
  {x : α × β}
  [inst : Obj f x]
  : Obj (fun a => f (a, x.snd)) x.fst where
    is_obj := inst.is_obj

instance 
  {x : α × β}
  [inst : Obj f x]
  : Obj (fun b => f (x.fst, b)) x.snd where
    is_obj := inst.is_obj

instance 
  {x : α × α}
  {f : α -> Type _}
  [inst : Obj (fun xprod => f xprod.fst × f xprod.snd) x]
  : Obj f x.fst where
    is_obj := inst.is_obj.fst

instance 
  {x : α × α}
  {f : α -> Type _}
  [inst : Obj (fun xprod => f xprod.fst × f xprod.snd) x]
  : Obj f x.snd where
    is_obj := inst.is_obj.snd

@[reducible]
def productObj (obj : γ -> Type u) : γ × γ -> Type u :=
  (fun (x : γ × γ) => obj x.fst × obj x.snd)

@[reducible]
def productHom (hom : γ -> γ -> Type u) : γ × γ -> γ × γ -> Type u :=
  (fun xprod xprod' => hom xprod.fst xprod'.fst × hom xprod.snd xprod'.snd)

instance [inst : @Category carrier obj hom] : @Category 
  (carrier × carrier) 
  (productObj obj)
  (productHom hom)
  where
    id := (inst.id, inst.id)
    comp := fun f g => (inst.comp f.fst g.fst, inst.comp f.snd g.snd)

@[reducible]
def productTensorObj (tensorObj : γ -> γ -> γ) : γ × γ -> γ × γ -> γ × γ :=
  (fun x y => (tensorObj x.1 y.1, tensorObj x.2 y.2))


instance
  [lift : Liftable obj obj obj tensorObj]
  : Liftable 
    (productObj obj)
    (productObj obj)
    (productObj obj)
    (productTensorObj tensorObj)
  where
    lift := (lift.lift, lift.lift)


instance 
  {monobj : γ -> Type u}
  [Category monobj monhom]
  [Liftable monobj monobj monobj tensorObj]
  [inst : Bifunctor monobj monhom monobj monhom monobj monhom tensorObj]
  : Bifunctor (productObj monobj) (productHom monhom) (productObj monobj) (productHom monhom) (productObj monobj) (productHom monhom) (productTensorObj tensorObj)
  where
    map := fun f g => (inst.map f.fst g.fst, inst.map f.snd g.snd)

instance [Obj obj x] [Obj obj y] : Obj (productObj obj) (x, y) where
  is_obj := (Obj.is_obj, Obj.is_obj)

instance 
  [Category monobj monhom]
  [inst : MonoidalCategory monobj monhom tensorObj]
  : Obj 
    (productObj monobj)
    (inst.tensorUnit, inst.tensorUnit) where
      is_obj := (inst.tensorUnit_obj.is_obj, inst.tensorUnit_obj.is_obj)

instance monProdCat
  {monobj : γ -> Type u}
  [Category monobj monhom]
  [inst : MonoidalCategory monobj monhom tensorObj]
  : MonoidalCategory 
    (productObj monobj) 
    (productHom monhom) 
    (productTensorObj tensorObj) where
      tensorUnit := (inst.tensorUnit, inst.tensorUnit)
      associator := (inst.associator, inst.associator)
      associator_inv := (inst.associator_inv, inst.associator_inv)
      leftUnitor := (inst.leftUnitor, inst.leftUnitor)
      leftUnitor_inv := (inst.leftUnitor_inv, inst.leftUnitor_inv)
      rightUnitor := (inst.rightUnitor, inst.rightUnitor)
      rightUnitor_inv := (inst.rightUnitor_inv, inst.rightUnitor_inv)

def MonProdCat.compTensorObj
  (tensorObja tensorObjb : μ -> μ -> μ)
  : μ × μ -> μ × μ -> μ × μ
  := fun x y => (tensorObja x.1 y.1, tensorObjb x.2 y.2)


instance
  [lifta : Liftable monobj monobj monobj tensorObja]
  [liftb : Liftable monobj monobj monobj tensorObjb]
  : Liftable (productObj monobj) (productObj monobj) (productObj monobj) (MonProdCat.compTensorObj tensorObja tensorObjb) where
    lift := (lifta.lift, liftb.lift)

instance
  {γ : Type v}
  {monobj : γ -> Type u}
  {tensorObja : γ -> γ -> γ}
  {tensorObjb : γ -> γ -> γ}
  {monhom : γ -> γ -> Type u}
  [Category monobj monhom]
  [cata : MonoidalCategory monobj monhom tensorObja]
  [catb : MonoidalCategory monobj monhom tensorObjb]
  : Bifunctor (productObj monobj) (productHom monhom) (productObj monobj) (productHom monhom) (productObj monobj) (productHom monhom) (MonProdCat.compTensorObj tensorObja tensorObjb) where
    map := fun f g => (cata.map f.fst g.fst, catb.map f.snd g.snd)

instance 
  {γ : Type v}
  {monobj : γ -> Type u}
  {tensorObja : γ -> γ -> γ}
  {tensorObjb : γ -> γ -> γ}
  {monhom : γ -> γ -> Type u}
  [Category monobj monhom]
  [cata : MonoidalCategory monobj monhom tensorObja]
  [catb : MonoidalCategory monobj monhom tensorObjb]
  : MonoidalCategory (productObj monobj) (productHom monhom) (MonProdCat.compTensorObj tensorObja tensorObjb) 
  where
    tensorUnit := (cata.tensorUnit, catb.tensorUnit)
    associator := (cata.associator, catb.associator)
    associator_inv := (cata.associator_inv, catb.associator_inv)
    leftUnitor := (cata.leftUnitor, catb.leftUnitor)
    leftUnitor_inv := (cata.leftUnitor_inv, catb.leftUnitor_inv)
    rightUnitor := (cata.rightUnitor, catb.rightUnitor)
    rightUnitor_inv := (cata.rightUnitor_inv, catb.rightUnitor_inv)


def MonoidalAction.compose_raw
  (ax ax' : γ -> γ -> γ)
  : γ × γ -> γ -> γ
  := fun xμ xγ => ax xμ.1 (ax' xμ.2 xγ)

instance 
  [Liftable monobj monobj monobj action]
  [liftb : Liftable monobj monobj monobj action']
  : Liftable (productObj monobj) monobj monobj (MonoidalAction.compose_raw action' action)
  where
    lift := liftb.lift

instance 
  {γ : Type v}
  {monobj : γ -> Type u}
  {monhom : γ -> γ -> Type u}
  {action action' : γ -> γ -> γ}
  [Category monobj monhom]
  [Liftable monobj monobj monobj action]
  [bifa : Bifunctor monobj monhom monobj monhom monobj monhom action]
  [Liftable monobj monobj monobj action']
  [bifb : Bifunctor monobj monhom monobj monhom monobj monhom action']
  : Bifunctor (productObj monobj) (productHom monhom) monobj monhom monobj monhom
    (MonoidalAction.compose_raw action action')
  where
    map := fun f g => bifa.map f.fst (bifb.map f.snd g)

def MonoidalAction.coproduct
  (ax : μ -> γ -> γ)
  (ax' : μ' -> γ -> γ)
  : μ ⊕ μ' -> γ -> γ :=
  Sum.elim ax ax'


def BiTamb'd
  (monobj monhom tensorObj obj hom)
  (actionₗ actionᵣ actionₗ' actionᵣ' : μ -> γ -> γ)
  [Category obj hom]
  [Category monobj monhom]
  [MonoidalCategory monobj monhom tensorObj]
  [Liftable monobj obj obj actionₗ]
  [MonoidalAction monobj monhom tensorObj obj hom actionₗ]
  [Liftable monobj obj obj actionᵣ]
  [MonoidalAction monobj monhom tensorObj obj hom actionᵣ]
  [Liftable monobj obj obj actionₗ']
  [MonoidalAction monobj monhom tensorObj obj hom actionₗ']
  [Liftable monobj obj obj actionᵣ']
  [MonoidalAction monobj monhom tensorObj obj hom actionᵣ']
  (α β ς τ : γ)
  := (p : _) -> [Tambara monobj monhom tensorObj obj hom actionₗ actionᵣ p] -> [Tambara monobj monhom tensorObj obj hom actionₗ' actionᵣ' p] -> p α β -> p ς τ


def toBiTamb'd
  [Category obj hom]
  [Category monobj monhom]
  [MonoidalCategory monobj monhom tensorObj]
  [Liftable monobj obj obj actionₗ]
  [MonoidalAction monobj monhom tensorObj obj hom actionₗ]
  [Liftable monobj obj obj actionᵣ]
  [MonoidalAction monobj monhom tensorObj obj hom actionᵣ]
  [Liftable monobj obj obj actionₗ']
  [MonoidalAction monobj monhom tensorObj obj hom actionₗ']
  [Liftable monobj obj obj actionᵣ']
  [MonoidalAction monobj monhom tensorObj obj hom actionᵣ']
  : ProfOptic monobj monhom tensorObj obj hom actionₗ actionᵣ δ ω ς τ ->
  ProfOptic monobj monhom tensorObj obj hom actionₗ' actionᵣ' α β δ ω ->
  BiTamb'd monobj monhom tensorObj obj hom actionₗ actionᵣ  actionₗ' actionᵣ' α β ς τ
  := fun xprofopt yprofopt p _ _ => xprofopt p ∘ yprofopt p

abbrev DistributiveLaw_aux
  (ax : μ -> γ -> γ)
  (ax' : μ' -> γ -> γ)
  (F : μ × μ' -> μ' × μ)
  : μ -> μ' -> γ -> γ
  := fun M N A => have := F (M, N); ax' this.fst (ax this.snd A)

class DistributiveLaw
  (monobj monhom tensorObj)
  (ax : μ -> γ -> γ)
  (monobj' monhom' tensorObj')
  (ax' : μ' -> γ -> γ)
  (obj hom)
  [Category obj hom]
  [Category monobj monhom]
  [MonoidalCategory monobj monhom tensorObj]
  [Liftable monobj obj obj ax]
  [MonoidalAction monobj monhom tensorObj obj hom ax]
  [Category monobj' monhom']
  [MonoidalCategory monobj' monhom' tensorObj']
  [Liftable monobj' obj obj ax']
  [MonoidalAction monobj' monhom' tensorObj' obj hom ax']
  (F : μ × μ' -> μ' × μ)
  where
    distribute : hom (ax M (ax' N A)) (DistributiveLaw_aux ax ax' F M N A)

/- instance : DistributiveLaw Trivial (· -> ·) Prod Prod Trivial (· -> ·) Sum Sum Trivial (· -> ·) (fun x => (x.fst, x.snd)) where -/
/-   distribute := by simp [DistributiveLaw_aux]; exact -/
/-     fun x => _ -/

@[reducible]
def BiTambTensorObj
  (tensorObja : μ -> μ -> μ)
  (tensorObjb : μ -> μ -> μ)
  : μ × μ -> μ × μ -> μ × μ
  := fun p q => (tensorObja p.fst q.fst, tensorObjb p.snd (tensorObja p.fst q.snd))

instance
  {γ : Type v}
  {monobj : γ -> Type u}
  {tensorObja : γ -> γ -> γ}
  {tensorObjb : γ -> γ -> γ}
  [lifta : Liftable monobj monobj monobj tensorObja]
  [liftb : Liftable monobj monobj monobj tensorObjb]
  : Liftable (productObj monobj) (productObj monobj) (productObj monobj) (BiTambTensorObj tensorObja tensorObjb)
  where
    lift := (lifta.lift, liftb.lift)

instance
  {γ : Type v}
  {monobj : γ -> Type u}
  {monhom : γ -> γ -> Type u}
  {tensorObja : γ -> γ -> γ}
  {tensorObjb : γ -> γ -> γ}
  [Category monobj monhom]
  [cata : MonoidalCategory monobj monhom tensorObja]
  [catb : MonoidalCategory monobj monhom tensorObjb]
  : Bifunctor (productObj monobj) (productHom monhom) (productObj monobj) (productHom monhom) (productObj monobj) (productHom monhom) (BiTambTensorObj tensorObja tensorObjb)
  where
    map := fun f g => (cata.map f.fst g.fst, catb.map f.snd (cata.map f.fst g.snd))

instance
  : MonoidalCategory (productObj Trivial) (productHom (· -> ·)) (BiTambTensorObj Sum Prod)
  where
    tensorUnit := (Empty, Unit)
    associator := (Sum.elim 
      (Sum.elim (fun x => .inl x) (fun x => .inr (.inl x))) 
      (fun x => .inr (.inr x)), 
      fun ((a, b), c) => 
        (a, 
        b.elim 
          .inl 
          (fun y => c.elim 
            (Sum.elim 
              .inl 
              (fun y' => .inr (y, .inl y'))) 
            (fun z => .inr (y, .inr z)))))
    associator_inv := (Sum.assoc, fun (a, b) => ((a, b.elim .inl fun c => .inr c.fst), b.elim (fun x => .inl (.inl x)) (fun (_, e) => e.elim (fun y => .inl (.inr y)) .inr)))
    leftUnitor := (Sum.elim Empty.elim id, fun (_, p) => p.elim Empty.elim id)
    leftUnitor_inv := (.inr, fun x => (.unit, .inr x))
    rightUnitor := (Sum.elim id Empty.elim, Prod.fst)
    rightUnitor_inv := (.inl, fun x => (x, .inr .unit))

instance 
  : Bifunctor (productObj Trivial) (productHom (· -> ·)) Trivial (· -> ·) Trivial (· -> ·) (fun (s, t) α => s ⊕ t × α)
  where
    map := fun f g => Sum.elim (fun x => .inl (f.fst x)) (fun (y, z) => .inr (f.snd y, g z))

