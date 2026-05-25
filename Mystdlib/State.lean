import Mystdlib.Optics.Tambara

open Std

variable {m : Type u -> Type v} [Monad m]

open Tamb

class LensClass (α : outParam (Type u)) (ς : Type u) where
  lens : Lens' α ς

class MonadStateOfLens (α : semiOutParam (Type u)) (m : Type u -> Type v)  where
  getOfLens : m α
  setOfLens : α -> m PUnit
  modifyGetOfLens : {γ : Type u} -> (α -> γ × α) -> m γ
export MonadStateOfLens (getOfLens setOfLens modifyGetOfLens)

instance [inst : MonadStateOf ς m] : MonadStateOfLens ς m where
  getOfLens := inst.get
  setOfLens := inst.set
  modifyGetOfLens := inst.modifyGet


instance {α ς : Type} {m : Type -> Type} [Monad m] [LensClass α ς] [MonadStateOfLens ς m] : MonadStateOfLens α m where
  getOfLens := do let s <- getOfLens (α := ς); return LensClass.lens.view s
  setOfLens := fun w => do let s <- getOfLens (α := ς); setOfLens <| LensClass.lens.over (fun _ => w) s
  modifyGetOfLens := fun f => modifyGetOfLens (α := ς) fun s => (Prod.fst (f (LensClass.lens.view s)), LensClass.lens.over (Prod.snd ∘ f) s)

open Lean

instance : LensClass MessageLog Core.State where
  lens := .mk Core.State.messages (fun s msgLog => { s with messages := s.messages ++ msgLog })
  
instance : LensClass MessageLog Elab.Command.State where
  lens := .mk Elab.Command.State.messages (fun s msgLog => { s with messages := s.messages ++ msgLog})




