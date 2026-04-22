import Mathlib.Control.Bifunctor
import Mathlib.Control.Traversable.Basic
import Std

open Std

class Profunctor (p : Type _ -> Type _ -> Type _) where
  map : (ς -> α) -> (β -> τ) -> p α β -> p ς τ

structure ActionPair.{u ,v} where
  left : Type u -> Type v -> Type v
  right : Type u -> Type v -> Type v

class Tamb (pair : ActionPair) (p : Type u -> Type u -> Type w)
  extends Profunctor p
  where
  tamb : p α β  -> p (pair.left μ α) (pair.right μ β)

class Tambs (actions : List ActionPair) (p : Type u -> Type u -> Type w)  
  extends Profunctor p
  where
    tambs : (i : Fin actions.length) -> Tamb actions[i] p

instance [inst : Tamb pair p] : Tambs [pair] p where
  tambs := fun | 0 => by dsimp; infer_instance

instance 
  [inst : Tambs (pair :: axs) p] 
  [inst' : Tamb pair' p] 
  : Tambs (pair :: pair' :: axs) p where
    tambs := fun fin =>
      if h : fin.val = 0 then by
        have := inst.tambs ⟨0, by grind⟩
        dsimp at this
        simp [h]
        exact this
      else if h' : fin.val = 1 then by
        simp [h']
        exact inst'
      else by
        have : (pair :: pair' :: axs)[fin] = (pair :: axs)[fin.pred (by simp_all)] := by grind
        rw [this]
        exact inst.tambs (fin.pred (by grind))

def ProfOptic (actions : List ActionPair) (α β ς τ : Type _) :=
  (p : _) -> [Tambs actions p] -> p α β -> p ς τ

def ProfOptic.compose_aux
  (tambs : Tambs (l ++ l') p)
  : Tambs l p × Tambs l' p :=
   let fst : Tambs l p := 
    have {n : Nat} (h : n = l.length) : n ≤ (l ++ l').length := by simp_all
    have {i : Fin l.length} : l[i] = (l ++ l')[Fin.castLE (this rfl) i] := by grind
    ⟨fun i => by rw [this]; exact tambs.tambs (Fin.castLE _ i)⟩
   let snd : Tambs l' p :=
      have {i : Fin l'.length} : l'[i] = (l ++ l').get ⟨l.length + i.val, by grind⟩ := by grind
      ⟨fun i => by rw [this]; exact tambs.tambs ⟨l.length + i.val, by grind⟩⟩
   (fst, snd)

def ProfOptic.compose
  (x : ProfOptic l δ ω ς τ)
  (y : ProfOptic l' α β δ ω)
  : ProfOptic (l ++ l') α β ς τ :=
  fun p tambs =>
    have := ProfOptic.compose_aux tambs
    have f := @x p ⟨fun i => this.fst.tambs i⟩
    have g := @y p ⟨fun i => this.snd.tambs i⟩
    f ∘ g

inductive ExOptic
  (pair : ActionPair)
  (α β ς τ : Type _)
| mk : (ς -> pair.left μ α) -> (pair.right μ β -> τ) -> ExOptic pair α β ς τ

def ExOptic.toProfOptic
  (x : ExOptic pair α β ς τ)
  : ProfOptic [pair] α β ς τ :=
  match x with
  | .mk l r => fun _ inst =>
    inst.map l r ∘ (inst.tambs 0).tamb

def Lens (α β ς τ : Type u) := ProfOptic [⟨Prod, Prod⟩] α β ς τ

def Lens.mk
  (get : ς -> α)
  (set : ς -> β -> τ)
  : Lens α β ς τ
  := fun {_} tambs =>
    tambs.map (fun s => (s, get s)) (Function.uncurry set) ∘ (tambs.tambs 0).tamb

def Lens' (α ς) := Lens α α ς ς

def Prism (α β ς τ : Type u) := ProfOptic [⟨Sum, Sum⟩] α β ς τ

def Prism.mk
  (build : β -> τ)
  (matchfn : ς -> τ ⊕ α)
  : Prism α β ς τ
  := fun {_} tambs =>
    tambs.map matchfn (Sum.elim id build) ∘ (tambs.tambs 0).tamb

def App (C : (Type u -> Type v) -> Type w) :=
  fun (σ : ΣF, C F) (α : _) => σ.fst α

