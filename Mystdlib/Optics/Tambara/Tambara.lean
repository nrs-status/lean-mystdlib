import Mystdlib.Optics.Tambara.Categories

namespace Tamb

class Profunctor (p : Type _ -> Type _ -> Type _) where
  map {α β ς τ}  : (ς -> α) -> (β -> τ) -> p α β -> p ς τ

set_option linter.dupNamespace false in
class Tamb (pair : ActionPair μ) (p : Type u -> Type u -> Type w)
  extends Profunctor p
  where
  tamb {xμ : μ} {α β} : p α β  -> p (pair.left xμ α) (pair.right xμ β)

class Tambs.{u, v, w} (actions : List (Σ(μ : Type u), ActionPair μ)) (p : Type v -> Type v -> Type w)  
  extends Profunctor p
  where
    tambs : (i : Fin actions.length) -> Tamb actions[i].snd p

instance [inst : Tamb (μ := μ) pair p] : Tambs [⟨μ, pair⟩] p where
  tambs := fun | 0 => by dsimp; infer_instance

instance 
  [inst : Tambs (pair :: axs) p] 
  [inst' : Tamb (μ := μ) pair' p] 
  : Tambs (pair :: ⟨μ, pair'⟩ :: axs) p where
    tambs := fun fin =>
      let (eq := fineq) ⟨val, lt⟩ := fin
      if h : val = 0 then by
        have := inst.tambs ⟨0, by grind⟩
        dsimp at this
        subst h
        simp
        exact this
      else if h' : val = 1 then by
        subst h'
        exact inst'
      else by
        have : (pair :: ⟨μ, pair'⟩ :: axs)[fin] = (pair :: axs)[fin.pred (by simp_all)] := by grind
        rw [<- fineq, this]
        exact inst.tambs (fin.pred (by grind))

def ProfOptic.{u, v, w} (actions : List (Σ(μ : Type u), ActionPair μ)) (α β ς τ : Type v) :=
  (p : Type v -> Type v -> Type w) -> [Tambs actions p] -> p α β -> p ς τ


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

instance 
  [inst : Tambs l p]
  [inst' : Tambs l' p]
  : Tambs (l ++ l') p where
    tambs := fun i =>
      if h : i.val < l.length
      then
        have thisa : (l ++ l')[i] = l[i] := by grind
        have thisb := inst.tambs (Fin.castLT i h)
        ⟨by rw [thisa]; exact thisb.tamb⟩
      else
        have thisa : (l ++ l')[i] = l'.get ⟨i - l.length, by grind⟩ := by grind
        have thisb := inst'.tambs ⟨i - l.length, by grind⟩
        ⟨by rw [thisa]; exact thisb.tamb⟩


inductive ExOptic
  {μ : Type v}
  (pair : ActionPair μ)
  (α β ς τ : Type u)
| mk {xμ : μ} : (ς -> pair.left xμ α) -> (pair.right xμ β -> τ) -> ExOptic pair α β ς τ

def ExOptic.xμ
  (x : ExOptic (μ := μ) pair α β ς τ)
  : μ
  := match x with
  | .mk (xμ := xμ) _ _ => xμ

def ExOptic.left
  (x : ExOptic pair α β ς τ)
  : Σxμ, ς -> pair.left xμ α
  := match x with 
  | .mk (xμ := xμ) l _ => ⟨xμ, l⟩

def ExOptic.right
  {pair : ActionPair μ}
  (x : ExOptic pair α β ς τ)
  : Σxμ, pair.right xμ β -> τ
  := match x with
  | .mk (xμ := xμ) _ r => ⟨xμ, r⟩

def ExOptic.toProfOptic
  (x : ExOptic (μ := μ) pair α β ς τ)
  : ProfOptic [⟨μ, pair⟩] α β ς τ :=
  match x with
  | .mk l r => fun _ inst =>
    inst.map l r ∘ (inst.tambs 0).tamb

instance : Profunctor (ExOptic pair α β) where
  map := fun f g ⟨l, r⟩ => .mk (l ∘ f) (g ∘ r)

abbrev TambOfExOptic_aux {M₀ : Type v} (M₁ : M₀ -> M₀ -> Type v) (O : M₀ -> M₀ -> M₀) (pair : ActionPair M₀) (α β : Type u) := ExOptic pair α β

instance 
  {M₀ : Type v}
  {α β : Type u}
  {O : M₀ -> M₀ -> M₀}
  {M₁ : M₀ -> M₀ -> Type v}
  {pair : ActionPair M₀}
  [inst : MonoidalActionPair pair M₁ O]
  : Tamb pair (TambOfExOptic_aux M₁ O pair α β) where
    tamb := fun ⟨l, r⟩ =>
      ExOptic.mk 
        (inst.left_ax.multiplicator.hom ∘ inst.left_ax.toBifunctor.map inst.cat.id l) 
        (inst.right_ax.toBifunctor.map inst.cat.id r ∘ inst.right_ax.multiplicator.inv)


def ProfOptic.toExOptic
  {α β ς τ : Type u}
  {M₀ : Type v}
  (pair : ActionPair M₀)
  (M₁ : M₀ -> M₀ -> Type v)
  (O)
  [inst : MonoidalActionPair pair M₁ O]
  (x : ProfOptic [⟨M₀, pair⟩] α β ς τ)
  : ExOptic pair α β ς τ
  := x (ExOptic pair α β) (ExOptic.mk inst.left_ax.unitor.inv inst.right_ax.unitor.hom)




