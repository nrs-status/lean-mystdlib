import Mathlib.Data.Part
import Mystdlib.Fin
import Mathlib.Data.Fin.Tuple.Reflection



namespace FinVec

def foldl (f : α -> β -> α) (init : α) (fv : Fin n -> β) : α :=
  match n with
  | .zero => init
  | .succ _ =>
    FinVec.foldl f (f init (fv 0)) (Fin.tail fv)


def mem (fv : Fin n -> β) (b : β) : Prop :=
  ∃fin, fv fin = b

instance : Membership α (Fin n -> α) where
  mem := FinVec.mem

@[simp, grind =_]
theorem mem_iff_exists_idx
  {fv : Fin n -> β}
  {b : β}
  : (∃fin, fv fin = b) <-> b ∈ fv := by
    simp [Membership.mem, mem]

@[grind =_]
theorem mem_iff_mem_ofFn
  {fv : Fin n -> β}
  {b : β}
  : b ∈ fv <-> b ∈ List.ofFn fv := by
    simp


theorem mem_tail_mem
  {fv : Fin (Nat.succ nn) -> β}
  {b : β}
  : (b ∈ Fin.tail fv) -> b ∈ fv := by
    intro ismem
    rw [Fin.tail_def] at ismem
    simp [<- mem_iff_exists_idx] at *
    obtain ⟨fin, eq⟩ := ismem
    exists ⟨fin.val.succ, by grind⟩

def pmap {P : α -> Prop} (f : ∀a, P a -> β) : ∀fv : Fin n -> α, (∀a ∈ fv, P a) -> (Fin n -> β) :=
  fun fv h => match n with
  | .zero => nofun
  | .succ nn => Fin.cons (f (fv 0) (h _ (by grind))) (pmap f (Fin.tail fv) (by grind [mem_tail_mem]))

def attach (fv : Fin n -> β) : Fin n -> { b // b ∈ fv } :=
  fun fin => ⟨fv fin, by grind⟩

theorem idx_prop_of_mem_prop
  {fv : Fin n -> β}
  {mot : β -> Prop}
  : (∀b ∈ fv, mot b) -> ∀fin, mot (fv fin) := by
    simp [<- mem_iff_exists_idx]

theorem pmap_eq_app
  {P : α -> Prop}
  {f : ∀a : α, P a -> β}
  {fv : Fin n -> α}
  : (pmap f fv) = (fun (h : ∀a ∈ fv, P a) (fin : Fin n) => f (fv fin) (idx_prop_of_mem_prop h fin)) :=
    Fin.consInduction 
      (by simp [Fin.elim0]; grind) 
      (fun a fv' h => by
        funext; rw [pmap.eq_def]; simp; expose_names
        rw! [Fin.tail_cons, h]
        simp [Fin.cons]
        obtain ⟨v,h'⟩ := x
        induction v; simp; expose_names; simp_all
        ) 
      fv

theorem pmap_eq_ofFn_pmap
  : List.ofFn (pmap f fv h) = (List.ofFn fv).pmap f (by grind [mem_iff_mem_ofFn]) := by
    simp [List.ofFn_eq_pmap, List.pmap_pmap, pmap_eq_app]
    apply List.pmap_congr_left
    grind

    
def Univ (v : Fin n -> Type u) := Σfin, v fin 
    

    


