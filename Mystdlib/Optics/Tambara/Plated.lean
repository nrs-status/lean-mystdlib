import Mystdlib.Optics.Tambara.Combinators
import Mystdlib.Optics.Tambara.Optics
import Mystdlib.Optics.Tambara.Traversal
import Mathlib.Data.List.TakeWhile

namespace Tamb

class Plated α where
  plate : Traversal' α α

def children
  [Plated α]
  : α -> Σn, Vector α n
  := (fun b => ⟨b.length, b.elements⟩) ∘ Plated.plate.extract

def context
  [Plated α]
  : α -> Σn, Vector α n -> α
  := (fun b => ⟨b.length, b.continuation⟩) ∘ Plated.plate.extract


partial def univ
  [Plated α]
  : α -> Σn, Vector α n
  := fun a =>
    let := children a
    if this.fst = 0 then ⟨1, #v[a]⟩
    else
      let self_n_subchildren := this.snd.toArray.map recur |>.foldl (fun acc next => acc ++ next.snd.toArray) #[a]
      ⟨_, self_n_subchildren<:⟩
    
partial def transform
  [Plated α]
  (f : α -> α)
  (a : α)
  : α 
  :=
    let ⟨_, elms, cont⟩ := Plated.plate.extract (f a)
    cont (elms.map (transform f))

def collect
  [Plated α]
  (p : α -> Bool)
  : α -> Array α
  := fun a =>
    (univ a).snd.toArray.filter p

def until_including_extract [Plated α] (p : α -> Bool) (a : α) : Bazaar α α α :=
  if p a
  then ⟨1, #v[a], Vector.head⟩
  else
    let ⟨len, elms, cont⟩ := Plated.plate.extract a
    let left := (elms.toList.dropWhile p).drop 1
    let left_v : Vector α left.length := ⟨left.toArray, rfl⟩
    let passed : Array α := elms.toArray.take (len - left.length)
    have makes_cont_arg : passed.size + left.length = len := by
      grind [List.length_dropWhile_le]
    ⟨passed.size, ⟨passed, rfl⟩, fun v => cont (makes_cont_arg ▸ (v ++ left_v))⟩

def until_excluding_extract
  (x : Traversal' α α)
  (p : α -> Bool)
  (a : α)
  : Bazaar α α α
  := 
  if p a 
  then ⟨0, #v[], fun _ => a⟩
  else
    let ⟨len, elms, cont⟩ := x.extract a
    let left := elms.toList.dropWhile p
    let left_v : Vector α left.length := ⟨left.toArray, rfl⟩
    let passed : Array α := elms.toArray.take (len - left.length)
    have makes_cont_arg : passed.size + left.length = len := by
      grind [List.length_dropWhile_le]
    ⟨passed.size, ⟨passed, rfl⟩, fun v => cont (makes_cont_arg ▸ (v ++ left_v))⟩

/-
partial def findSkippingNestedOnHit_aux [Plated α] :=
  Plated.plate.sequence (α := α) (F := StateM (List (α -> Bool) × Array α))
    fun a => do
      let (ps, _) <- get
      if h : ps.isEmpty
      then return
      else
        let p := ps.head (by grind)
        if p a
        then modifyGet (fun (ps', ss) => (.unit, (ps'.tail, ss.push a)))
        else
          let r' := Plated.plate.toListOf a
          let r'' := r'.dropWhile (¬ p ·)
          match r'' with
          | .nil => 
            r'.forM recur
          | .cons x xs =>
            modify fun (ps', ss) => (ps'.tail, ss.push x)
            xs.forM recur

def findSkippingNestedOnHit [Plated α] (p : List (α -> Bool)) (a : α) :=
  findSkippingNestedOnHit_aux a (p, #[]) |>.snd.snd
-/


partial def findSkippingNestedOnHit_aux [Plated α] :=
  Plated.plate.sequence (F := StateM (List (α -> Bool) × Array α))
    fun a => do
      let (ps, _) <- get
      if h : ps.isEmpty then return else
      let p := ps.head (by grind)
      if p a then modify (fun (ps', ss) => (ps'.tail, ss.push a)) else
      Plated.plate.sequence recur a

def findSkippingNestedOnHit [Plated α] (p : List (α -> Bool)) (a : α) : Array α :=
  findSkippingNestedOnHit_aux a (p, #[]) |>.snd.snd
