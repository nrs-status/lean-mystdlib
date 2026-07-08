import Mathlib.Data.List.Nodup
import Mystdlib.General
import Std

open Std

section
variable 
  {α β : Type}
  [BEq α]
  [LawfulBEq α]
  [Hashable α]


def Std.HashMap.keys_attach (b : Std.HashMap α β) : List { x // b.contains x } :=
  b.keys.attachWith _ (by grind)

def Std.HashMap.keysArray_attach (b : Std.HashMap α β) : Array { x // b.contains x } :=
  b.keysArray.attachWith _ (by simp)

def Std.HashMap.values_attach (b : Std.HashMap α β) 
  : Array <| (σ : { k // b.contains k }) × { v // v = b.get σ.1 σ.2 } 
  := b.keysArray_attach.map fun σ => ⟨σ, (b.get σ.1 σ.2)<:⟩

def Std.HashMap.foldl_attaching
  (b : Std.HashMap α β)
  (f : γ -> 
    (σ : { x : α // b.contains x }) -> 
    { x : β // x = b.get σ.1 σ.2 } -> γ)
  (init : γ)
  : γ :=
   b.values_attach.foldl (fun xγ ⟨kσ, vσ⟩ => f xγ kσ vσ) init

/-
Std.HashMap.mem_toList_iff_getElem?_eq_some
-/
namespace Std.HashMap
def attach (hm : Std.HashMap α β) : Std.HashMap { x // x ∈ hm } β :=
  .ofList (hm.toList.pmap (P := fun pair => pair.fst ∈ hm) (fun x y => ⟨⟨x.fst, !p⟩, x.snd⟩) !p)

theorem attach_size
  {hm : HashMap α β}
  : hm.attach.size = hm.size := by
    simp [attach]
    rw [Std.HashMap.size_ofList]
    · simp
    · simp 
      apply List.Nodup.pairwise_of_forall_ne 
      · apply List.Nodup.pmap
        · grind
        · apply List.Nodup.of_map (f := Prod.fst)
          rw [Std.HashMap.map_fst_toList_eq_keys ]
          simp [HashMap.nodup_keys]
      · grind





