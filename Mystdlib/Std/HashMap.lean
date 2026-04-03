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

end
