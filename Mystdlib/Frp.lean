import Std

open Std

/- def mkTriggerListeners := fun parent_nm parent_out_ref ls_ref => -/
/-   fun _ => ls_ref.map fun x => x.f x.listener_out_atm x.listener's_trigger_listeners -/

def mkSubscribe := fun emitter_nm emitter_ls_ref =>
  fun new_listener_nm new_listener_out_ref new_listener's_trigger_listeners new_listener's_on_tirgger =>
    sorry

inductive Univ | nat | bool | array (uα : Univ)

def Univ.decode : Univ -> Type
| .nat => Nat
| .bool => Bool
| .array uα => Array uα.decode

def Frp (α : Type) := StateM (HashMap String (Σuα : Univ, uα.decode)) α

instance : MonadState (HashMap String (Σuα : Univ, uα.decode)) Frp where
  get := fun current => return (current, current)
  set := fun new current => return sorry
  modifyGet := sorry

def initSignal [Nonempty α] (nm : String) (uα : Univ) (default_val : uα.decode) : Frp Unit := 
  modify sorry
