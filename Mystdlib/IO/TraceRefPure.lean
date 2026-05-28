import Std
import Lean
import Mystdlib.IO.Misc
import Mystdlib.StateRefT
import Mystdlib.Writer

/-
an attempt at a pure TraceRef, so that we can parametrize the Ref hashmap's keys
-/

open Std

def TraceT  {ξ : Type} [BEq ξ] [Hashable ξ] (β : ξ -> Type) (ρ : (DHashMap ξ β) -> Prop) (m : Type -> Type) (α : Type) :=
  StateRefT' IO.RealWorld { hm : DHashMap ξ β // ρ hm } m α

variable {ξ : Type} [BEq ξ] [Hashable ξ] {β : ξ -> Type} {ρ : (DHashMap ξ β) -> Prop} [Monad m] [MonadLiftT (ST IO.RealWorld) m]

section

local macro "infer" : term => return (<- `(by unfold TraceT; infer_instance))

instance : Monad (TraceT β ρ m) := infer

instance : MonadLift m (TraceT β ρ m) := infer

instance : MonadControl m (TraceT β ρ m) := infer

instance  : MonadStateOf { hm : DHashMap ξ β // ρ hm } (TraceT β ρ m) := infer

open Lean

instance  [MonadRef m] : MonadRef (TraceT β ρ m) := infer

instance  [MonadQuotation m] : MonadQuotation (TraceT β ρ m) := infer

instance  [Lean.AddErrorMessageContext m] : Lean.AddErrorMessageContext (TraceT β ρ m) := infer

instance [MonadError m] : MonadError (TraceT β ρ m) := infer

instance [MonadRecDepth m] : MonadRecDepth (TraceT β ρ m) := infer

end

namespace TraceT


def insert? [DecidablePred ρ] (key : ξ) (xbkey : β key) : TraceT β ρ m Bool := do
  let s <- get
  if h : ρ (s.val.insert key xbkey)
  then 
    set (σ := { hm : DHashMap ξ β // ρ hm }) ⟨s.val.insert key xbkey, h⟩
    return .true
  else return .false

def insert (key : ξ) (xbkey : β key) (h : ∀(s : { hm // ρ hm }), ρ (s.val.insert key xbkey)) : TraceT β ρ m Unit :=
  modify (fun hm => ⟨hm.val.insert key xbkey, h hm⟩)

def insertMany [ForIn Id γ ((key : ξ) × β key)] (l : γ) (h : ∀(s : { hm // ρ hm }), ρ (s.val.insertMany l)) : TraceT β ρ m Unit :=
  modify (fun hm => ⟨hm.val.insertMany l, h hm⟩)




end TraceT

open Lean Elab Command

variable (β) in
def Formatter := (key : ξ) -> β key -> Option (CommandElabM Format)

def Formatter.mk (pred : ξ -> Bool) (format : (key' : ξ) -> pred key' -> β key' -> CommandElabM Format) : Formatter β :=
  fun key' xbkey' =>
    if h : pred key'
    then format key' h xbkey'
    else .none

def Formatter.else (x y : Formatter β) : Formatter β :=
  fun k xbkey => match x k xbkey with
  | .some x => x
  | .none => y k xbkey

def Formatter.ofList (l : List (Formatter β)) : Formatter β :=
  match l with
  | .nil => fun _ _ => .none
  | .cons x xs => x.else (.ofList xs)


def trace (format : Formatter β) (termPath : String) : TraceT β ρ CommandElabM Unit := do
  let s <- get
  for i in s.val do match format i.fst i.snd with
  | .none => continue
  | .some x => printToTerminal termPath (toString (<- x))


