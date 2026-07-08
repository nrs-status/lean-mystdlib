import Std
import Lean
import Mystdlib.IO.Misc
import Mystdlib.StateRefT
import Mystdlib.Writer
import Mystdlib.DMap.Map.Defs
import Mystdlib.DMap.Map.Lemmas

/-
an attempt at a pure TraceRef, so that we can parametrize the Ref hashmap's keys
-/

open Std

abbrev TraceT [BEq γ] (ρ : DMap γ β -> Prop) (μ : Type -> Type) (α : Type) :=
  StateRefT' IO.RealWorld { db // ρ db } μ α

variable [BEq γ] {ρ : DMap γ β -> Prop} [Monad μ] [MonadLiftT (ST IO.RealWorld) μ]

/-
section

local macro "infer" : term => return (<- `(by unfold TraceT; infer_instance))

instance : Monad (TraceT ρ μ) := infer

instance : MonadLift μ (TraceT ρ μ) := infer

instance : MonadControl μ (TraceT ρ μ) := infer

instance  : MonadStateOf { db // ρ db } (TraceT ρ μ) := infer

open Lean

instance  [MonadRef μ] : MonadRef (TraceT ρ μ) := infer

instance  [MonadQuotation μ] : MonadQuotation (TraceT ρ μ) := infer

instance  [Lean.AddErrorMessageContext μ] : Lean.AddErrorMessageContext (TraceT ρ μ) := infer

instance [MonadError μ] : MonadError (TraceT ρ μ) := infer

instance [MonadRecDepth μ] : MonadRecDepth (TraceT ρ μ) := infer

end
-/

namespace TraceT

def run (x : TraceT ρ μ α) (s : { m // ρ m }) : μ (α × { m // ρ m }) :=
  StateRefT'.run x s

def getValueCast [LawfulBEq γ] (k : γ) (h : ∀σ : { m // ρ m }, k ∈ σ.val) : TraceT ρ μ (β k) := do
  let m <- get
  return m.val.get k (h _)

def modifyKey [LawfulBEq γ] (k : γ) (f : β k -> β k) (h : ∀σ : { m // ρ m }, ρ (σ.val.modifyKey k f)) : TraceT ρ μ Bool := do
  let m <- get
  if h' : k ∈ m.val
  then
    set (σ := { m // ρ m }) ⟨m.val.modifyKey k f, h _⟩
    return .true
  else return .false

def modifyGet [LawfulBEq γ] (k : γ) (f : β k -> β k) (h1 : ∀σ : { m // ρ m }, k ∈ σ.val) (h2 : ∀σ : { m // ρ m }, ρ (σ.val.modifyKey k f)) : TraceT ρ μ (β k) := 
  MonadState.modifyGet fun σ => (f <| σ.val.get k (h1 _), ⟨σ.val.modifyKey k f, h2 _⟩)

def insertEntry? [PartialEquivBEq γ] [DecidablePred ρ] (k : γ) (v : β k) : TraceT ρ μ Bool := do
  let m <- get
  if h : k ∈ m.val
  then 
    if h' : ρ (m.val.insertEntry k v)
    then
      set (σ := { m // ρ m }) ⟨m.val.insertEntry _ _, h'⟩
      return .true
    else return .false
  else return .false

def insertList?Aux [PartialEquivBEq γ] [DecidablePred ρ] (l : List ((k : γ) × β k)) (acc : Nat) : TraceT ρ μ Nat :=
  match l with
  | [] => return acc
  | x :: xs => do
    let r <- insertEntry? x.1 x.2
    insertList?Aux xs (ite r acc acc.succ)

def insertList? [PartialEquivBEq γ] [DecidablePred ρ] (l : List ((k : γ) × β k)) : TraceT ρ μ Nat :=
  insertList?Aux l 0

end TraceT

open Lean Elab Command

def Formatter (γ : Type u) (β : γ -> Type v) := (k : γ) -> β k -> Option (CommandElabM Format)


def Formatter.else (x y : Formatter γ β) : Formatter γ β :=
  fun k v => match x k v with
  | .some x => x
  | .none => y k v

def Formatter.ofList (l : List (Formatter γ β)) : Formatter γ β :=
  match l with
  | .nil => fun _ _ => .none
  | .cons x xs => x.else (.ofList xs)


def trace (format : Formatter γ β) (termPath : String) : TraceT ρ CommandElabM Unit := do
  let s <- get
  s.val.forM fun k v => match format k v with
  | .none => return
  | .some x => do printToTerminal termPath (toString (<- x))




