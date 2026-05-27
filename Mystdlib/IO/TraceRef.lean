import Std
import Lean
import Mystdlib.Univ.MetaUniv
import Mystdlib.IO.Misc
import Mystdlib.Reader
import Mystdlib.Writer

/-
unsafe, impure version of TagFormatT
-/

open Std

namespace TraceRef

initialize tref : IO.Ref (DHashMap (List String × MetaUniv.Code) (·.snd.decode)) <-
  IO.mkRef {}


variable [Monad m] [MonadLiftT (ST IO.RealWorld) m]

def reset : m Unit :=
  tref.set {}

def TraceT (m : Type -> Type) (α : Type) := ReaderT (List String -> List String) m α

section

local macro "infer" : term => return (<- `(by unfold TraceT; infer_instance))

instance : Monad (TraceT m) := infer

instance : MonadReader (List String -> List String) (TraceT m) := infer

instance : MonadLift m (TraceT m) := infer

instance : MonadControl m (TraceT m) := infer

open Lean

instance  [MonadRef m] : MonadRef (TraceT m) := infer

instance  [MonadQuotation m] : MonadQuotation (TraceT m) := infer

instance  [Lean.AddErrorMessageContext m] : Lean.AddErrorMessageContext (TraceT m) := infer

instance [MonadError m] : MonadError (TraceT m) := infer

instance [MonadRecDepth m] : MonadRecDepth (TraceT m) := infer

end

instance : MonadLiftT (TraceT m) m where
  monadLift := fun xm => xm id

def insert (k : List String) (enc : MetaUniv.Code) (v : enc.decode) : TraceT m Unit := do
  tref.modify (·.insert ((<- read) k, enc) v)


def getEntire : m (DHashMap (List String × MetaUniv.Code) (·.snd.decode)) :=
  tref.get

open Lean Elab Command

def Formatter := List String -> (enc : MetaUniv.Code) -> enc.decode -> Option (CommandElabM Format)


def Formatter.mk (pred : List String -> Bool) (enc : MetaUniv.Code) (format : enc.decode -> CommandElabM Format) : Formatter :=
  fun l enc' dek => if h : pred l ∧ enc = enc'
  then format (cast (by grind) dek)
  else .none

def Formatter.else (x y : Formatter) : Formatter :=
  fun l enc dek => match x l enc dek with
  | .some x => x
  | .none => y l enc dek

def Formatter.first (l : List Formatter) : Formatter :=
  fun l' enc dek => match l with
  | .nil => .none
  | .cons x xs => x.else (recur xs) l' enc dek

def Formatter.prefixing (prefix_ : List String) :=
  Formatter.mk (prefix_.IsPrefix ·)

def trace (format : Formatter) (termPath : String) : CommandElabM Unit := do
  let hm <- getEntire
  for i in hm do match format i.fst.fst i.fst.snd i.snd with
  | .none => continue
  | .some x => printToTerminal termPath (toString (<- x))


