import Lean
import Mystdlib.Tactics
import Mystdlib.Foldable
import Mystdlib.Writer
import Mystdlib.Univ.MetaUniv
import Mystdlib.Reader
import Batteries.Data.String.Matcher
import Mystdlib.Dynamic

open Lean

namespace Lean.MessageData

def tag (x : List Name) (y : MessageData) : MessageData :=
  match x with
  | .nil => y
  | .cons x xs => .tagged x (y.tag xs.tail)
termination_by x.length

def getTags (x : MessageData) : List Name :=
  match x with
  | .tagged nm x' => nm :: getTags x'
  | _ => []

def toMessage {m : Type -> Type} [Monad m] [MonadLog m] [AddMessageContext m] (msgData : MessageData) (severity := MessageSeverity.information) : m Message := do
  let ref <- MonadLog.getRef
  let fileMap <- getFileMap
  let pos    := ref.getPos?.getD 0
  let endPos := ref.getTailPos?.getD pos
  return {
    fileName := (<- getFileName)
    pos := fileMap.toPosition pos
    endPos := fileMap.toPosition endPos
    data := msgData
    severity
    isSilent := .false
  }

end Lean.MessageData

open Lean.MessageData

open Foldable in
def filterTagged [Filterable t] (p : List Name -> Bool) : t MessageData -> t MessageData := 
  filter (p ∘ getTags)

def withTag [Monad m] [MonadWriter MessageLog m] (tag : Name) (xm : m α) : m α := pass do
  return (<- xm, fun msgLog => { msgLog with
    reported := msgLog.reported.map (fun msg => { msg with data := .tagged tag msg.data })
    unreported := msgLog.unreported.map (fun msg => { msg with data := .tagged tag msg.data })
  })

section 

class HasFormattingIn (tag : Name) (α : Type u) (m : Type -> Type v) where
  format : α -> m Std.Format

instance [Monad m] [Repr α] : HasFormattingIn nm α m where
  format := fun a => pure (repr a)

def logTagged [Monad m] [AddMessageContext m] [MonadLog m] [MonadOptions m] (tag : Name) (target : α)  [HasFormattingIn tag α m] (severity := MessageSeverity.information) : m Unit := do
  Lean.log (.tagged tag (<- HasFormattingIn.format tag target)) severity

end

section 

def Formatter (univ : Univ) (m : Type _ -> Type _) :=
  (Name -> (enc : univ.Code) -> enc.decode -> m Std.Format)


def TagFormatT (univ : Univ) (m : Type _ -> Type _) (α : Type _) := 
  ReaderT (Formatter univ m) m α



variable [Monad m]

instance : Monad (TagFormatT univ m) where
  pure := fun a f => pure a
  bind := fun xm xf f => do
    let r <- xm f
    (xf r) f

instance : MonadReader (Formatter univ m) (TagFormatT univ m) where
  read := fun f => pure f


def TagFormatT.log [AddMessageContext m] [MonadLog m] [MonadOptions m] (tag : Name) (target : α) [Codable α univ] (severity := MessageSeverity.information) : TagFormatT univ m Unit := fun f => do
  Lean.log (.tagged tag (.ofFormat (<- f tag (Codable.encode α) (cast ?_ target)))) severity
where finally
  simp [Codable.wf]

section

local macro "infer" : term => return (<- `(by unfold TagFormatT; infer_instance))

instance : MonadLift m (TagFormatT univ m) := infer

instance : MonadControl m (TagFormatT univ m) := infer

instance  [MonadRef m] : MonadRef (TagFormatT univ m) := infer

instance  [MonadQuotation m] : MonadQuotation (TagFormatT univ m) := infer

instance  [Lean.AddErrorMessageContext m] : Lean.AddErrorMessageContext (TagFormatT univ m) := infer

instance [MonadError m] : MonadError (TagFormatT univ m) := infer

instance [MonadRecDepth m] : MonadRecDepth (TagFormatT univ m) := infer

end

def liftThe (m) [Monad m] [inst : MonadControlT m n] (xm : TagFormatT MetaUniv m (stM m n α)) (h : stM m n Format = Format := by rfl)  : TagFormatT MetaUniv n (stM m n α) := fun f =>
  liftWith (m := m) (n := n) fun lift =>
    xm fun x y z => do
      let r <- lift (f x y z)
      return (cast h r)


deriving instance BEq for Format

namespace Formatter

def formatter_unimplemented_string := "FormatterUnimplemented"

def pformatter (name_pred : Name -> Bool) (enc : MetaUniv.Code) (f : enc.decode -> m Format) : Formatter MetaUniv m := fun x y z => if h : name_pred x ∧ y = enc then f (cast (by simp_all) z) else pure formatter_unimplemented_string

def _root_.Formatter.else (x y : Formatter univ m) : Formatter univ m :=
  fun a b c => do
    let r <- x a b c
    if r == formatter_unimplemented_string then y a b c else return r


def any (l : List (Formatter univ m)) : Formatter univ m :=
  match l with
  | .nil => fun _ _ _ => return formatter_unimplemented_string
  | .cons x xs => x.else (recur xs)

def contained (s : String) : Name -> Bool :=
  fun nm => nm.toString.contains s

def prefixed (l : List Name) : Name -> Bool :=
  fun nm => l.IsPrefix nm.components

end Formatter

end
