import Lean
import Mystdlib.Tactics
import Mystdlib.Foldable
import Mystdlib.Writer
import Mystdlib.Univ.Basic

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

class HasFormattingIn (tag : Name) (α : Type u) (m : Type -> Type v) where
  format : α -> m Std.Format

def TagFormatT (univ : Univ) (m : Type _ -> Type _) (α : Type _) := 
  ReaderT ((tag : Name) -> (enc : Rose univ.arities) -> univ.decode enc -> HasFormattingIn tag (univ.decode enc) m -> Std.Format) m α

instance [Monad m] : Monad (TagFormatT univ m) where
  pure := fun a f => pure a
  bind := fun xm xf f => do
    let r <- xm f
    (xf r) f

instance [Monad m] : MonadReader ((tag : Name) -> (enc : Rose univ.arities) -> univ.decode enc -> HasFormattingIn tag (univ.decode enc) m -> Std.Format) (TagFormatT univ m) where
  read := fun f => pure f


def log [Monad m] [AddMessageContext m] [MonadLog m] [MonadOptions m] (tag : Name) (target : α) [Codable α univ] [HasFormattingIn tag α m] (severity := MessageSeverity.information) : TagFormatT univ m Unit := fun f =>
  have := Eq.symm (Codable.wf (α := α) (univ := univ))
  let target_as_coded : univ.decode (Codable.encode α) := this ▸ target
  have : HasFormattingIn tag (univ.decode (Codable.encode α)) m := this ▸ inferInstance
  Lean.log (.tagged tag (.ofFormat (f tag (Codable.encode α) target_as_coded inferInstance))) severity


