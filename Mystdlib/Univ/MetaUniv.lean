import Lean
import Mystdlib.Mems
import Mystdlib.Univ.BasicUniv


open Lean Core Meta Elab Term Command

namespace MetaUniv

@[simp]
def codeNodes_extension : Std.HashSet String :=
  {"expr", "metam", "termelabm", "corem", "commandelabm"}

@[simp]
def arities_extension : codeNodes_extension∋ -> Type
| ⟨str, _⟩ => if str = "expr"
  then Empty
  else Unit

@[simp]
def decode_extension : (σ : codeNodes_extension∋) -> (arities_extension σ -> Type) -> Type :=
  fun ⟨str, is_elm⟩ cont => if h : str = "expr"
  then Lean.Expr
  else if h : str = "metam"
  then Lean.Meta.MetaM (cont (cast ?_ Unit.unit))
  else if h : str = "termelabm"
  then Lean.Elab.Term.TermElabM (cont (cast ?_ Unit.unit))
  else if h : str = "corem"
  then Lean.Core.CoreM (cont (cast ?_ Unit.unit))
  else if h : str = "commandelabm"
  then CommandElabM (cont (cast ?_ Unit.unit))
  else ?_
where finally
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · exfalso
    simp at is_elm
    grind

@[simp, grind]
def Extension : Univ where
  codeNodes := codeNodes_extension
  arities := arities_extension
  decode := decode_extension


instance {σ : Extension.codeNodes∋} : Encodable (Extension.arities σ)  := by
  simp [Extension]
  split; infer_instance; infer_instance

instance {σ : Extension.codeNodes∋} : Fintype (Extension.arities σ) := by
  simp [Extension]
  split; infer_instance; infer_instance

instance : Encodable Extension.Code := by
  rw [Univ.Code]
  infer_instance

instance : DecidableEq Extension.Code := Encodable.decidableEqOfEncodable _


instance : Codable Lean.Expr Extension where
  encode := expr#


end MetaUniv

@[simp, grind]
abbrev MetaUniv : Univ :=
  BasicUniv.merge MetaUniv.Extension

instance : BasicUniv.AritiesAgree MetaUniv.Extension where
  arities_agree := fun str h h' => by
    exfalso; simp_all
    grind (splits := 15)

instance : BasicUniv.DecodesAgree MetaUniv.Extension where
  decodes_agree := fun str h h' => by
    exfalso; simp_all
    grind (splits := 15)

instance [inst : Codable α MetaUniv] : Codable (CoreM α) MetaUniv where
  encode := .mk "corem"<: fun _ => inst.encode
  wf := by
    have := inst.wf
    simp [MetaUniv.decode_extension]
    congr

instance [inst : Codable α MetaUniv] : Codable (MetaM α) MetaUniv where
  encode := .mk "metam"<: fun _ => inst.encode
  wf := by
    have := inst.wf
    simp [Univ.merge, merge_decode, MetaUniv.decode_extension]
    congr

instance [inst : Codable α MetaUniv] : Codable (TermElabM α) MetaUniv where
  encode := .mk "termelabm"<: fun _ => inst.encode
  wf := by
    have := inst.wf
    simp [Univ.merge, merge_decode, MetaUniv.decode_extension]
    congr

instance [inst : Codable α MetaUniv] : Codable (CommandElabM α) MetaUniv where
  encode := .mk "commandelabm"<: fun _ => inst.encode
  wf := by
    have := inst.wf
    simp [Univ.merge, merge_decode, MetaUniv.decode_extension]
    congr



