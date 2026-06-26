import Lean
import Mystdlib.Univ.PropCodable.BasicUniv


open Lean Core Meta Elab Term Command

namespace MetaUniv

@[simp]
def codeNodes_extension : Finset String :=
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


instance : Codable Lean.Expr Extension expr# where


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

instance [inst : Codable α MetaUniv code] : Codable (CoreM α) MetaUniv (.mk "corem"<: fun _ => code
) where
  wf := by
    have := inst.wf
    simp [MetaUniv.decode_extension]
    congr

instance [inst : Codable α MetaUniv code] : Codable (MetaM α) MetaUniv (.mk "metam"<: fun _ => code) where
  wf := by
    have := inst.wf
    simp [Univ.merge, merge_decode, MetaUniv.decode_extension]
    congr

instance [inst : Codable α MetaUniv code] : Codable (TermElabM α) MetaUniv (.mk "termelabm"<: fun _ => code) where
  wf := by
    have := inst.wf
    simp [Univ.merge, merge_decode, MetaUniv.decode_extension]
    congr

instance [inst : Codable α MetaUniv code] : Codable (CommandElabM α) MetaUniv (.mk "commandelabm"<: fun _ => code) where
  wf := by
    have := inst.wf
    simp [Univ.merge, merge_decode, MetaUniv.decode_extension]
    congr

instance [Codable α BasicUniv code] : Codable α MetaUniv (code_merge_lift_left code) := inferInstance

/- instance [Codable α MetaUniv (code_merge_lift_left (.mk str cont))] : Codable α MetaUniv (.mk _ cont) where -/


#synth Codable Nat MetaUniv (code_merge_lift_left nat#)

class ZeroArity (univ : Univ) (codeNode : String) where
  is_code_node : codeNode ∈ univ.codeNodes
  zero_arity : univ.arities ⟨codeNode, is_code_node⟩ = Empty

instance [Codable α BasicUniv (.mk ⟨str, h⟩ cont)] : Codable α MetaUniv (.mk ⟨str, h'⟩ cont) :=
  _

#synth Codable Nat MetaUniv nat#

class CodeEquiv (x y : Univ) (code : x.Code) (code' : y.Code) where


