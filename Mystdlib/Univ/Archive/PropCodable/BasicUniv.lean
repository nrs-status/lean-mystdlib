import Mystdlib.Univ.PropCodable.Basic


namespace BasicUniv
@[simp]
def codeNodesImpl : Finset String := {"nat", "bool", "unit", "empty", "string", "format", "syntax", "name", "array", "list"}

@[simp]
def aritiesImpl : codeNodesImpl∋ -> Type :=
  fun ⟨str, _⟩ => if str ∈ ({"array", "list"} : Finset String)
  then Unit
  else Empty

@[grind, simp]
def decodeImpl : (σ : codeNodesImpl∋) -> (aritiesImpl σ -> Type) -> Type :=
  fun ⟨str, is_elm⟩ cont => if h : str = "nat"
  then Nat
  else if h : str = "bool"
  then Bool
  else if h : str = "unit"
  then Unit
  else if h : str = "empty"
  then Empty
  else if h : str = "string"
  then String
  else if h : str = "format"
  then Std.Format
  else if h : str = "syntax"
  then Lean.Syntax
  else if h : str = "name"
  then Lean.Name
  else if h : str = "array"
  then Array (cont (cast ?_ Unit.unit))
  else if h : str = "list"
  then List (cont (cast ?_ Unit.unit))
  else ?_
where finally
  · simp_all
  · simp_all
  · exfalso
    simp at is_elm
    grind


@[reducible]
def _root_.BasicUniv : Univ where
  codeNodes := BasicUniv.codeNodesImpl
  arities := BasicUniv.aritiesImpl
  decode := BasicUniv.decodeImpl


instance {σ : BasicUniv.codeNodes∋} : Encodable (BasicUniv.arities σ)  := by
  simp [BasicUniv]
  split <;> infer_instance
instance {σ : BasicUniv.codeNodes∋} : Fintype (BasicUniv.arities σ) := by
  simp [BasicUniv]
  split <;> infer_instance

instance : Encodable BasicUniv.Code := by
  simp [Univ.Code]
  apply @WType.instEncodable _ _ _ (fun a => BasicUniv.instEncodableArities)

instance : DecidableEq BasicUniv.Code := Encodable.decidableEqOfEncodable _



instance : Codable Nat BasicUniv nat# where

instance : Codable Bool BasicUniv bool# where

instance : Codable Lean.Syntax BasicUniv (.mk "syntax"<: (fun x => Empty.elim x)) where

instance : Codable Empty BasicUniv empty# where

instance : Codable Unit BasicUniv unit# where

instance : Codable String BasicUniv string# where

instance : Codable Std.Format BasicUniv format# where

instance : Codable Lean.Name BasicUniv name# where

instance [inst : Codable α BasicUniv code] : Codable (Array α) BasicUniv (.mk "array"<: (fun _ => code)) where
  wf := by
    have := inst.wf
    simp [Univ.Code.decode, decodeImpl] at *
    grind

instance [inst : Codable α BasicUniv code] : Codable (List α) BasicUniv (.mk "list"<: (fun _ => code)) where
  wf := by
    have := inst.wf
    simp [Univ.Code.decode, decodeImpl] at *
    grind


end BasicUniv


