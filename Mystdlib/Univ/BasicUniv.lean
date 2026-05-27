import Mystdlib.Univ.Basic2


namespace BasicUniv
@[simp]
def codeNodesImpl : Std.HashSet String := {"nat", "bool", "unit", "empty", "string", "format", "syntax", "name", "array", "list"}

@[simp]
def aritiesImpl : codeNodesImpl∋ -> Type :=
  fun ⟨str, _⟩ => if str ∈ ({"array", "list"} : Std.HashSet String)
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


instance : Codable Nat BasicUniv where
  encode := nat#

instance : Codable Bool BasicUniv where
  encode := bool#

instance : Codable Lean.Syntax BasicUniv where
  encode := .mk "syntax"<: (by simp; nofun)

instance : Codable Empty BasicUniv where
  encode := empty#

instance : Codable Unit BasicUniv where
  encode := unit#

instance : Codable String BasicUniv where
  encode := string#

instance : Codable Std.Format BasicUniv where
  encode := format#

instance : Codable Lean.Name BasicUniv where
  encode := name#

instance [inst : Codable α BasicUniv] : Codable (Array α) BasicUniv where
  encode := .mk "array"<: (fun x => inst.encode)
  wf := by
    have := inst.wf
    simp [Univ.Code.decode, decodeImpl] at *
    grind

instance [inst : Codable α BasicUniv] : Codable (List α) BasicUniv where
  encode := .mk "list"<: (fun _ => inst.encode)
  wf := by
    have := inst.wf
    simp [Univ.Code.decode, decodeImpl] at *
    grind


end BasicUniv


