import Mystdlib.General
import Mathlib.Data.W.Basic
import Mystdlib.Mathlib.Encodable

structure Univ where
  codeNodes : List String
  arities : { str // str ∈ codeNodes } -> Type
  decode : WType arities -> Type u

abbrev Univ.Code (univ : Univ) := WType univ.arities

def Univ.Code.decode {univ : Univ} (enc : univ.Code) := univ.decode enc

syntax:max (name := encode_pdescr) ident "#" : term
macro_rules
| `($(x):ident#) => `(⟨$(Lean.Syntax.mkStrLit x.getId.toString)<:, nofun⟩)

class Codable (α : Type u) (univ : Univ) where
  encode : WType univ.arities
  wf : univ.decode encode = α := by simp

namespace BasicUniv

@[grind]
def codeNodes := ["nat", "bool", "unit", "empty", "string", "format", "syntax", "expr", "name", "array", "list"]

@[grind]
def arities : { str // str ∈ codeNodes } -> Type :=
  fun ⟨str, _⟩ => if str ∈ ["array", "list"]
  then Unit
  else Empty

@[simp]
def decode : WType arities -> Type :=
  fun ⟨⟨str, is_elm⟩, v⟩ => if h : str = "nat"
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
  else if h : str = "expr"
  then Lean.Expr
  else if h : str = "name"
  then Lean.Name
  else if h : str = "array"
  then Array (decode (v (cast ?_ Unit.unit)))
  else if h : str = "list"
  then List (decode (v (cast ?_ Unit.unit)))
  else ?_
where finally
  · subst h
    simp [arities]
  · subst h
    simp [arities]
  · exfalso
    simp [codeNodes] at is_elm
    grind

@[simp]
def _root_.BasicUniv : Univ where
  codeNodes := codeNodes
  arities := arities
  decode := decode

instance {σ : { str // str ∈ codeNodes }} : Encodable (arities σ)  := by
  simp [arities]
  split <;> infer_instance

instance {σ : { str // str ∈ codeNodes}} : Fintype (arities σ) := by
  simp [arities]
  split <;> infer_instance

#synth Encodable (WType arities)
instance : Encodable BasicUniv.Code := by
  simp [Univ.Code]
  infer_instance

instance : DecidableEq BasicUniv.Code := Encodable.decidableEqOfEncodable _

instance : Hashable BasicUniv.Code where
  hash := hash ∘ (inferInstance : Encodable BasicUniv.Code).encode

instance : Codable Nat BasicUniv where
  encode := nat#

instance : Codable Bool BasicUniv where
  encode := bool#

instance : Codable Lean.Syntax BasicUniv where
  encode := .mk "syntax"<: nofun

instance : Codable Empty BasicUniv where
  encode := empty#

instance : Codable Unit BasicUniv where
  encode := unit#

instance : Codable String BasicUniv where
  encode := string#

instance : Codable Std.Format BasicUniv where
  encode := format#

instance : Codable Lean.Expr BasicUniv where
  encode := expr#

instance : Codable Lean.Name BasicUniv where
  encode := name#

instance [inst : Codable α BasicUniv] : Codable (Array α) BasicUniv where
  encode := .mk "array"<: (fun x => inst.encode)
  wf := by
    have := inst.wf
    simp at *
    grind

instance [inst : Codable α BasicUniv] : Codable (List α) BasicUniv where
  encode := .mk "list"<: (fun _ => inst.encode)
  wf := by
    have := inst.wf
    simp at *
    grind

end BasicUniv



