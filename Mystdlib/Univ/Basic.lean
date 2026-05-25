import Mystdlib.General
import Mystdlib.Rose.BFinVec

structure Univ where
  codeNodes : List String
  arities : { str // str ∈ codeNodes } -> Nat
  decode : Rose arities -> Type u


class Codable (α : Type u) (univ : Univ) where
  encode : Rose univ.arities
  wf : univ.decode encode = α := by simp

namespace BasicUniv

@[grind]
def codeNodes := ["nat", "bool", "unit", "empty", "string", "format", "syntax", "expr", "array", "list"]

@[grind]
def arities : { str // str ∈ codeNodes } -> Nat :=
  fun ⟨str, _⟩ => if str ∈ ["array", "list"]
  then 1
  else 0

@[simp]
def decode : Rose arities -> Type :=
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
  else if h : str = "array"
  then Array (decode (v ⟨0, by grind⟩))
  else if h : str = "list"
  then List (decode (v ⟨0, by grind⟩))
  else by
    simp [codeNodes] at is_elm
    exfalso; grind

@[simp]
def _root_.BasicUniv : Univ where
  codeNodes := codeNodes
  arities := arities
  decode := decode

instance : Codable Nat BasicUniv where
  encode := .mk "nat"<: nofun

instance : Codable Bool BasicUniv where
  encode := .mk "bool"<: nofun

instance : Codable Lean.Syntax BasicUniv where
  encode := .mk "syntax"<: nofun

instance : Codable Empty BasicUniv where
  encode := .mk "empty"<: nofun

instance : Codable Unit BasicUniv where
  encode := .mk "unit"<: nofun

instance : Codable String BasicUniv where
  encode := .mk "string"<: nofun

instance : Codable Std.Format BasicUniv where
  encode := .mk "format"<: nofun

instance : Codable Lean.Expr BasicUniv where
  encode := .mk "expr"<: nofun

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
