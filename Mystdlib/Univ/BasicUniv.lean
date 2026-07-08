import Mystdlib.Univ.Basic
import Mystdlib.Univ.CodableGen

open Univ

abbrev BasicUniv : Univ where
  inner := .ofList [
    (mkUnivEntry "nat" 0 Nat),
    (mkUnivEntry "bool" 0 Bool),
    (mkUnivEntry "unit" 0 Unit),
    (mkUnivEntry "empty" 0 Empty),
    (mkUnivEntry "string" 0 String),
    (mkUnivEntry "format" 0 Std.Format),
    (mkUnivEntry "arrow" 2 (· -> ·)),
    (mkUnivEntry "name" 0 Lean.Name),
    (mkUnivEntry "array" 1 Array),
    (mkUnivEntry "list" 1 List),
    (mkUnivEntry "prod" 2 Prod),
    (mkUnivEntry "option" 1 Option),
    ]


/-
class Univ.CanRepr (univ : Univ) (t : univ.CodedTerm) where
  reprInst : Repr t.type

instance : Univ.CanRepr univ t where
  reprInst := ⟨fun _ _ => "(No proper Univ.CanRepr instance)"⟩

instance [inst : Codable α univ code] : univ.CanRepr ⟨_, _, _⟩ where
-/


/-
inductive CanRepr : Univ.Code -> Prop
| intro : code.typ ∈ ["nat", "bool", "unit", "empty", "string", "name", "array", "list", "prod", "option"] -> (∀i, CanRepr (code.tail i)) -> CanRepr code

partial def CanRepr_decidable : Decidable (CanRepr code) := 
  if h : ∀i, (CanRepr_decidable (code := code.tail i)).decide = true
  then if h' : code.typ ∈ ["nat", "bool", "unit", "empty", "string", "name", "array", "list", "prod", "option"]
    then .isTrue (.intro h' (by grind))
    else .isFalse <| by
      rintro ⟨h1, h2⟩
      grind
  else isFalse <| by
    rintro ⟨h1, h2⟩
    grind
  
instance : Decidable (CanRepr code) := CanRepr_decidable

def BasicUniv.repr (t : BasicUniv.CodedTerm) (h : CanRepr t.code) : String :=
  match h with
  | .intro iselm tailCanRepr =>
    if h : t.code.typ = "nat"
    then
      have : type_of% t.term = Nat := by
        rcases t with ⟨code, _, term⟩
        rcases code with ⟨⟨typ, _⟩, _⟩
        simp_all [Code.typ, Code.head, WType.head]
        subst h
        cbv
      reprStr (this ▸ t.term)
    else if h : t.code.typ = "bool"
    then 
      have : type_of% t.term = Bool := by
        rcases t with ⟨code, _, term⟩
        rcases code with ⟨⟨typ, _⟩, _⟩
        simp_all [Code.typ, Code.head, WType.head]
        subst h
        cbv
      reprStr (this ▸ t.term)
    else "unimplemented"


instance : Repr BasicUniv.CodedTerm where
  reprPrec := fun t _ =>
    if h : CanRepr t.code
    then BasicUniv.repr t h
    else "cannot repr"
-/



/-
class Univ.CanRepr (univ : Univ) (t : univ.CodedTerm) where
  reprInst : Repr t.type

instance [Repr α] [inst : Codable α univ code] {term : α} : univ.CanRepr ⟨code, h, inst.wf ▸ term⟩ where
  reprInst := by
    rw [CodedTerm.type, inst.wf]
    infer_instance

def Univ.CodedTerm.repr {univ : Univ} (t : univ.CodedTerm) [inst : univ.CanRepr t] : Std.Format := @_root_.repr _ inst.reprInst t.term
-/

/-
def Univ.CodedTerm.repr {univ : Univ} (t : univ.CodedTerm) [inst : Repr t.type] := @_root_.repr _ inst t.term

def Univ.CodedTerm.repr' {univ : Univ} (t : univ.CodedTerm) : match t with | ⟨code, satisfies, _⟩ => [Repr (univ.decode code satisfies)] -> Std.Format :=
  match hmatch : t with
  | ⟨_, _, term⟩ => by
    expose_names
    subst hmatch
    simp only at inst
    exact _root_.repr term

def Univ.CodedTerm.repr'' {univ : Univ} (t : univ.CodedTerm) [Codable α univ t.code] [Repr α] : Std.Format := by
  expose_names
  rw [<- inst.wf] at inst_1
  exact _root_.repr t.term
-/
--def Univ.CodedTerm.repr''' {univ : Univ} (t : univ.CodedTerm) [Codable α univ [inst : Repr t.type] := @_root_.repr _ inst t.term



--instance [TypeFnGen arity t] : IsUnivMem t α ⟨.ofList [mkUnivEntry typ arity α]⟩ typ where


/-

class IsUnivType (code : String) (univ : Univ) (type : outParam Type) 
instance  : IsUnivType code ⟨.ofList [mkUnivEntry typ 0 α]⟩ α := sorry

instance 
  [IsUnivType code ⟨.ofList es⟩ α]
  : IsUnivType code ⟨.ofList (e :: es)⟩ α := sorry

instance 
  [IsUnivType code ⟨.ofList (e :: es)⟩ α]
  : IsUnivType code ⟨.ofList (e :: e' :: es)⟩ α := sorry

instance
  : IsUnivType _ _ _ := _

#eval! x.repr

set_option synthInstance.checkSynthOrder false in
instance [Codable α univ code] [Repr α] : Repr (⟨code, satisfies, term⟩ : univ.CodedTerm).type := _
-/
