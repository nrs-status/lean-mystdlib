import Mystdlib.Univ.Basic
import Mystdlib.Univ.GenCodable

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

