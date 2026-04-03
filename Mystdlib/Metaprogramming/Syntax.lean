import Lean 
import Mystdlib.RecursionSchemes

open Lean 

--

open Lean Parser  in
def mkTypelessFunTerm (binders : Array Ident) (body : Syntax) : TSyntax ``Lean.Parser.Term.fun := 
  ⟨mkNode ``Lean.Parser.Term.fun #[mkAtom "fun", mkNode ``Lean.Parser.Term.basicFun 
    #[mkNullNode binders, 
    mkNullNode #[], 
    mkAtom "=>", 
    body]]⟩

--

def constructTerm (ar : Array String) : CoreM Syntax := do
  match Lean.Parser.runParserCategory (<- getEnv) `term (ar.foldl (fun prev x => prev ++ " " ++ x) "") with
  | .ok x => return x
  | .error e => throwError e

--

def Syntax.getArg? (stx : Syntax) (i : Nat) : Option Syntax :=
  match stx[i] with
  | .missing => .none
  | x => x

partial def Syntax.getAt?_impl (stx : Syntax) (parser_nms_rev : Array Name) (h : ¬ parser_nms_rev.isEmpty) : Option (Array Syntax) :=
  match stx with
  | .node _ kind sub_stx => if kind = parser_nms_rev.back (by grind) 
    then if h' : parser_nms_rev.pop.isEmpty
      then sub_stx
      else sub_stx.findSome? fun stx' => Syntax.getAt?_impl stx' parser_nms_rev.pop h'
    else .none
  | _ => .none

partial def Lean.Syntax.getAt? (stx : Syntax) (parser_nms : Array Name) (h : ¬ parser_nms.isEmpty) : Option (Array Syntax) := Syntax.getAt?_impl stx parser_nms.reverse (by simp_all)

partial def Lean.Syntax.getAtLeaf? (stx : Syntax) (parser_nms : Array Name) (h : ¬ parser_nms.isEmpty := by first | grind | simp_all) : Option (String ⊕ Name) := match stx.getAt? parser_nms h with
| .none => .none
| .some x => if h : x.size = 1 then 
  match x[0]'(by grind) with
  | .ident _ _ nm _ => .some <| .inr nm
  | .atom _ s => .some <| .inl s
  | _ => .none
  else .none

instance : Recursive Syntax where
  ctor_aux := SourceInfo × SyntaxNodeKind
  recur_info := fun | .node inf kind substx => .some ((inf, kind), substx) | _ => .none
  of_recur := fun ((inf, kind), recur_result) => .node inf kind recur_result

