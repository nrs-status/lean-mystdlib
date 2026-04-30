import Mystdlib.Optics.Tambara.Fold
import Mystdlib.Optics.Tambara
import Mystdlib.Metaprogramming.General
import Mystdlib.Optics.Tambara.Traversal

open Lean

open Tamb

open Lean.PrettyPrinter

section Arrow

def Syntax.mkArrow : Syntax -> Syntax -> Syntax :=
  fun head body => MacroM.stx `($(.mk head) -> $(.mk body))

def Syntax.mkArrows : List Syntax -> Syntax
| .nil => .missing
| .cons x .nil => x
| .cons x xs => Syntax.mkArrow x (Syntax.mkArrows xs)

partial def arrow_iso_stx_to : Syntax -> (Syntax × List Syntax)
| `($x -> $y) => match recur y with
  | (head, rest) => (x, head :: rest)
| `(Lean.Parser.Term.depArrow|$x -> $y) => match recur y with
  | (head, rest) => (x, head :: rest)
| x => (x, [])

def arrow_iso_stx_from : (Syntax × List Syntax) -> Syntax
| (head, rest) => Syntax.mkArrows (head :: rest)

def arrow_iso_stx : Iso' (Syntax × List Syntax) Syntax :=
  .mk arrow_iso_stx_to arrow_iso_stx_from

def arrow_last : Lens' Syntax (Syntax × List Syntax) :=
  .mk 
    (fun (head, tail) => if h : tail.isEmpty then head else tail.getLast !p) 
    (fun (head, tail) new => if h : tail.isEmpty then (new, []) else (head, tail.modify tail.length.pred (fun _ => new)))

def arrow_fold : Fold Syntax Syntax :=
  .mk (F := List) (arrow_iso_stx_to · |> uncurry .cons)

def arrow_aff_list : AffineTraversal' Syntax (List Syntax) :=
  .mk 
    (fun | .nil => .inl .nil | x => .inr <| Syntax.mkArrows x)
    (fun l stx => arrow_iso_stx.view.{0, 0} stx |> (fun (head, rest) => l ++ (head :: rest)))

partial def arrow_traversalVL : TraversalVL' Syntax Syntax  :=
  fun _ _ f x => Syntax.mkArrows <$> traverse f (arrow_fold.toListOf x)

partial def arrow_traversal := arrow_traversalVL.toTraversal

end Arrow

section App

def app_iso_stx : Iso' (Syntax × Array Syntax) Syntax :=
  .mk 
    (fun 
      | `($head $args*) => (head, args)
      | x => (x, .mk []))
    (fun (head, args) => Lean.Syntax.mkApp (.mk head) (.mk args))

partial def app_traversalVL : TraversalVL' Syntax Syntax :=
  fun F _ f x =>
    let (head, args) := app_iso_stx.view.{0,0} x
    (fun head' args' => Lean.Syntax.mkApp (.mk head') (.mk args')) <$> f head <*> args.traverse (app_traversalVL F f)

end App

section Matchers

def syntax_missing : Prism' Unit Syntax :=
  .mk (fun _ => .missing) (fun | .missing => .inr .unit | x => .inl x)

def syntax_node : Prism' (SourceInfo × SyntaxNodeKind × Array Syntax) Syntax :=
  .mk 
    (fun (srcinf, kind, ar) => .node srcinf kind ar)
    (fun | .node srcinf kind ar => .inr (srcinf, kind, ar) | x => .inl x)

def syntax_atom : Prism' (SourceInfo × String) Syntax :=
  .mk
    (fun (inf, str) => .atom inf str)
    (fun | .atom inf str => .inr (inf, str) | x => .inl x)

def syntax_ident : Prism' (SourceInfo × Substring.Raw × Name × List Syntax.Preresolved) Syntax :=
  .mk
    (fun (inf, substr, nm, l) => .ident inf substr nm l)
    (fun | .ident inf substr nm l => .inr (inf, substr, nm, l) | x => .inl x)

end Matchers


partial def syntax_traversalVL : TraversalVL' Syntax Syntax :=
  fun _ _ f x => match x with
  | .node _ _ rest =>
    (fun head rest' => match head with | .node x y _ => .node x y rest' | x => x) <$> f x <*> rest.traverse (syntax_traversalVL _ f)
  | _ => f x

def syntax_traversal : Traversal'.{0,0} Syntax Syntax := TraversalVL.toTraversal syntax_traversalVL



inductive bracketedBinderKind | explicit | implicit | strict_implicit | instance_implicit
def bracketedBinder : Prism' (bracketedBinderKind × Array Syntax × Syntax) Syntax :=
  .mk 
    (fun (kind, lhs, rhs) =>  
      MacroM.stx <| match kind with
      | .explicit => `(bracketedBinder|($(.mk lhs)* : $(.mk rhs)))
      | .implicit => `(bracketedBinder|{$(.mk lhs)* : $(.mk rhs)})
      | .strict_implicit => `(bracketedBinder|{{$(.mk lhs)* : $(.mk rhs)}})
      | .instance_implicit => if h : lhs.isEmpty
        then `(bracketedBinder|[$(.mk rhs)])
        else `(bracketedBinder|[$(.mk (lhs[0]'!p)) : $(.mk rhs)])
      )
    <| fun
    | `(bracketedBinder|($lhs* : $rhs)) => .inr (.explicit, lhs, rhs)
    | `(bracketedBinder|{$lhs* : $rhs}) => .inr (.implicit, lhs, rhs)
    | `(bracketedBinder|{{$lhs* : $rhs}}) => .inr (.strict_implicit, lhs, rhs)
    | `(bracketedBinder|[$lhs : $rhs]) => .inr (.instance_implicit, #[lhs], rhs)
    | `(bracketedBinder|[$x]) => .inr (.instance_implicit, #[], x)
    | x => .inl x


section Structures
/-
def mkStructureField (fieldName : TSyntax `ident) (fieldType : TSyntax ``optDeclSig) : MacroM (TSyntax `Lean.Parser.Command.structSimpleBinder):= do
  let r <- `(structSimpleBinder| $(.mk fieldName.raw):ident $fieldType)
  return r
-/

end Structures

section Inductive

structure InductiveStx where
  declmods : Syntax
  declid : Syntax
  optdeclsig : Option Syntax
  ctors : Array Syntax
  cfields : Option Syntax
  optderiving : Array Syntax

def inductive_stx_prism_match : Syntax -> Syntax ⊕ InductiveStx
| `(Lean.Parser.Command.declaration|$declmods inductive $declid $[$optdeclsig]? where $ctors* $[$cfields]? $optderiving) => 
  let optderiving' : Array Syntax := match optderiving with
  | `(Lean.Parser.Command.optDeriving|deriving $x,*) => x
  | _ => #[]
  .inr ⟨declmods, declid, optdeclsig, ctors, cfields, optderiving'⟩
| x => .inl x

def inductive_stx_prism_build : InductiveStx -> Syntax
| ⟨declmods, declid, optdeclsig, ctors, cfields, optderiving⟩ => 
  let optderiving' : Option (TSyntax ``Lean.Parser.Command.optDeriving) := if optderiving.isEmpty
    then Option.none
    else Option.some <| MacroM.tstx `(Lean.Parser.Command.optDeriving|deriving $(.mk optderiving),*)
  let optdeclsig' : Option (TSyntax `Lean.Parser.Term.typeSpec) := optdeclsig.elim .none (fun stx => .some (.mk stx))
  let cfields' : Option (TSyntax `Lean.Parser.Command.computedFields) := cfields.elim .none (fun stx => .some (.mk stx))
  match optderiving' with
  | .none => MacroM.stx `($(.mk declmods):declModifiers inductive $(.mk declid):declId $[$optdeclsig']? where $(.mk ctors)* $[$cfields']?)
  | .some x => MacroM.stx `($(.mk declmods):declModifiers inductive $(.mk declid):declId $[$optdeclsig']? where $(.mk ctors)* $[$cfields']? $x)


def inductive_stx_prism : Prism' InductiveStx Syntax :=
  .mk inductive_stx_prism_build inductive_stx_prism_match

end Inductive

section Structure

/-
inductive bracketedBinderKind | explicit | implicit | strict_implicit | instance_implicit
def bracketedBinder : Prism' (bracketedBinderKind × Array Syntax × Syntax) Syntax :=
-/

inductive structureFieldKind | explicit | implicit | instance_implicit | simple
structure StructureFieldStx where
  kind : structureFieldKind
  lhs : Syntax
  rhs : Syntax

open Lean Parser Command in
def structure_field_stx_prism : Prism' StructureFieldStx Syntax :=
  .mk
    (fun ⟨kind, lhs, rhs⟩ => match kind with
    | .explicit => MacroM.stx `(structExplicitBinder|($(.mk lhs) : $(.mk rhs)))
    | .implicit => MacroM.stx `(structImplicitBinder|{$(.mk lhs) : $(.mk rhs)})
    | .instance_implicit => MacroM.stx `(structInstBinder|[$(.mk lhs) : $(.mk rhs)])
    | .simple => MacroM.stx `(structSimpleBinder|$(.mk lhs):ident : $(.mk rhs)))
    fun
    | `(structExplicitBinder|($lhs : $rhs)) => .inr ⟨.explicit, lhs ,rhs⟩
    | `(structImplicitBinder|{$lhs : $rhs}) => .inr ⟨.implicit, lhs, rhs⟩
    | `(structInstBinder|[$lhs : $rhs]) => .inr ⟨.instance_implicit, lhs, rhs⟩
    | `(structSimpleBinder|$lhs:ident : $rhs) => .inr ⟨.simple, lhs, rhs⟩
    | x => .inl x


structure StructureStx where
  declmods : Syntax
  declid : Syntax
  optdeclsig : Option Syntax
  fields : Array StructureFieldStx
  optderiving : Array Syntax

def structure_stx_prism_match : Syntax -> Syntax ⊕ StructureStx
| `(Lean.Parser.Command.declaration|$declmods structure $declid $[$optdeclsig]? where $fields:structFields $optderiving) =>
  let fields' := match fields with
  | `(Lean.Parser.Command.structFields|$x*) => x.filterMap structure_field_stx_prism.preview
  | _ => #[]
  let optderiving' : Array Syntax := match optderiving with
  | `(Lean.Parser.Command.optDeriving|deriving $x,*) => x
  | _ => #[]
  .inr ⟨declmods, declid, optdeclsig, fields', optderiving'⟩
| x => .inl x

def structure_stx_prism_build : StructureStx -> Syntax :=
  fun ⟨declmods, declid, optdeclsig, fields, optderiving⟩ =>
  let optderiving' : Option (TSyntax ``Lean.Parser.Command.optDeriving) := if optderiving.isEmpty
    then Option.none
    else Option.some <| MacroM.tstx `(Lean.Parser.Command.optDeriving|deriving $(.mk optderiving),*)
  let optdeclsig' : Option (TSyntax `Lean.Parser.Term.typeSpec) := optdeclsig.elim .none (fun stx => .some (.mk stx))
  let fields' : TSyntax `Lean.Parser.Command.structFields := MacroM.tstx `(Lean.Parser.Command.structFields| $(.mk <| fields.map structure_field_stx_prism.review)*)
  match optderiving', fields.isEmpty with
  | .none, .false => MacroM.stx `($(.mk declmods) structure $(.mk declid) $[$optdeclsig']? where)
  | .some _, .false => .missing
  | .none, .true => MacroM.stx `($(.mk declmods) structure $(.mk declid) $[$optdeclsig']? where $fields':structFields)
  | .some x, .true => MacroM.stx `($(.mk declmods) structure $(.mk declid) $[$optdeclsig']? where $fields':structFields $x)

def structure_stx_prism : Prism' StructureStx Syntax :=
  .mk structure_stx_prism_build structure_stx_prism_match

def structure_stx_fields : Lens' (Array StructureFieldStx) StructureStx :=
  .mk StructureStx.fields ({ . with fields := · })

def structure_stx_declid : Lens' Syntax StructureStx :=
  .mk StructureStx.declid ({ · with declid := · })

end Structure
/-
def ctortype1 := MacroM.stx `(Unit -> Nat -> mytype String)
def ctortype2 := MacroM.stx `(Nat -> notapp)
def ctortype3 := MacroM.stx `(mytype Nat)
def ctortypes := [ctortype1, ctortype2, ctortype3]
def prer := each (ς := List _) <∘> arrow_iso_stx <∘> arrow_last <∘> app_iso_stx <∘> tuple 0
def r :=
  (each <∘> arrow_iso_stx <∘> arrow_last <∘> app_iso_stx <∘> tuple 0).set (mkIdent `typate)
  ctortypes
#run_elab
  r.forM (do dbg_trace <- formatTerm ·)
-/
