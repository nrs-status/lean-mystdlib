import Mystdlib.Optics.Tambara
import Mystdlib.Metaprogramming.General
import Mathlib.Data.List.TakeWhile

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

def syntax_traversal : Traversal' Syntax Syntax := TraversalVL.toTraversal syntax_traversalVL

def syntax_nodes_traversal : Traversal' Syntax Syntax :=
  .mk'' fun
  | .node _ k rest => 
    ⟨rest.size, rest.reverse<:, fun v => .node .none k v.toArray⟩
  | x => 
    ⟨0, #v[], fun _ => x⟩

instance : Plated Syntax where
  plate := syntax_nodes_traversal

section Prod

partial def prod_iso_stx_to : Syntax -> Syntax × List Syntax
| `($x × $y) => match recur y with
  | (y', []) => (x, [y'])
  | (y', rest) => (x, y' :: rest)
| x => (x, [])

def prod_iso_stx_from : Syntax × List Syntax -> Syntax 
| (fst, []) => fst
| (fst, (last :: [])) => MacroM.stx `($(.mk fst) × $(.mk last))
| (fst, (snd :: rest)) => MacroM.stx `($(.mk fst) × $(.mk (recur (snd, rest))))

def prod_iso_stx : Iso' (Syntax × List Syntax) Syntax :=
  .mk prod_iso_stx_to prod_iso_stx_from


end Prod

section Tuple

def tuple_iso_stx_to : Syntax -> Syntax × List Syntax
| `(($x, $y,*)) => (x, y.getElems.raw.toList)
| x => (x, [])

def tuple_iso_stx_from : Syntax × List Syntax -> Syntax
| (fst, []) => fst
| (fst, rest) => MacroM.stx `(($(.mk fst), $(Lean.Syntax.TSepArray.ofElems <| rest.toArray.map .mk),*))

def tuple_iso_stx : Iso' (Syntax × List Syntax) Syntax :=
  .mk tuple_iso_stx_to tuple_iso_stx_from


end Tuple



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

section DeclModifiers
/-
def declModifiers (inline : Bool) := leading_parser
  optional docComment >>
  optional (Term.«attributes» >> if inline then skip else ppDedent ppLine) >>
  optional visibility >>
  optional «protected» >>
  optional («meta» <|> «noncomputable») >>
  optional «unsafe» >>
  optional («partial» <|> «nonrec»)
-/

structure DeclModifiers where
  meta_or_noncomputable : Fin 3 -- 0 = none; 1 = meta; 2 = noncomputable
  unsafe_ : Bool
  partial_or_nonrec : Fin 3 -- same idea as above
deriving Repr, Inhabited


open Lean Parser Command in
def declmodifiers_stx_match : Syntax -> Syntax ⊕ DeclModifiers
| `(declModifiersF|$[$docComment]? $[$attributes]? $[$vis]? $[$protected_]? $[$meta_or_noncomputable?]? $[$unsafe_]? $[$partial_or_nonrec?]?) =>
  let meta_or_noncomputable?' : Fin 3 := match meta_or_noncomputable? with
  | .none => 0
  | .some x => match x with
    | `(«meta»|meta) => 1
    | `(«noncomputable»|noncomputable) => 2
    | _ => 0
  let partial_or_nonrec?' : Fin 3 := match partial_or_nonrec? with
  | .none => 0
  | .some x => match x with
    | `(«partial»|partial) => 1
    | `(«nonrec»|nonrec) => 2
    | _ => 0
  .inr ⟨meta_or_noncomputable?', unsafe_.elim .false (fun _ => .true), partial_or_nonrec?'⟩
| x => .inl x

open Lean Parser Command in
def declmodifiers_stx_build : DeclModifiers -> Syntax :=
  fun ⟨meta_or_noncomputable, unsafe_, partial_or_nonrec⟩ =>
    let meta_or_noncomputable' := match meta_or_noncomputable with
    | 0 => Option.none
    | 1 => .some <| .mk <| MacroM.stx `(«meta»|meta)
    | 2 => .some <| .mk <| MacroM.stx `(«noncomputable»|noncomputable)
    let unsafe_' := match unsafe_ with
    | .false => .none
    | .true => .some <| MacroM.tstx `(«unsafe»|unsafe)
    let partial_or_nonrec' := match partial_or_nonrec with
    | 0 => Option.none
    | 1 => .some <| .mk <| MacroM.stx `(«partial»|partial)
    | 2 => .some <| .mk <| MacroM.stx `(«nonrec»|nonrec)
    MacroM.stx `(declModifiersF|$(.none)? $(.none)? $(.none)? $(.none)? $(meta_or_noncomputable')? $(unsafe_')? $(partial_or_nonrec')?)

def declmodifiers_stx_prism : Prism' DeclModifiers Syntax :=
  .mk declmodifiers_stx_build declmodifiers_stx_match

end DeclModifiers

section DeclId

structure DeclId where
  nm : Lean.Name
  univ_vars : Array Syntax
deriving Repr, Inhabited


def declid_stx_prism_match : Syntax -> Syntax ⊕ DeclId 
| `(declId|$x:ident) => .inr ⟨x.getId, #[]⟩
| `(declId|$x:ident.{$y,*}) => .inr ⟨x.getId, y.getElems⟩
| x => .inl x

def declid_stx_prism_build : DeclId -> Syntax
| ⟨nm, univ_vars⟩ => if univ_vars.isEmpty
  then MacroM.stx `(declId|$(mkIdent nm))
  else MacroM.stx `(declId|$(mkIdent nm).{$(Lean.Syntax.TSepArray.ofElems <| univ_vars.map .mk),*})

def declid_stx_prism : Prism' DeclId Syntax :=
  .mk declid_stx_prism_build declid_stx_prism_match

end DeclId

section OptDeclSig

def OptDeclSig := Option (Syntax × List Syntax) deriving Inhabited, Repr

def optdeclsig_stx_prism_match : Syntax -> Syntax ⊕ OptDeclSig
| `(optDeclSig|: $y) => .inr <| .some <| arrow_iso_stx.view.{0,0} y
| `(optDeclSig|$x* : $y) =>
  let r := arrow_iso_stx.view.{0,0} y
  let r' := arrow_iso_stx.review.{0,0} (if h : x.raw.isEmpty 
    then r
    else (x.raw[0]'!p, (x.raw.drop 1).toList ++ (r.fst :: r.snd)))
  .inr <| .some <| arrow_iso_stx.view.{0,0} r'
| `(optDeclSig|) => .inr .none
| x => .inl x

def optdeclsig_stx_prism_build : Option (Syntax × List Syntax) -> Syntax
| .none => .missing
| .some x =>
  let r := arrow_iso_stx.review.{0,0} x
  MacroM.stx `(optDeclSig|: $(.mk r))

def optdeclsig_stx_prism : Prism' (Option (Syntax × List Syntax)) Syntax :=
  .mk optdeclsig_stx_prism_build optdeclsig_stx_prism_match

end OptDeclSig

section Ctor

structure Ctor where
  declmods : DeclModifiers
  nm : Lean.Name
  rhs : OptDeclSig
deriving Inhabited, Repr


open Lean Parser Command

/- keep in case findSkippingNestedOnHit doesn't work
def ctor_stx_prism_match : Syntax -> Syntax ⊕ Ctor :=
  fun stx => match stx with
| .node _ b args => if b == ``ctor
  then
    let := args.flatMap <| collect (Lean.Syntax.isOfKind · ``declModifiers)
    let declmods : DeclModifiers := if h : this.isEmpty 
      then default
      else (declmodifiers_stx_prism.preview <| this[0]'!p).elim default id
    let := args.filter (fun | .ident .. => .true | _ => .false)
    let nm := if h : this.isEmpty
      then Lean.Name.anonymous
      else let := this[0]'!p; this.getId
    let := args.flatMap <| collect (Lean.Syntax.isOfKind · ``optDeclSig)
    let := if h : this.isEmpty
     then Syntax.missing
     else this[0]'!p
    let typ := optdeclsig_stx_prism.preview this |>.elim default id
    dbg_trace "tracing ctor nm"
    dbg_trace nm
    .inr ⟨declmods, nm, typ⟩
  else .inl stx
| _ => .inl stx
-/
def ctor_stx_prism_match : Syntax -> Syntax ⊕ Ctor :=
  fun stx => match stx with
  | .node _ b _ => if b == ``ctor
  then
    let := findSkippingNestedOnHit [
      (Syntax.isOfKind · ``declModifiers), 
      (· matches .ident ..),
      (Syntax.isOfKind · ``optDeclSig)
      ] stx
    .inr ⟨declmodifiers_stx_prism.preview this[0]! |>.someD, this[1]!.getId, optdeclsig_stx_prism.preview this[2]! |>.someD⟩
  else .inl stx
  | _ => .inl stx

def ctor_stx_prism_build : Ctor -> Syntax
| ⟨declmods, nm, typ⟩ =>
  Syntax.node .none ``ctor #[.atom .none "|", declmodifiers_stx_prism.review declmods, mkCIdent nm, optdeclsig_stx_prism.review typ]

def ctor_stx_prism : Prism' Ctor Syntax :=
  .mk ctor_stx_prism_build ctor_stx_prism_match

#run_elab
  let stx := ctor_stx_prism.review ⟨default, `myctor, .some (MacroM.stx `(Nat), [MacroM.stx `(mytype)])⟩
  let r := ctor_stx_prism.preview stx |>.someD
  dbg_trace repr r
  let stx' <- `(inductive mytype $(.mk stx):ctor)
  dbg_trace <- ppCategory `command stx'

end Ctor

section Inductive

structure InductiveStx where
  declmods : DeclModifiers := default
  declid : DeclId
  optdeclsig : Option Syntax := .none
  ctors : Array Ctor
  cfields : Option Syntax := .none
  optderiving : Array Syntax := #[]
deriving Repr, Inhabited

def inductive_stx_prism_match : Syntax -> Syntax ⊕ InductiveStx
| `(Lean.Parser.Command.declaration|$declmods inductive $declid $[$optdeclsig]? where $ctors* $[$cfields]? $optderiving)
| `(Lean.Parser.Command.declaration|$declmods inductive $declid $[$optdeclsig]? $ctors* $[$cfields]? $optderiving) => 
  let declid' := declid_stx_prism.preview declid |>.elim default id
  let declmods' := declmodifiers_stx_prism.preview declmods |>.elim default id
  let ctors' := ctors.filterMap ctor_stx_prism.preview
  let optderiving' : Array Syntax := match optderiving with
  | `(Lean.Parser.Command.optDeriving|deriving $x,*) => x.getElems
  | _ => #[]
  .inr ⟨declmods', declid', optdeclsig, ctors', cfields, optderiving'⟩
| x => .inl x

def inductive_stx_prism_build : InductiveStx -> Syntax
| ⟨declmods, declid, optdeclsig, ctors, cfields, optderiving⟩ => 
  let declmods' := declmodifiers_stx_prism.review declmods
  let declid' := declid_stx_prism.review declid
  let optdeclsig' : Option (TSyntax `Lean.Parser.Term.typeSpec) := optdeclsig.elim .none (fun stx => .some (.mk stx))
  let ctors' := ctors.map ctor_stx_prism.review
  let cfields' : Option (TSyntax `Lean.Parser.Command.computedFields) := cfields.elim .none (fun stx => .some (.mk stx))
  let optderiving' : Option (TSyntax ``Lean.Parser.Command.optDeriving) := if optderiving.isEmpty
    then Option.none
    else Option.some <| MacroM.tstx `(Lean.Parser.Command.optDeriving|deriving $(Lean.Syntax.TSepArray.ofElems <| optderiving.map .mk),*)
  match optderiving' with
  | .none => MacroM.stx `($(.mk declmods'):declModifiers inductive $(.mk declid'):declId $[$optdeclsig']? where $(.mk ctors')* $[$cfields']?)
  | .some x => MacroM.stx `($(.mk declmods'):declModifiers inductive $(.mk declid'):declId $[$optdeclsig']? where $(.mk ctors')* $[$cfields']? $x)


def inductive_stx_prism : Prism' InductiveStx Syntax :=
  .mk inductive_stx_prism_build inductive_stx_prism_match

end Inductive

section Structure

inductive structureFieldKind | explicit | implicit | instance_implicit | simple
deriving Repr, Inhabited
structure StructureFieldStx where
  kind : structureFieldKind
  lhs : Lean.Name
  rhs : Syntax
deriving Repr, Inhabited

open Lean Parser Command in
def structure_field_stx_prism : Prism' StructureFieldStx Syntax :=
  .mk
    (fun ⟨kind, lhs, rhs⟩ => match kind with
    | .explicit => MacroM.stx `(structExplicitBinder|($(.mk (mkIdent lhs)) : $(.mk rhs)))
    | .implicit => MacroM.stx `(structImplicitBinder|{$(.mk (mkIdent lhs)) : $(.mk rhs)})
    | .instance_implicit => MacroM.stx `(structInstBinder|[$(.mk (mkIdent lhs)) : $(.mk rhs)])
    | .simple => MacroM.stx `(structSimpleBinder|$(.mk (mkIdent lhs)):ident : $(.mk rhs)))
    fun
    | `(structExplicitBinder|($lhs : $rhs)) => .inr ⟨.explicit, lhs.getId ,rhs⟩
    | `(structImplicitBinder|{$lhs : $rhs}) => .inr ⟨.implicit, lhs.getId, rhs⟩
    | `(structInstBinder|[$lhs : $rhs]) => .inr ⟨.instance_implicit, lhs.getId, rhs⟩
    | `(structSimpleBinder|$lhs:ident : $rhs) => .inr ⟨.simple, lhs.getId, rhs⟩
    | x => .inl x


structure StructureStx where
  declmods : DeclModifiers := default
  declid : DeclId
  optdeclsig : Option Syntax := .none
  fields : Array StructureFieldStx
  optderiving : Array Syntax := #[]
deriving Repr

def structure_stx_prism_match : Syntax -> Syntax ⊕ StructureStx
| `(Lean.Parser.Command.declaration|$declmods structure $declid $[$optdeclsig]? where $fields:structFields $optderiving) =>
  let declmods' := declmodifiers_stx_prism.preview declmods |>.elim default id
  let declid' := declid_stx_prism.preview declid |>.elim default id
  let fields' := match fields with
  | `(Lean.Parser.Command.structFields|$x*) => x.filterMap structure_field_stx_prism.preview
  | _ => #[]
  let optderiving' : Array Syntax := match optderiving with
  | `(Lean.Parser.Command.optDeriving|deriving $x,*) => x
  | _ => #[]
  .inr ⟨declmods', declid', optdeclsig, fields', optderiving'⟩
| x => .inl x

def structure_stx_prism_build : StructureStx -> Syntax :=
  fun ⟨declmods, declid, optdeclsig, fields, optderiving⟩ =>
  let declid' := declid_stx_prism.review declid
  let declmods' := declmodifiers_stx_prism.review declmods
  let optderiving' : Option (TSyntax ``Lean.Parser.Command.optDeriving) := if optderiving.isEmpty
    then Option.none
    else Option.some <| MacroM.tstx `(Lean.Parser.Command.optDeriving|deriving $(Lean.Syntax.TSepArray.ofElems <| optderiving.map .mk),*)
  let optdeclsig' : Option (TSyntax `Lean.Parser.Term.typeSpec) := optdeclsig.elim 
    .none 
    (fun stx => .some <| .mk (MacroM.stx `(Lean.Parser.Term.typeSpec|: $(.mk stx))))
  let fields' : TSyntax `Lean.Parser.Command.structFields := MacroM.tstx 
    `(Lean.Parser.Command.structFields| $(.mk <| fields.map structure_field_stx_prism.review)*)
  match optderiving', fields.isEmpty with
  | .none, .false => MacroM.stx `($(.mk declmods'):declModifiers structure $(.mk declid'):declId $[$optdeclsig']? where $fields':structFields)
  | .some x, .false => MacroM.stx `($(.mk declmods'):declModifiers structure $(.mk declid'):declId $[$optdeclsig']? where $fields':structFields $x)
 -- | .none, .true => MacroM.stx `($(.mk declmods'):declModifiers structure $(.mk declid'):ident $[$optdeclsig']? where)
  | .none, .true => MacroM.stx `($(.mk declmods'):declModifiers structure $(.mk declid'):declId $[$optdeclsig']? where)
  | .some x, .true => MacroM.stx `($(.mk declmods'):declModifiers structure $(.mk declid'):declId $[$optdeclsig']? where $x:optDeriving)


def structure_stx_prism : Prism' StructureStx Syntax :=
  .mk structure_stx_prism_build structure_stx_prism_match

def structure_stx_fields : Lens' (Array StructureFieldStx) StructureStx :=
  .mk StructureStx.fields ({ . with fields := · })

def structure_stx_declid : Lens' DeclId StructureStx :=
  .mk StructureStx.declid ({ · with declid := · })
end Structure

section Def
/-
def structure_stx_prism_match : Syntax -> Syntax ⊕ StructureStx
| `(Lean.Parser.Command.declaration|$declmods structure $declid $[$optdeclsig]? where $fields:structFields $optderiving) =>

-/

structure DefStx where
  declmods : DeclModifiers := default
  declid : DeclId
  optdeclsig : Option Syntax := .none
  body : Syntax

def def_stx_prism_match : Syntax -> Syntax ⊕ DefStx 
| `(Lean.Parser.Command.declaration|$declmods def $declid $[$optdeclsig]? := $body) =>
  let declmods' := declmodifiers_stx_prism.preview declmods |>.elim default id
  let declid' := declid_stx_prism.preview declid |>.elim default id
  .inr ⟨declmods', declid', optdeclsig, body⟩
| x => .inl x

def def_stx_prism_build : DefStx -> Syntax
| ⟨declmods, declid, optdeclsig, body⟩ => 
  let declmods' := declmodifiers_stx_prism.review declmods
  let declid' := declid_stx_prism.review declid
  let optdeclsig' := match optdeclsig with
  | .some x => MacroM.tstx `(optDeclSig|: $(.mk x))
  | .none => MacroM.tstx `(optDeclSig|)
  let body' := MacroM.tstx `(declVal|:= $(.mk body))
  MacroM.stx `($(.mk declmods'):declModifiers def $(.mk declid'):declId $optdeclsig' $body':declVal)

def def_stx_prism : Prism' DefStx Syntax :=
  .mk def_stx_prism_build def_stx_prism_match

end Def

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

/-
def mystructstx : StructureStx where
  declmods := ∅
  declid := `hi
  optdeclsig := .some <| MacroM.stx `(Nat -> Nat)
  fields := #[⟨.simple, mkCIdent `myfield, MacroM.stx `(Nat -> Nat)⟩]
  optderiving := #[]

#run_elab
  let declmods : DeclModifiers := ∅ 
  let declmods_as_stx := declmodifiers_stx_prism.review declmods
  let stx <- `($(.mk declmods_as_stx):declModifiers structure hi where)
  dbg_trace <- ppCategory `command stx
  dbg_trace <- ppCategory `command <| structure_stx_prism.review mystructstx
-/
