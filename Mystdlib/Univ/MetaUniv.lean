import Lean
import Mystdlib.Univ.BasicUniv

open Lean Core Meta Elab Term Command

open Univ

def MetaUniv.Extension : Univ where
  inner := .ofList [
      (mkUnivEntry "expr" 0 Expr),
      (mkUnivEntry "metavarkind" 0 MetavarKind),
      (mkUnivEntry "mvarid" 0 MVarId),
      (mkUnivEntry "fvarid" 0 FVarId),
      (mkUnivEntry "localcontext" 0 LocalContext),
      (mkUnivEntry "metam" 1 MetaM),
      (mkUnivEntry "termelabm" 1 TermElabM),
      (mkUnivEntry "corem" 1 CoreM),
      (mkUnivEntry "commandelabm" 1 CommandElabM),
    ]

abbrev MetaUniv : Univ := BasicUniv ∪ MetaUniv.Extension

instance : Univ.DisjointUnivUnion BasicUniv MetaUniv.Extension where
  disjoint := by native_decide


