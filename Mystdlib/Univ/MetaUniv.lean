import Lean
import Mystdlib.Univ.Free.Basic

open Lean Core Meta Elab Term Command

def MetaUniv.Extension : Univ where
  inner := .ofList [
      ("expr", ⟨0, fun _ => Expr⟩),
      ("metam", ⟨1, fun v => MetaM v[0]⟩),
      ("termelabm", ⟨1, fun v => TermElabM v[0]⟩),
      ("corem", ⟨1, fun v => CoreM v[0]⟩),
      ("commandelabm", ⟨1, fun v => CommandElabM v[0]⟩),
    ]

def MetaUniv : Univ := Univ.BasicUniv ∪ MetaUniv.Extension


