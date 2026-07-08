import Mystdlib.IO.TraceRefPure
import Lean
import Std
import Mystdlib.Univ.MetaUniv
import Mystdlib.Univ.Structure
import Mathlib.Lean.Meta


open Lean

open Std


abbrev LocalDeclSchema : Structure := .ofList [
  ("userName", .mk "name" 0 []),
  ("toExpr", .mk "expr" 0 []),
  ("toExpr_inferType", .mk "expr" 0 []),
  ]
abbrev MVarDeclSchema : Structure := .ofList [
  ("userName", .mk "name" 0 []),
  ("lctx", .mk "localcontext" 0 []),
  ("type", .mk "expr" 0 []),
  ]

namespace TraceElabT


def β : String -> Type _ :=
  fun str => if str = "nextAssignableIdx" then Nat
  else Map Nat (Structure.Term MetaUniv)

structure WF (m : DMap String β) where
  hasNextAssignableIdx : "nextAssignableIdx" ∈ m
  hasLocalDecls : "localDecls" ∈ m
  hasMVarDecls : "mvarDecls" ∈ m

instance : Decidable (WF m) :=
  if h1 : "nextAssignableIdx" ∈ m
  then if h2 : "localDecls" ∈ m
    then if h3 : "mvarDecls" ∈ m
      then .isTrue (by grind [WF])
      else .isFalse (by grind [WF])
    else .isFalse (by grind [WF])
  else .isFalse (by grind [WF])

abbrev _root_.TraceElabT (μ : Type -> Type) [Monad μ] [MonadLiftT (ST IO.RealWorld) μ] (α : Type) :=
  TraceT WF μ α

variable [Monad μ] [MonadLiftT (ST IO.RealWorld) μ]


def run (x : TraceElabT μ α) : μ (α × { m // WF m }) :=
  TraceT.run x ⟨.ofList [⟨"nextAssignableIdx", cast (by cbv) 0⟩, ⟨"localDecls", cast (by cbv) (∅ : Map Nat (Structure.Term MetaUniv))⟩, ⟨"mvarDecls", cast (by cbv) (∅ : Map Nat (Structure.Term MetaUniv))⟩], by decide⟩

open Elab
def runTacticM (m : Lean.MVarId) (x : TraceElabT Tactic.TacticM Unit) : TraceElabT Term.TermElabM (List MVarId) := do
  let r <- Tactic.run_for m (TraceT.run x (<- get))
  modifyGet fun σ => (r.2, match r.1 with | .some x => x.2 | .none => σ)

def requestIdx : TraceT WF μ Nat := do
  let idx <- TraceT.getValueCast "nextAssignableIdx" (·.property.hasNextAssignableIdx)
  discard <| TraceT.modifyKey "nextAssignableIdx" Nat.succ (by grind [WF, DMap.containsKey_modifyKey])
  return idx

def logLocalDecl (ldecl : Structure.Term MetaUniv) (h : LocalDeclSchema.SatisfiedBy ldecl := by decide) : TraceT WF μ Unit := do
  let newIdx <- requestIdx
  discard <| TraceT.modifyKey "localDecls" (fun m => m.insertEntry newIdx ldecl) (by grind [WF, DMap.containsKey_modifyKey])

def logMVarDecl [MonadError μ] (mvarDecl : Structure.Term MetaUniv) : TraceT WF μ Unit := do
  let newIdx <- requestIdx
  if h : MVarDeclSchema.SatisfiedBy mvarDecl
  then discard <| TraceT.modifyKey "mvarDecls" (fun m => m.insertEntry newIdx mvarDecl) (by grind [WF, DMap.containsKey_modifyKey])
  else throwError m!"logMVarDecl: schema not satisfied by structure term"

def logMVarId [MonadMCtx μ] [MonadError μ] (mvarid : Lean.MVarId) : TraceElabT μ Unit := do
  let mctx <- getMCtx
  match mctx.decls.find? mvarid with
  | .none => throwError m!"logMVarId: MVarId not found in mctx.decls"
  | .some x => logMVarDecl ⟨.ofList [("userName", Univ.mkTerm x.userName), ("lctx", Univ.mkTerm x.lctx), ("type", Univ.mkTerm x.type)]⟩
