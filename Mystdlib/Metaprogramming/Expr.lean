import Lean

open Lean

instance : ToString FVarId where
  toString := fun | .mk nm => nm.toString

--

deriving instance Lean.ToExpr for String.Pos.Raw
deriving instance Lean.ToExpr for Substring.Raw
deriving instance Lean.ToExpr for Lean.SourceInfo
deriving instance Lean.ToExpr for Lean.Syntax

--

def getForallEBinderType (forall_e : Expr) : forall_e.isForall -> Expr := fun h =>
  match forall_e with
  | .forallE _ bindertyp _ _ => bindertyp

def getForallERHSType (forall_e : Expr) : forall_e.isForall -> Expr := fun h =>
  match forall_e with
  | .forallE _ _ rhstyp _ => rhstyp


