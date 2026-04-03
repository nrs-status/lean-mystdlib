import Lean

open Lean

instance : ToString FVarId where
  toString := fun | .mk nm => nm.toString

--

def getForallEBinderType (forall_e : Expr) : forall_e.isForall -> Expr := fun h =>
  match forall_e with
  | .forallE _ bindertyp _ _ => bindertyp

def getForallERHSType (forall_e : Expr) : forall_e.isForall -> Expr := fun h =>
  match forall_e with
  | .forallE _ _ rhstyp _ => rhstyp

