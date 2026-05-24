import Qq
import Lean
import Mystdlib.CPUModel.Nodeless
import Mystdlib.Metaprogramming.SyntaxOptics
import Mystdlib.Metaprogramming.GenThms
import Mystdlib.Metaprogramming.Misc

open Lean Meta Elab Term Command

open Qq

open Circuit

open Std


inductive Univ | bool
deriving DecidableEq, Repr, ToExpr

abbrev Univ.decode : Univ -> Type
| .bool => Bool

abbrev andCircuit : Circuit Univ := .ofNodeCodes #[.bool, .bool] #[.bool]


def mkNodeCodesOfIdxThm_mkThmNm (circuit_nm : Name) (idx : Nat) : Lean.Name :=
  String.toName (circuit_nm.toString ++ "_nodeCodesOfIdxThms_" ++ toString idx)

unsafe def mkNodeCodesOfIdxThm (circuit_nm : Name) (idx : Nat) : CommandElabM Unit := do
  let statement <- delabbing <| eqOfEvalExprToExpr' <| <- mkAppM ``nodeCodesOfIdx #[mkConst circuit_nm, q($idx)]
  genThm (mkNodeCodesOfIdxThm_mkThmNm circuit_nm idx) statement (<- `(by native_decide))

def mkIdxElmIdsThm_mkThmNm (circuit_nm : Name) (idx : Nat) : Lean.Name :=
  String.toName (circuit_nm.toString ++ "_idxElmIdsThms_" ++ toString idx)

def mkIdxElmIdsThm_mkStatement (circuit_nm : Name) (idx : Nat) : TermElabM Expr := do
  let ids_expr <- mkAppM ``Circuit.ids #[mkConst circuit_nm]
  mkAppM ``Membership.mem #[ids_expr, q($idx)]

def mkIdxElmIdsThm (circuit_nm : Name) (idx : Nat) : CommandElabM Unit := do
  genThm 
    (mkIdxElmIdsThm_mkThmNm circuit_nm idx) 
    (<- delabbing <| mkIdxElmIdsThm_mkStatement circuit_nm idx) 
    (<- `(by native_decide))

def mkTypeOfIdxThm_tacticSeq (circuit_nm decode_fn_nm : Name) (idx : Nat) : Lean.Syntax :=
  let idx_eq_thm_nm := mkNodeCodesOfIdxThm_mkThmNm circuit_nm idx
  let simpstx := simp_nm_prism.review [``typeOfIdx, idx_eq_thm_nm, ``typeOfNodeCodes, ``TypeList.toDFinVecFunType, ``TypeList.concat, ``TypeList.toFunType, decode_fn_nm, ``TypeList.toDFinVec, ``DFinVec, ``TypeList.length, ``TypeList.get]
  let rwstx := rw_nm_prism.review (idx_eq_thm_nm, [])
  let simpstx' := simp_nm_prism.review [decode_fn_nm]
  let tacticstx := tacticSeq_prism.review [simpstx, rwstx, simpstx']
  tacticstx

def mkTypeOfIdxThm_mkThmNm (circuit_nm : Name) (idx : Nat) : Lean.Name :=
  String.toName (circuit_nm.toString ++ "_typeOfIdxThms_" ++ toString idx)

def mkTypeOfIdxThm (circuit_nm decode_fn_nm : Name) (idx : Nat) : CommandElabM Unit := do
  let lhs <- mkAppM ``Circuit.typeOfIdx #[mkConst circuit_nm, mkConst decode_fn_nm, q($idx), mkConst <| mkIdxElmIdsThm_mkThmNm circuit_nm idx]
  let statement <- delabbing <| eqOfTacticSeq lhs (mkTypeOfIdxThm_tacticSeq circuit_nm decode_fn_nm idx)
  genThm 
    (mkTypeOfIdxThm_mkThmNm circuit_nm idx) 
    statement 
    (<- `(by $(.mk <| mkTypeOfIdxThm_tacticSeq circuit_nm decode_fn_nm idx); rfl))

@[implemented_by mkNodeCodesOfIdxThm]
opaque unsafeMkNodeCodesOfIdxThm (circuit_nm : Name) (idx : Nat) : CommandElabM Unit

syntax "thma" : command
syntax "thmb" : command
syntax "thmc" : command
elab_rules : command
| `(thma) => unsafeMkNodeCodesOfIdxThm ``andCircuit 0
| `(thmb) => mkIdxElmIdsThm ``andCircuit 0
| `(thmc) => mkTypeOfIdxThm ``andCircuit ``Univ.decode 0

thma
thmb
thmc


