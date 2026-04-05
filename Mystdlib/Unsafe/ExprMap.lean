import Std

open Std


structure BVMap where
  i : Nat
  env : HashMap String Nat

def BVMap.empty : BVMap := ⟨0, {}⟩

def BVMap.add : String -> BVMap -> BVMap := 
  fun v bvm => BVMap.mk (BVMap.i bvm).succ <| (BVMap.env bvm).insert v bvm.i

def BVMap.find? (s : String) (bvm : BVMap) := bvm.env.get? s


unsafe inductive ExprMap α
| impl_empty
| impl_mk
  (bvar : HashMap Nat α)
  (fvar : HashMap String α)
  (app : ExprMap (ExprMap α))
  (lam : ExprMap α)

-- without opaque wrapper

unsafe def ExprMap.toOpt : ExprMap α -> Option (ExprMap α)
| .impl_empty => .none
| x => .some x

unsafe def ExprMap.ofOpt : Option (ExprMap α) -> ExprMap α
| .none => .impl_empty
| .some x => x

unsafe def ExprMap.union {α} (f : α -> α -> Option α) (ea eb : ExprMap α) : ExprMap α :=
  match ea, eb with
  | .impl_empty, em | em, .impl_empty => em
  | .impl_mk bvar fvar app lam, .impl_mk bvar' fvar' app' lam' => 
    let new_bvar := HashMap.union bvar bvar'
    let new_fvar := HashMap.union fvar fvar'
    let new_app := ExprMap.union (α := ExprMap α) 
      (fun x y => ExprMap.toOpt (ExprMap.union f x y)) app app'
    let new_lam := ExprMap.union f lam lam'
    .impl_mk new_bvar new_fvar new_app new_lam


inductive Expr
| var (s : String)
| app (e e' : Expr)
| lam : String -> Expr -> Expr

unsafe def ExprMap.update {α} : Expr -> (Option α -> Option α) -> ExprMap α -> ExprMap α := 
  fun e f em => 
    let rec go {α} : BVMap -> Expr -> (Option α -> Option α) -> ExprMap α -> ExprMap α :=
      fun bvm e f em =>
        match em with
        | .impl_empty => go bvm e f .impl_empty
        | .impl_mk bvar fvar app lam =>
          match e with
          | .var s => match BVMap.find? s bvm with
            | .some x => .impl_mk (bvar.alter x f) fvar app lam
            | .none => .impl_mk bvar (fvar.alter s f) app lam
          | .app e' e'' =>
            let r := go bvm e' (fun em' => ExprMap.toOpt (go bvm e'' f (ExprMap.ofOpt em'))) app
            .impl_mk bvar fvar r lam
          | .lam s e' =>
            .impl_mk bvar fvar app (go (BVMap.add s bvm) e' f lam)
  go BVMap.empty e f em


