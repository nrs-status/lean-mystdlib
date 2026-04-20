import Std

open Std

unsafe inductive ExprMapImpl (α)
| impl_empty
| impl_mk
  (bvar : HashMap Nat α)
  (fvar : HashMap String α)
  (app : ExprMapImpl (ExprMapImpl α))
  (lam : ExprMapImpl α)

#print ExprMapImpl.rec

opaque ExprMapRef (α : Type) : NonemptyType.{0}

structure ExprMap (α : Type) where
  private mk' :: 
  val : (ExprMapRef α).type
  nonempty : Nonempty α

instance [Nonempty α] : Nonempty (ExprMap α) := (ExprMapRef α).2.rec (⟨·, inferInstance⟩)

unsafe def ExprMap.mk_impl {α : Type} [Nonempty α] (bvar : HashMap Nat α) (fvar : HashMap String α) (app : ExprMap (ExprMap α)) (lam : ExprMap α) : ExprMap α :=
  unsafeCast (ExprMapImpl.impl_mk bvar fvar (unsafeCast app) (unsafeCast lam))

unsafe def ExprMap.empty_impl {α : Type} [Nonempty α] : ExprMap α := unsafeCast (@ExprMapImpl.impl_empty α)

@[implemented_by ExprMap.mk_impl]
opaque ExprMap.mk {α : Type} [Nonempty α] (bvar : HashMap Nat α) (fvar : HashMap String α) (app : ExprMap (ExprMap α)) (lam : ExprMap α) : ExprMap α

@[implemented_by ExprMap.empty_impl]
opaque ExprMap.empty {α : Type} [Nonempty α] : ExprMap α

unsafe def ExprMap.casesOn_impl.{u} 
  {α : Type}
  [Nonempty α]
  {motive : ExprMap α -> Sort u}
  (t : ExprMap α)
  (empty : motive ExprMap.empty)
  (mk : (bvar : HashMap Nat α) ->
    (fvar : HashMap String α) ->
    (app : ExprMap (ExprMap α)) ->
    (lam : ExprMap α) -> motive (ExprMap.mk bvar fvar app lam))
  [Nonempty (motive t)] : motive t := unsafeCast (β := motive t) <| @ExprMapImpl.casesOn.{u} α (unsafeCast motive) (unsafeCast t) (unsafeCast empty) (unsafeCast mk)

@[implemented_by ExprMap.casesOn_impl]
opaque ExprMap.cases
  {α : Type}
  [Nonempty α]
  {motive : ExprMap α -> Sort u}
  (t : ExprMap α)
  (empty : motive ExprMap.empty)
  (mk : (bvar : HashMap Nat α) ->
    (fvar : HashMap String α) ->
    (app : ExprMap (ExprMap α)) ->
    (lam : ExprMap α) -> motive (ExprMap.mk bvar fvar app lam))
  [Nonempty (motive t)]
  : motive t

attribute [elab_as_elim, cases_eliminator] ExprMap.cases

variable {α : Type} [Nonempty α]

structure BVMap where
  i : Nat
  env : HashMap String Nat

def BVMap.empty : BVMap := ⟨0, {}⟩

def BVMap.add : String -> BVMap -> BVMap := 
  fun v bvm => BVMap.mk (BVMap.i bvm).succ <| (BVMap.env bvm).insert v bvm.i

def BVMap.find? (s : String) (bvm : BVMap) := bvm.env.get? s

def ExprMap.toOpt : ExprMap α -> Option (ExprMap α) :=
  fun x => x.cases .none (fun _ _ _ _ => .some x)

def ExprMap.ofOpt : Option (ExprMap α) -> ExprMap α
| .none => .empty
| .some x => x

partial def ExprMap.union {α} [Nonempty α] (f : α -> α -> Option α) (ea eb : ExprMap α) : ExprMap α :=
  ea.cases eb
    fun bvar fvar app lam => eb.cases ea 
      fun bvar' fvar' app' lam' => 
        let new_bvar := HashMap.union bvar bvar'
        let new_fvar := HashMap.union fvar fvar'
        let new_app := ExprMap.union (α := ExprMap α) (fun x y => (ExprMap.union f x y).toOpt) app app'
        let new_lam := ExprMap.union f lam lam'
        .mk new_bvar new_fvar new_app new_lam

inductive Expr
| var (s : String)
| app (e e' : Expr)
| lam : String -> Expr -> Expr

partial def ExprMap.update {α} [Nonempty α] : Expr -> (Option α -> Option α) -> ExprMap α -> ExprMap α := 
  fun e f em => 
    let rec go {α} [Nonempty α] : BVMap -> Expr -> (Option α -> Option α) -> ExprMap α -> ExprMap α :=
      fun bvm e f em =>
        em.cases 
          (go bvm e f .empty)
          (fun bvar fvar app lam => 
            match e with
            | .var s => match BVMap.find? s bvm with
              | .some x => .mk (bvar.alter x f) fvar app lam
              | .none => .mk bvar (fvar.alter s f) app lam
            | .app e' e'' =>
              let r := go bvm e' (fun em' => ExprMap.toOpt (go bvm e'' f (ExprMap.ofOpt em'))) app
              .mk bvar fvar r lam
            | .lam s e' =>
              .mk bvar fvar app (go (BVMap.add s bvm) e' f lam))
    go BVMap.empty e f em


