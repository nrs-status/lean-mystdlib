import Mystdlib.List.NEList.Lemmas
import Mystdlib.Univ.Basic
import Mystdlib.Univ.BasicUniv

abbrev CodeList := NEList Univ.Code

namespace CodeList

def toProdType (univ : Univ) (typs : CodeList) (h : ∀typ ∈ typs, univ.SatisfiedBy typ) : Type :=
  match h' : typs with
  | ⟨code :: code' :: codes, _⟩ => univ.decode code (h _ (by grind)) × toProdType univ ⟨code' :: codes, by grind⟩ (by grind)
  | ⟨code :: .nil, _⟩ => univ.decode code (h _ (by grind))

def toFnType (univ : Univ) (typs : CodeList) (h : ∀typ ∈ typs, univ.SatisfiedBy typ) : Type :=
  let ⟨code :: codes, _⟩ := typs
  match h' : codes with
  | .nil => univ.decode code (h _ (by grind))
  | .cons x xs => univ.decode code (h _ (by grind)) -> toFnType univ ⟨codes, by grind⟩ (by grind)

def toProdType? (univ : Univ) (typs : CodeList) : Option Type :=
  if h : ∀typ ∈ typs, univ.SatisfiedBy typ
  then .some (toProdType univ typs h)
  else .none

def toFnType? (univ : Univ) (typs : CodeList) : Option Type :=
  if h : ∀typ ∈ typs, univ.SatisfiedBy typ
  then .some (toFnType univ typs h)
  else .none

def toTypeVec (univ : Univ) (typs : CodeList) (h : ∀typ ∈ typs, univ.SatisfiedBy typ) : Fin typs.length -> Type :=
  match hmatch : typs with
  | ⟨code :: .nil, _⟩ => fun | ⟨0, _⟩ => univ.decode code (h _ (by grind))
  | ⟨code :: code' :: codes, _⟩ => fun
  | ⟨0, _⟩ => univ.decode code (h _ (by grind))
  | ⟨Nat.succ n, _⟩ => toTypeVec univ ⟨code' :: codes, by grind⟩ (by grind) ⟨n, by grind [NEList.length]⟩

def toProdTypeMapping (univ : Univ) (typs : CodeList) (h : ∀typ ∈ typs, univ.SatisfiedBy typ) (f : Type -> Type) : Type :=
  match h' : typs with
  | ⟨code :: [], _⟩ => f (univ.decode code (h _ (by grind)))
  | ⟨code :: code' :: codes, _⟩ =>
    f (univ.decode code (h _ (by grind))) × toProdTypeMapping univ ⟨code' :: codes, by grind⟩ (by grind) f

end CodeList

abbrev HList (univ : Univ) := List univ.CodedTerm

namespace HList

def toCodeList (l : HList univ) (h : ¬ l.isEmpty) : CodeList :=
  ⟨l.map fun x => x.code, by simp_all⟩


def toProd {univ : Univ} (l : HList univ) (h : ¬ l.isEmpty) : CodeList.toProdType univ (l.toCodeList h) (by grind [toCodeList, Univ.CodedTerm]) :=
  match hmatch : l with 
  | x :: [] => by
    simp only [toCodeList, List.map_cons, List.map_nil, CodeList.toProdType]
    exact x.term
  | x :: x' :: xs => by
    simp only [toCodeList, List.map_cons]
    rw  [CodeList.toProdType]
    exact (x.term, toProd (x' :: xs) (by grind))

def toProdMapping (l : HList univ) (h : ¬ l.isEmpty) (F : Type -> Type) (f : ∀x ∈ l, x.type -> F x.type) : CodeList.toProdTypeMapping univ (l.toCodeList h) (by grind [toCodeList, Univ.CodedTerm]) F :=
  match hmatch : l with
  | x :: [] => by
    simp only [toCodeList, List.map_cons, List.map_nil, CodeList.toProdTypeMapping]
    exact f x (by grind) x.term
  | x :: x' :: xs => by
    simp only [toCodeList, List.map_cons]
    rw [CodeList.toProdTypeMapping]
    exact (f x (by grind) x.term, toProdMapping (x' :: xs) (by grind) F (fun t iselm xt => f t (by grind) xt))

def toProdZipping (l : HList univ) (h : ¬ l.isEmpty) (l' : List α) (h' : l.length = l'.length) : CodeList.toProdTypeMapping univ (l.toCodeList h) (by grind [toCodeList, Univ.CodedTerm]) (· × α) := 
  match l, l' with
  | x :: [], y :: [] => by
    simp [toCodeList, CodeList.toProdTypeMapping]
    exact (x.term, y)
  | x :: x' :: xs, y :: y' :: ys => by
    simp only [toCodeList, List.map_cons]
    rw [CodeList.toProdTypeMapping]
    exact ((x.term, y), toProdZipping (x' :: xs) (by grind) (y' :: ys) (by grind))

end HList


structure CodedFn (univ : Univ) where
  codes : CodeList
  one_lt_codes_len : 1 < codes.length
  codes_satisfy_univ : ∀code ∈ codes, univ.SatisfiedBy code
  fn : codes.toFnType univ codes_satisfy_univ


namespace CodedFn

def paramsCodeList (cfn : CodedFn univ) : CodeList :=
  cfn.codes.dropLast (by grind [CodedFn])

def returnTypeCode (cfn : CodedFn univ) : Univ.Code :=
  cfn.codes.getLast

theorem returnTypeCode_satisfies
  {cfn : CodedFn univ}
  : univ.SatisfiedBy cfn.returnTypeCode :=
  cfn.codes_satisfy_univ cfn.returnTypeCode <| by
    simp [returnTypeCode, NEList.getLast_mem]

abbrev returnType (cfn : CodedFn univ) : Type :=
  univ.decode cfn.returnTypeCode (by grind [returnTypeCode_satisfies])

abbrev returnTypeDomCode (cfn : CodedFn univ) : univ.Domain :=
  ⟨cfn.returnTypeCode, by grind [returnTypeCode_satisfies]⟩

def apply (cfn : CodedFn univ) (params : HList univ) (params_ne : ¬ params.isEmpty) (h : cfn.paramsCodeList = params.toCodeList params_ne) : cfn.returnType :=
  match hmatch : cfn with
  | ⟨⟨code :: code' :: [], _⟩, _, _, fn⟩ => by
    let x :: [] := params
    simp [CodeList.toFnType] at fn
    have : univ.decode code (by grind) = univ.decode x.code x.satisfies := by
      grind [paramsCodeList, NEList.dropLast, HList.toCodeList, Univ.Domain.decode]
    exact fn (cast (by grind) x.term)
  | ⟨⟨code :: code' :: code'' :: codes, _⟩, _, _, fn⟩ => by
    let x :: x' :: xs := params
    rw [CodeList.toFnType] at fn
    have : univ.decode code (by grind) = univ.decode x.code x.satisfies := by
      grind [paramsCodeList, NEList.dropLast, HList.toCodeList, Univ.Domain.decode]
    let nextCfn := CodedFn.mk 
      (univ := univ)
      ⟨code' :: code'' :: codes, by grind⟩
      (by grind [NEList.length])
      (by grind)
      (fn (cast (by grind) x.term))
    exact apply nextCfn (x' :: xs) (by grind) <| by
      simp_all [paramsCodeList, NEList.dropLast, HList.toCodeList]
      grind
    
def apply? (cfn : CodedFn univ) (params : HList univ) : Option (univ.decode cfn.returnTypeCode (by grind [returnTypeCode_satisfies])) :=
  if params_ne : 0 < params.length
  then if h : cfn.paramsCodeList = params.toCodeList (by simp_all; grind)
    then .some (apply cfn params (by grind) h)
    else .none
  else .none

/- delete if ends up unused
def paramType (cfn : CodedFn univ) : Type :=
  cfn.paramsCodeList.toProdType univ <| by
    grind [CodedFn, paramsCodeList, NEList.dropLast, List.dropLast_subset]




structure ParamHList (cfn : CodedFn univ) where
  hlist : HList univ
  not_empty : ¬ hlist.isEmpty
  welltyped : cfn.paramsCodeList = hlist.toCodeList not_empty

structure AppRecord (univ : Univ) (α : Type) (cfn : CodedFn univ) where
  args : List (α × univ.CodedTerm)
  args_not_empty : ¬ args.isEmpty
  welltyped : cfn.paramsCodeList = HList.toCodeList (args.map Prod.snd) (by simp_all)

def AppRecord.run (appRecord : AppRecord univ α cfn) : cfn.returnType :=
  CodedFn.apply _ (appRecord.args.map Prod.snd) (by grind [AppRecord]) appRecord.welltyped
-/




def _root_.HList.isParamHListOf (hlist : HList univ) (cfn : CodedFn univ) : Prop :=
  ∃h : ¬ hlist.isEmpty, cfn.paramsCodeList = hlist.toCodeList h

/-
structure ParamConstrainedFnAppRecord (cfn : CodedFn univ) {domcode : univ.Domain} (it : Nat × domcode.Term) (phl : List (Nat × univ.CodedTerm)) where
  phl_prodmap_is_param_hlist : HList.isParamHListOf (phl.map Prod.snd) cfn
  phl' : List (Nat × univ.CodedTerm)
  phl'_prodmap_is_param_hlist : HList.isParamHListOf (phl'.map Prod.snd) cfn
  phl'_sublist : phl'.Sublist ((it.1, it.2.toCodedTerm) :: phl)
  r : cfn.returnType
  r_is_phl'_app_result : r = cfn.apply (phl'.map Prod.snd) (by grind [HList.isParamHListOf]) (by grind [HList.isParamHListOf])

def ParamConstrainedFn (cfn : CodedFn univ) (domcode : univ.Domain) := (it : Nat × domcode.Term) -> (phl : List (Nat × univ.CodedTerm)) -> ParamConstrainedFnAppRecord cfn it phl

-/

/-
need to be able to get: 
  - position of non-distinguished args
  - position of distinguished arg
-/

/-
structure DistinguishedArgInfoResult (cfn : CodedFn univ) (icode : Univ.Code × Nat) (l : List (Univ.Code × Nat)) where
  info : List (Univ.Code × Nat)
  welltyped : info.map Prod.snd = l.map Prod.snd
  indexing_nodup : (icode.fst :: l.map Prod.fst).Nodup
  wellindexed : ((info.map Prod.fst).filter (· = icode.1)).Sublist (l.map Prod.fst)

def DistinguishedArgInfo (cfn : CodedFn univ) := (it : Univ.Code × Nat) -> (l : List (Univ.Code × Nat)) -> DistinguishedArgInfoResult cfn it l

def DistinguishedArgInfo.run (info : DistinguishedArgInfo cfn) (code : Univ.Code) : DistinguishedArgInfoResult cfn (code, cfn.paramsCodeList.length) cfn.paramsCodeList.toList.zipIdx :=
  info _ _
-/

def DistinguishedArgInfo.Raw (cfn : CodedFn univ) := 
  (icode : Univ.Code × Nat) -> Vector (Univ.Code × Nat) cfn.paramsCodeList.length -> List (Univ.Code × Nat)
  
namespace DistinguishedArgInfo.Raw
  
def run {cfn : CodedFn univ} (icode_code : Univ.Code) (info : DistinguishedArgInfo.Raw cfn) : List (Univ.Code × Nat) :=
  info (icode_code, 0) ⟨List.toArray (cfn.paramsCodeList.toList.zipIdx 1), by grind [NEList.length, List.length_zipIdx]⟩ 

def distinguishedArgPos (icode_code : Univ.Code) (info : Raw cfn) : Option Nat := 
  (info.run icode_code).findIdx? (·.2 = 0)



