import Mystdlib.TypeList.Basic
import Std

open Std

abbrev Circuit (univ : Type u) [DecidableEq univ] := HashMap (Nat × Nat) univ

namespace Circuit 

variable {univ : Type} [DecidableEq univ]

def ofInputEdges (inputCodes : Vector univ n) (inputIds : Vector Nat n) (center : Nat) (h : center ∉ inputIds) : Circuit univ :=
  let r : Vector ((Nat × Nat) × univ) n := 
    inputIds.mapFinIdx fun i x lt => ((x, center), inputCodes[i])
  .ofArray r.toArray

def ofOutputEdges (outputCodes : Vector univ n) (center : Nat) (outputIds : Vector Nat n)  (h : center ∉ outputIds) : Circuit univ :=
  let r : Vector ((Nat × Nat) × univ) n := 
    outputIds.mapFinIdx fun i x lt => ((center, x), outputCodes[i])
  .ofArray r.toArray

def ofNodeCodes (inputCodes outputCodes : Array univ) : Circuit univ :=
  let r := ofInputEdges (Vector.mk (n := inputCodes.size) inputCodes rfl) (Vector.range' 1 _) 0 (by grind)
  let r' := ofOutputEdges (Vector.mk (n := outputCodes.size) outputCodes rfl) 0 (Vector.range' (if inputCodes.size = 0 then 1 else inputCodes.size) _) (by grind)
  r.union r'

def ids (c : Circuit univ) : List Nat := c.keys.flatMap fun (a, b) => [a, b] |>.eraseDups

theorem ids_equiv_perm
  {c c' : Circuit univ}
  : c.Equiv c' -> c.ids.Perm c'.ids := sorry

def nodeCodesOfIdx (c : Circuit univ) (idx : Nat) : Array univ × Array univ :=
  let r := c.toArray.filterMap fun ((a, b), u) => if b = idx 
    then .some (Sum.inl u) 
    else if a = idx
    then .some (Sum.inr u)
    else .none
  r.foldl (fun (l, r) x => match x with | .inl x' => (l.push x', r) | .inr x' => (l, r.push x')) (∅, ∅)

theorem nodeCodesOfIdx_mem_iff_nontrivial
  {c : Circuit univ}
  {idx : Nat}
  : idx ∈ c.ids <-> ¬ (c.nodeCodesOfIdx idx).fst.isEmpty ∨ ¬ (c.nodeCodesOfIdx idx).snd.isEmpty := by
    sorry

theorem nodeCodesOfIdx_equiv_eq
  {c c' : Circuit univ}
  {h : c.Equiv c'}
  : c.nodeCodesOfIdx idx = c'.nodeCodesOfIdx idx := sorry

def typeOfNodeCodes (decode : univ -> Type u) (nodeCodes : Array univ × Array univ) (h : ¬ nodeCodes.fst.isEmpty ∨ ¬ nodeCodes.snd.isEmpty) := 
  if h : nodeCodes.fst.isEmpty then TypeList.toProdType ⟨nodeCodes.snd.toList.map decode, by simp_all⟩
  else if h' : nodeCodes.snd.isEmpty then TypeList.toProdType ⟨nodeCodes.fst.toList.map decode, by simp_all⟩
  else TypeList.toDFinVecFunType ⟨nodeCodes.fst.toList.map decode, by simp_all⟩ ⟨nodeCodes.snd.toList.map decode, by simp_all⟩

def typeOfIdx (c : Circuit univ) (decode : univ -> Type u) (idx : Nat) (h : idx ∈ c.ids) :=
  typeOfNodeCodes decode (c.nodeCodesOfIdx idx) (by grind [nodeCodesOfIdx_mem_iff_nontrivial])

theorem typeOfIdx_equiv_eq
  {c c' : Circuit univ}
  {h : c.Equiv c'}
  {h'}
  : typeOfIdx c decode n h' = typeOfIdx c' decode n (by rwa [<- List.Perm.mem_iff (ids_equiv_perm h)]) := sorry

def FunctionNode (c : Circuit univ) (idx : Nat) : Prop :=
  ¬ (c.nodeCodesOfIdx idx).fst.isEmpty ∧ ¬ (c.nodeCodesOfIdx idx).snd.isEmpty


def Interpretation (c : Circuit univ) (decode : univ -> Type u) := 
  (idx : Nat) -> (h : c.FunctionNode idx) -> c.typeOfIdx decode idx (by simp [FunctionNode] at h; grind [nodeCodesOfIdx_mem_iff_nontrivial])

def Valuation (c : Circuit univ) (decode : univ -> Type u) := 
  DHashMap { i // i ∈ c } fun edge => decode (c.get edge.val edge.property)

/-
inductive Univ | bool
deriving DecidableEq, Repr

abbrev Univ.decode : Univ -> Type
| .bool => Bool

abbrev andCircuit : Circuit Univ := .ofNodeCodes #[.bool, .bool] #[.bool]

theorem mythm_aux : andCircuit.nodeCodesOfIdx 0 = (#[.bool, .bool], #[.bool]) := by
  native_decide

theorem mythm : andCircuit.typeOfIdx Univ.decode 0 (by native_decide) = (Bool -> Bool -> (i : Fin 1) -> [Bool].get i) := by
  simp [typeOfIdx, mythm_aux, typeOfNodeCodes, TypeList.toDFinVecFunType, TypeList.concat, TypeList.toFunType, Univ.decode, TypeList.toDFinVec, DFinVec, TypeList.length, TypeList.get]
  rw [mythm_aux]
  simp [Univ.decode]
  rfl

theorem zero_only_andCircuit_fnnode
  : andCircuit.FunctionNode idx <-> idx = 0 := sorry

def myinterp : andCircuit.Interpretation Univ.decode := 
  fun idx fnnode => by
    have : idx = 0 := by grind [zero_only_andCircuit_fnnode]
    subst this
    rw [mythm]
    exact fun x y 0 => by simp; exact x && y
-/














  



