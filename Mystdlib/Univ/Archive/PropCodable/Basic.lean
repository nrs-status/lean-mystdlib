import Mystdlib.General
import Mathlib.Data.W.Basic
import Mystdlib.Mathlib.Encodable
import Mystdlib.Tactics
import Mystdlib.FinsetLike.Basic


structure Univ where
  codeNodes : Finset String
  arities : codeNodes∋ -> Type
  decode : (σ : codeNodes∋) -> (arities σ -> Type u) -> Type u

abbrev Univ.Code (univ : Univ) := WType univ.arities

@[simp, grind]
def Univ.Code.decode {univ : Univ} (enc : univ.Code) : Type u :=
  let ⟨a, b⟩ := enc
  univ.decode a (fun i => recur (b i))

@[simp]
def merge_arities 
  (x y : Univ)
  : (x.codeNodes ∪ y.codeNodes)∋ → Type
  := fun z =>
    if h : z.val ∈ x.codeNodes
    then x.arities ⟨z.val, by grind⟩
    else if h' : z.val ∈ y.codeNodes
    then y.arities ⟨z.val, by grind⟩
    else by 
      exfalso
      grind



@[simp]
def merge_decode
  (x y : Univ)
  : (σ : (x.codeNodes ∪ y.codeNodes)∋) -> (merge_arities x y σ -> Type u) -> Type u :=
  fun ⟨a, b⟩ c => if h : a ∈ x.codeNodes
  then x.decode ⟨a, by grind⟩ (fun i => c (cast ?_ i))
  else y.decode ⟨a, by grind⟩ (fun i => c (cast ?_ i))
where finally
  · simp [merge_arities]; grind
  · simp [merge_arities]; grind

@[grind, simp]
def Univ.merge (x y : Univ) : Univ where
  codeNodes := x.codeNodes ∪ y.codeNodes
  arities := merge_arities x y
  decode := merge_decode x y

instance {x y : Univ} [∀σ, Encodable (x.arities σ)] [∀σ, Encodable (y.arities σ)] {σ} : Encodable ((Univ.merge x y).arities σ)  := by
  simp [Univ.merge, merge_arities]
  split; infer_instance
  split; infer_instance
  grind

instance {x y : Univ} [∀σ, Fintype (x.arities σ)] [∀σ, Fintype (y.arities σ)] {σ} : Fintype ((Univ.merge x y).arities σ) := by
  simp [Univ.merge, merge_arities]
  split; infer_instance
  split; infer_instance
  grind

instance {x y : Univ} [∀σ, Encodable (x.arities σ)] [∀σ, Encodable (y.arities σ)] [∀σ, Fintype (x.arities σ)] [∀σ, Fintype (y.arities σ)]  : Encodable (Univ.merge x y).Code := by
  simp [Univ.Code]
  apply @WType.instEncodable _ _ (fun _ => instFintypeAritiesMerge) (fun _ => instEncodableAritiesMerge)

instance {x y : Univ} [∀σ, Encodable (x.arities σ)] [∀σ, Encodable (y.arities σ)] [∀σ, Fintype (x.arities σ)] [∀σ, Fintype (y.arities σ)] : DecidableEq (Univ.merge x y).Code := Encodable.decidableEqOfEncodable _

instance {x y : Univ} [∀σ, Encodable (x.arities σ)] [∀σ, Encodable (y.arities σ)] [∀σ, Fintype (x.arities σ)] [∀σ, Fintype (y.arities σ)] : BEq (Univ.merge x y).Code := instBEqOfDecidableEq


syntax:max (name := encode_pdescr) ident "#" : term
macro_rules
| `($(x):ident#) => `(⟨$(Lean.Syntax.mkStrLit x.getId.toString)<:, (fun x => Empty.elim (cast (by simp) x))⟩)

class Codable (α : Type u) (univ : Univ) (code : univ.Code) : Prop where
  wf : code.decode = α := by simp

def code_merge_lift_left 
  {x y : Univ}
  : x.Code -> (x.merge y).Code
  | ⟨a, b⟩ => ⟨⟨a.val, by grind⟩, fun i => recur (b (cast ?_ i))⟩
where finally
  simp [Univ.merge, merge_arities]

theorem code_merge_lift_left_wf
  {x y : Univ}
  {z : x.Code}
  : z.decode = (code_merge_lift_left (y := y) z).decode := by
    induction z; simp [code_merge_lift_left, Univ.Code.decode, Univ.merge, merge_decode]
    congr
    funext
    grind

@[grind]
class Univ.AritiesAgree (x y : Univ) : Prop where
  arities_agree : ∀str, (h : str ∈ x.codeNodes) -> (h' : str ∈ y.codeNodes) -> x.arities str<: = y.arities str<:


def code_merge_lift_right
  {x y : Univ}
  [x.AritiesAgree y]
  : y.Code -> (x.merge y).Code
  | ⟨a, b⟩ => ⟨⟨a.val, by grind⟩, fun i => recur (b (cast ?_ i))⟩
where finally
  simp [Univ.merge, merge_arities]
  grind


@[grind]
class Univ.DecodesAgree (x y : Univ) extends Univ.AritiesAgree x y where
  decodes_agree : ∀str, (h : str ∈ x.codeNodes) -> (h' : str ∈ y.codeNodes) -> (cont : x.arities str<: -> Type u) -> x.decode str<: cont = y.decode str<: (cast !p cont)
  
theorem code_merge_lift_right_wf
  {x y : Univ}
  {z : y.Code}
  [x.DecodesAgree y]
  : z.decode = (code_merge_lift_right (x := x) z).decode := by
    induction z
    simp [code_merge_lift_right, Univ.Code.decode, Univ.merge, merge_decode]
    split <;> expose_names
    · have := @Univ.DecodesAgree.decodes_agree (str := a) (h := h) x y !p !p
      simp_all
      congr
      rw [eq_cast_iff_heq]
      apply Function.hfunext <;> grind
    · congr
      grind

instance [Codable α x code] : Codable α (Univ.merge x y) (code_merge_lift_left code) where
  wf := by
    rw [<- code_merge_lift_left_wf]
    apply Codable.wf

instance {x y : Univ} [inst : x.DecodesAgree y] {code : y.Code} [Codable α y code] : Codable α (Univ.merge x y) (code_merge_lift_right code) where
    wf := by
      rw [<- code_merge_lift_right_wf ..]
      apply Codable.wf

theorem decode_eq_type_of_codable
  [Codable typ univ code]
  : code.decode = typ := by
    apply Codable.wf









    



