import Mystdlib.Mathlib.WType
import Mystdlib.DMap.Set.Defs
import Mystdlib.DMap.Set.Lemmas
import Mystdlib.DMap.Map.Lemmas


structure Univ where
  inner : Map String ((n : Nat) × (Vector Type n -> Type))

namespace Univ 

def arities (univ : Univ) : Map String Nat :=
  univ.inner.map fun _ x => x.fst

instance : Membership String Univ where
  mem := fun univ str => str ∈ univ.inner

instance {k : String} {univ : Univ} : Decidable (k ∈ univ) := by
  simp [Membership.mem]
  infer_instance

theorem mem_iff_mem_arities
  {univ : Univ}
  {k : String}
  : k ∈ univ <-> k ∈ univ.arities := by
    rw [Membership.mem, instMembershipString, arities, <- Map.mem_map]

def get (k : String) (univ : Univ) (h : k ∈ univ) : (n : Nat) × (Vector Type n -> Type) :=
  univ.inner.get k (by simp_all [Membership.mem])

def get? (k : String) (univ : Univ) :=
  univ.inner.get? k
    
def getArity (k : String) (univ : Univ) (h : k ∈ univ) : Nat :=
  (univ.inner.get k (by simp_all [Membership.mem])).1

def getInterpretation (k : String) (univ : Univ) (h : k ∈ univ) : Vector Type (univ.getArity k h) -> Type :=
  (univ.inner.get k _).2


abbrev Code := WType.Free String

namespace Code

def repr (code : Code) : String :=
  code.elim _ fun ⟨head, tail⟩ =>
    if head.2 = 0
    then head.1
    else "(" ++ head.1 ++ " " ++ String.intercalate " " (List.ofFn tail) ++ ")"

instance : Repr Code where
  reprPrec := fun x _ => x.repr

def head (code : Code) : String × Nat := 
  WType.head code

def arity (code : Code) : Nat := 
  code.head.2

def typ (code : Code) : String :=
  code.head.1

def tail (code : Code) : Fin code.arity -> Code :=
  fun fin => (WType.tail code) fin

abbrev mk (typ : String) (arity : Nat) (subterms : List Code) (h : subterms.length = arity := by simp) : Code :=
  WType.mk (typ, arity) (h ▸ subterms.get)

instance : EmptyCollection (Vector Code 0) where
  emptyCollection := ⟨#[], by simp⟩

abbrev mk' (typ : String) : Code := 
  WType.mk (typ, 0) (∅ : Vector Code 0).get

end Code

inductive SatisfiedBy (univ : Univ) : Code -> Prop 
| intro {codeNode : String} : (h : codeNode ∈ univ) -> (cont : Fin (univ.getArity codeNode h) -> Code) -> (∀i, univ.SatisfiedBy (cont i)) -> univ.SatisfiedBy (WType.mk (codeNode, univ.getArity codeNode h) cont)


theorem SatisfiedBy_congr_aux
  {n m : Nat}
  {str tail}
  (eq : n = m)
  : @WType.mk (String × Nat) (fun x => Fin x.2) (str, n) tail = WType.mk (str, m) fun i => tail ⟨i, by grind⟩ := by 
  subst eq
  simp_all [Fin.eta]

theorem SatisfiedBy_congr
  {univ : Univ} {tail}
  (mem : head.fst ∈ univ)
  (htail : ∀i, univ.SatisfiedBy (tail i))
  (hsnd : head.snd = univ.getArity head.fst mem)
  : univ.SatisfiedBy ⟨head, tail⟩ := by
    rcases head with ⟨fst, snd⟩
    simp_all
    rw [SatisfiedBy_congr_aux hsnd]
    constructor
    grind

theorem head_mem_of_SatisfiedBy
  {head tail}
  (h : SatisfiedBy univ ⟨head, tail⟩)
  : head.fst ∈ univ := by
    grind [SatisfiedBy]

theorem SatisfiedBy_child
  {head tail}
  {h : SatisfiedBy univ ⟨head, tail⟩}
  : ∀i, SatisfiedBy univ (tail i) := by
    cases h
    grind

theorem not_SatisfiedBy_of_not_mem
  {univ : Univ}
  {code : Code}
  : ¬ code.head.fst ∈ univ -> ¬ univ.SatisfiedBy code := by
    intro h wf
    cases wf
    simp [Code.head, WType.head] at h
    grind

theorem not_SatisfiedBy_of_get_neq_arity
  {univ : Univ}
  {code : Code}
  {h}
  : univ.getArity code.head.fst h ≠ code.head.snd -> ¬ univ.SatisfiedBy code := by
    contrapose
    intro w
    cases w
    congr
    
theorem not_SatisfiedBy_of_child_not_wf
  {univ : Univ}
  {code : Code}
  (i)
  : ¬ univ.SatisfiedBy (code.tail i) -> ¬ univ.SatisfiedBy code := by
    intro h wf
    cases wf
    simp [Code.tail, WType.tail] at h
    grind

theorem not_SatisfiedBy_of_child_not_mem
  {univ : Univ}
  {code : Code}
  (i)
  : ¬ (code.tail i).head.fst ∈ univ -> ¬ univ.SatisfiedBy code := by
    intro h
    apply not_SatisfiedBy_of_child_not_wf i
    apply not_SatisfiedBy_of_not_mem
    assumption


def SatisfiedBy_decidable {univ : Univ} : Decidable (univ.SatisfiedBy code) :=
  match hmatch : code with
  | WType.mk (fst, snd) tail =>
    if h : ∀i, (SatisfiedBy_decidable (code := tail i) (univ := univ)).decide = true
    then if h' : fst ∈ univ
      then if h'' : univ.getArity fst h' = snd
        then .isTrue <| by
          subst h''
          grind [SatisfiedBy.intro]
        else .isFalse <| by
          apply not_SatisfiedBy_of_get_neq_arity
          <;> grind [Code.head, WType.head]
      else .isFalse <| by
        apply not_SatisfiedBy_of_not_mem h'
    else .isFalse <| by
      simp only [decide_eq_true_eq, not_forall] at h
      obtain ⟨_, h⟩ := h
      apply not_SatisfiedBy_of_child_not_wf _ h
termination_by code.depth
decreasing_by
  · apply WType.depth_lt_depth_mk 
  · apply WType.depth_lt_depth_mk 
  · apply WType.depth_lt_depth_mk 
  · subst h'' 
    expose_names
    have thisa := WType.depth_lt_depth_mk (α := (String × Nat)) (β := fun x => Fin x.2) (f := tail_1) (fst, snd) i
    grind
  · subst h'' 
    expose_names
    have thisa := WType.depth_lt_depth_mk (α := (String × Nat)) (β := fun x => Fin x.2) (f := tail_1) (fst, _) i
    grind
  · subst h'' 
    grind
  · subst h'' 
    expose_names
    have thisa := WType.depth_lt_depth_mk (α := (String × Nat)) (β := fun x => Fin x.2) (f := tail_1) (fst, _) i
    grind
  · expose_names
    have thisa := WType.depth_lt_depth_mk (α := (String × Nat)) (β := fun x => Fin x.2) (f := tail) (fst, _)
    grind
  · expose_names
    have thisa := WType.depth_lt_depth_mk (α := (String × Nat)) (β := fun x => Fin x.2) (f := tail) (fst, _)
    grind

instance {univ : Univ} : Decidable (univ.SatisfiedBy code) := SatisfiedBy_decidable


def decode (univ : Univ) (code : Univ.Code) (h : univ.SatisfiedBy code) : Type :=
  let ⟨head, tail⟩ := code
  let aux := univ.get head.fst (by grind [Univ.head_mem_of_SatisfiedBy])
  aux.2 (.ofFn fun i => decode univ (tail (cast ?_ i)) (Univ.SatisfiedBy_child (h := h) (cast ?_ i)))
where finally
  all_goals (cases h; subst aux; simp [Univ.getArity, Univ.get])

def decode? (univ : Univ) (code : Univ.Code) : Option Type :=
  if h : univ.SatisfiedBy code
  then decode univ code h
  else .none

def Domain (univ : Univ) := { code // univ.SatisfiedBy code }

def Domain.decode {univ : Univ} (code : univ.Domain) : Type := 
  univ.decode code.val code.property

structure CodedTerm (univ : Univ) where
  code : Code
  satisfies : univ.SatisfiedBy code
  term : univ.decode code satisfies

abbrev CodedTerm.type (ct : CodedTerm univ) : Type :=
  univ.decode ct.code ct.satisfies

structure Domain.Term (domcode : Domain univ) where
  term : domcode.decode

def Domain.Term.toCodedTerm {domcode : Univ.Domain univ} (t : domcode.Term) : univ.CodedTerm where
  code := domcode.val
  satisfies := domcode.property
  term := t.term

instance : Union Univ where
  union := fun univ univ' => ⟨univ.inner ∪ univ'.inner⟩

theorem union_def
  {x y : Univ}
  : x ∪ y = ⟨x.inner ∪ y.inner⟩ := by
    simp [Union.union]

theorem mem_union_disj_of_mem
  {x y : Univ}
  {k : String}
  : k ∈ x ∪ y <-> k ∈ x ∨ k ∈ y := by
    apply DMap.mem_union_disj_of_mem

theorem mem_union_of_left
  {x y : Univ}
  {k : String}
  (mem : k ∈ x)
  : k ∈ x ∪ y := by
    apply DMap.mem_union_of_left
    simp_all [Membership.mem, Map.containsKey]


theorem mem_union_of_right
  {x y : Univ}
  {k : String}
  (mem : k ∈ y)
  : k ∈ x ∪ y := by
    apply DMap.mem_union_of_right
    simp_all [Membership.mem, Map.containsKey]


theorem getArity_union_of_mem_right
  {x y : Univ}
  (mem : k ∈ y)
  : (x ∪ y).getArity k (by grind [mem_union_of_right]) = y.getArity k mem := by
    simp [getArity]
    congr 1
    apply DMap.getValueCast_union_of_mem_right


theorem getArity_union_of_mem_left_and_not_mem_right
  {x y : Univ}
  (mem : k ∈ x)
  (notmem : k ∉ y)
  : (x ∪ y).getArity k (by grind [mem_union_of_left]) = x.getArity k mem := by
    simp [getArity]
    congr 1
    apply Map.getValueCast_union_of_mem_left_and_not_mem_right
      (by simp [mem_iff_mem_arities, arities, <- Map.mem_map] at mem; grind [Map.mem_union_of_left])
      (by simp_all [Membership.mem])

def Disjoint (x y : Univ) : Prop :=
  ∀k, k ∈ x -> k ∉ y
  deriving Decidable

theorem getArity_Disjoint_union_of_mem_left
  {x y : Univ}
  (hdisj : x.Disjoint y)
  (mem : k ∈ x)
  : (x ∪ y).getArity k (by grind [mem_union_of_left]) = x.getArity k mem := by
    apply getArity_union_of_mem_left_and_not_mem_right
    grind [Disjoint]

theorem satisfies_union_of_satisfies_right
  {x y : Univ}
  (h : y.SatisfiedBy code)
  : (x ∪ y).SatisfiedBy code := by
    obtain ⟨ismem, tail, ih⟩ := h
    rename_i codeNode
    suffices getArity codeNode y ismem = getArity codeNode (x ∪ y) (by grind [mem_union_of_right]) by
      rw [SatisfiedBy_congr_aux this]
      constructor
      rintro ⟨n, lt⟩
      apply satisfies_union_of_satisfies_right
      simp_all
    grind [getArity_union_of_mem_right]
termination_by code.depth
decreasing_by
  unfold Code WType.Free at *
  expose_names
  have := WType.depth_lt_depth_mk 
    (α := String × Nat) 
    (β := fun x => Fin x.2)
    (a := (codeNode, getArity codeNode y (by grind)))
    (f := tail)
    ⟨n, by grind⟩
  grind

theorem satisfies_Disjoint_union_of_satisfies_left
  {x y : Univ}
  (hdisj : x.Disjoint y)
  (satisfies : x.SatisfiedBy code)
  : (x ∪ y).SatisfiedBy code := by
    obtain ⟨ismem, tail, ih⟩ := satisfies
    rename_i codeNode
    suffices getArity codeNode x ismem = getArity codeNode (x ∪ y) (by grind [mem_union_of_left]) by
      rw [SatisfiedBy_congr_aux this]
      constructor
      rintro ⟨n, lt⟩
      apply satisfies_Disjoint_union_of_satisfies_left
      <;> simp_all
    grind [getArity_Disjoint_union_of_mem_left]

theorem union_decode_eq_right_decode
  {x y : Univ}
  {code : Code}
  {h : y.SatisfiedBy code}
  : (x ∪ y).decode code (satisfies_union_of_satisfies_right h) = y.decode code h := by
    induction code with | mk head tail ih => ?_
    simp only [decode]
    conv =>
      left
      right
      right
      intro i
      rw [ih (h := by cases h; grind)]
    simp only [get, Map.get]
    rw! (castMode := .all) [union_def]
    rw! (castMode := .all) [Map.getValueCast_union_of_mem_right]
    · simp
    · have := head_mem_of_SatisfiedBy h
      simp_all [Membership.mem]

theorem Disjoint_union_decode_eq_left_decode
  {x y : Univ}
  {code : Code}
  {h : x.SatisfiedBy code}
  (hdisj : x.Disjoint y)
  : (x ∪ y).decode code (satisfies_Disjoint_union_of_satisfies_left hdisj h) = x.decode code h := by
    induction code with | mk head tail ih => ?_
    simp only [decode]
    conv =>
      left
      right
      right
      intro i
      rw [ih (h := by cases h; grind)]
    simp only [get, Map.get]
    rw! (castMode := .all) [union_def]
    have := Map.getValueCast_union_of_mem_left_and_not_mem_right 
      (by apply head_mem_of_SatisfiedBy h)
      (by simp [Disjoint, mem_iff_mem_arities, arities, <- Map.mem_map] at hdisj; apply hdisj; apply head_mem_of_SatisfiedBy h)
    rw! (castMode := .all) [this]
    simp

class DisjointUnivUnion (x y : Univ) where
  disjoint : x.Disjoint y

instance {x y : Univ} : Coe y.CodedTerm (x ∪ y).CodedTerm where
  coe := fun ⟨code, satisfies, term⟩ => ⟨code, Univ.satisfies_union_of_satisfies_right satisfies, cast (by symm; apply Univ.union_decode_eq_right_decode) term⟩

instance [DisjointUnivUnion x y] : Coe x.CodedTerm (x ∪ y).CodedTerm where
  coe := fun ⟨code, satisfies, term⟩ => ⟨code, Univ.satisfies_Disjoint_union_of_satisfies_left DisjointUnivUnion.disjoint satisfies, cast (by symm; apply Univ.Disjoint_union_decode_eq_left_decode; apply DisjointUnivUnion.disjoint) term⟩

class Codable (α : Type) (univ : Univ) (code : outParam Code) where
  satisfies : univ.SatisfiedBy code := by native_decide
  wf : univ.decode code satisfies = α := by cbv

instance [Codable α x code] [DisjointUnivUnion x y] : Codable α (x ∪ y) code where
  satisfies := Univ.satisfies_Disjoint_union_of_satisfies_left DisjointUnivUnion.disjoint (Codable.satisfies α)
  wf := by
    rw! [<- Codable.wf (α := α) (univ := x) (code := code)]
    apply Univ.Disjoint_union_decode_eq_left_decode
    apply DisjointUnivUnion.disjoint

instance [Codable α y code] : Codable α (x ∪ y) code where
  satisfies := Univ.satisfies_union_of_satisfies_right (Codable.satisfies α)
  wf := by
    rw! [<- Codable.wf (α := α) (univ := y) (code := code)]
    apply Univ.union_decode_eq_right_decode

def typeToCode α [Codable α univ code] := code

def typeToDomCode α [Codable α univ code] : univ.Domain :=
  ⟨code, Codable.satisfies α⟩

def mkTerm [Codable α univ code] (a : α) : univ.CodedTerm :=
  ⟨code, Codable.satisfies α, cast (by symm; apply Codable.wf) a⟩

class TypeFnGen (arity : Nat) (typ : outParam (Type 1)) where
  fn : (F : typ) -> Vector Type arity -> Type

instance : TypeFnGen 0 Type where
  fn := fun t _ => t

instance
  [inst : TypeFnGen n t]
  : TypeFnGen (Nat.succ n) (Type -> t) where
    fn := fun F v =>
      inst.fn (F v.head) v.tail

def mkUnivEntry (typ : String) (arity : Nat) [TypeFnGen arity t] (F : t) : String ×  (n : Nat) × (Vector Type n -> Type) :=
  (typ, ⟨arity, TypeFnGen.fn F⟩)

/- def CodedTerm.repr {univ : Univ} (t : univ.CodedTerm) [Repr t.type] : Std.Format := -/
/-   _root_.repr t.term -/


