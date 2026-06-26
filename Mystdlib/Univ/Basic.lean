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
    
def getArity (k : String) (univ : Univ) (h : k ∈ univ) : Nat :=
  (univ.inner.get k (by simp_all [Membership.mem])).1

def getInterpretation (k : String) (univ : Univ) (h : k ∈ univ) : Vector Type (univ.getArity k h) -> Type :=
  (univ.inner.get k _).2


abbrev Code := WType.Free String

inductive SatisfiedBy (univ : Univ) : Code -> Prop 
| intro {codeNode : String} : (h : codeNode ∈ univ) -> (cont : Fin (univ.getArity codeNode h) -> Code) -> (∀i, univ.SatisfiedBy (cont i)) -> univ.SatisfiedBy (.mk (codeNode, univ.getArity codeNode h) cont)


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
    simp [WType.head] at h
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
    simp [WType.tail] at h
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
  | .mk (fst, snd) tail =>
    if h : ∀i, (SatisfiedBy_decidable (code := tail i) (univ := univ)).decide = true
    then if h' : fst ∈ univ
      then if h'' : univ.getArity fst h' = snd
        then .isTrue <| by
          subst h''
          grind [SatisfiedBy.intro]
        else .isFalse <| by
          apply not_SatisfiedBy_of_get_neq_arity
          <;> grind [WType.head]
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

def Domain (univ : Univ) := { code // univ.SatisfiedBy code }

def Domain.decode {univ : Univ} (code : univ.Domain) : Type := 
  univ.decode code.val code.property

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

theorem union_decode_eq_right_decode
  {x y : Univ}
  {code : Code}
  {h : y.SatisfiedBy code}
  : (x ∪ y).decode code (satisfies_union_of_satisfies_right h) = y.decode code h := by
    induction code with | mk head tail ih => ?_
    simp [decode]
    conv =>
      left
      right
      right
      intro i
      rw [ih (h := by cases h; grind)]
    simp [get, Map.get]
    rw! (castMode := .all) [union_def]
    simp
    rw! (castMode := .all) [Map.getValueCast_union_of_mem_right]
    · simp
    · have := head_mem_of_SatisfiedBy h
      simp_all [Membership.mem]

class Codable (α : Type) (univ : Univ) where
  code : Code
  satisfies : univ.SatisfiedBy code
  wf : univ.decode code satisfies = α := by simp

instance [inst : Codable α y] : Codable α (x ∪ y) where
  code := inst.code
  satisfies := satisfies_union_of_satisfies_right inst.satisfies
  wf := by 
    have := inst.wf
    rw! (castMode := .all) (occs := [4]) [<- inst.wf]
    apply union_decode_eq_right_decode


def BasicUniv : Univ where
  inner := .ofList [
      ("nat", ⟨0, fun _ => Nat⟩),
      ("bool", ⟨0, fun _ => Bool⟩),
      ("unit", ⟨0, fun _ => Unit⟩),
      ("empty", ⟨0, fun _ => Empty⟩),
      ("string", ⟨0, fun _ => String⟩),
      ("format", ⟨0, fun _ => Lean.Format⟩),
      ("name", ⟨0, fun _ => Lean.Name⟩),
      ("array", ⟨1, fun v => Array v[0]⟩),
      ("list", ⟨1, fun v => List v[0]⟩),
      ("prod", ⟨2, fun v => Prod v[0] v[1]⟩),
      ("option", ⟨1, fun v => Option v[0]⟩)
    ]


--- 

/-
def wfterm (term : Univ.Code × Type) (univ : Univ) (h : univ.SatisfiedBy term.1) : Prop :=
  term.2 = univ.decode term.1 h

example : wfterm (.mk ("nat", 0) nofun, Nat) BasicUniv (by native_decide) := by
  unfold wfterm
  simp
  cbv
-/
