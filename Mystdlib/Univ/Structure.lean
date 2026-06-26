import Mystdlib.Univ.Free.Basic
import Mystdlib.Decidable
import Mystdlib.DMap.Map.Lemmas


structure Structure where
  toMap : Map String Univ.Code

namespace Structure

instance : Membership String Structure where
  mem := fun s str => str ∈ s.toMap

theorem mem_iff_mem_toMap
  {stct : Structure}
  {k : String}
  : k ∈ stct <-> k ∈ stct.toMap := by
    simp [Membership.mem]

instance {str : String} {stct : Structure} : Decidable (str ∈ stct) := by
  simp [Membership.mem]
  infer_instance

def ofList (l : List (String × Univ.Code)) : Structure :=
  .mk <| .ofList l

def fields (stct : Structure) : List String :=
  stct.toMap.keys


def get (str : String) (stct : Structure) (h : str ∈ stct) : Univ.Code :=
  stct.toMap.get str h

structure Term (univ : Univ) where
  toMap : Map String ((code : univ.Domain) × code.decode)

instance : Membership String (Term univ) where
  mem := fun t str => str ∈ t.toMap


theorem Term.mem_iff_mem_toMap
  {stct : Term univ}
  {k : String}
  : k ∈ stct <-> k ∈ stct.toMap := by
    simp [Membership.mem]

instance {str : String} {t : Term univ} : Decidable (str ∈ t) := by
  simp [Membership.mem]
  infer_instance

def Term.getFieldCode (str : String) (t : Term univ) (h : str ∈ t) : Univ.Code :=
  (t.toMap.get str h).fst.val

def Term.getFieldTerm (str : String) (t : Term univ) (h : str ∈ t) :=
  (t.toMap.get str h).snd

def SatisfiedBy (stct : Structure) (term : Term univ) : Prop :=
  ∀(k : String) (h : k ∈ stct), ∃(h' : k ∈ term), stct.get k h = term.getFieldCode k h'

instance {term : Term univ} {stct : Structure} : Decidable (∀k, k ∈ stct -> k ∈ term) := by
  simp [mem_iff_mem_toMap, Term.mem_iff_mem_toMap]
  infer_instance

instance {term : Term univ} {stct : Structure} : Decidable (∀k, k ∈ term -> k ∈ stct) := by
  simp [mem_iff_mem_toMap, Term.mem_iff_mem_toMap]
  infer_instance

instance : Decidable (SatisfiedBy stct term) := by
  unfold SatisfiedBy
  have := Map.entryDecidableBAll_key_getValueCast stct.toMap (p := fun str code => ∃h : str ∈ term, code = Term.getFieldCode str term h)
  simp only [mem_iff_mem_toMap, get]
  infer_instance
