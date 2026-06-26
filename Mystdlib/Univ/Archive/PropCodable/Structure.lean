import Mystdlib.Map.Misc
import Mystdlib.Univ.PropCodable.Basic

open Map.Set
structure Structure (univ : Univ) where
  fields : Map.Set String
  fieldsDef : Map' String univ.Code
  equiv : fieldsDef.keySet.Equiv fields

instance [DecidableEq univ.Code] : DecidableEq (Structure univ) := by
  simp [DecidableEq]
  intro a b
  cases a; cases b; expose_names
  simp
  infer_instance

namespace Structure

variable {univ : Univ}

def contains (s : Structure univ) (k : String) : Bool :=
  s.fields.contains k

def get (s : Structure univ) (k : String) (h : s.contains k) : univ.Code :=
  s.fieldsDef.get k <| by
    have := s.equiv
    rw [Map.Set.equiv_iff_contains] at this
    have := this k
    rw [Map.keySet_contains_iff] at this
    rw [this]
    simp [contains] at h
    assumption

def ofMap (m : Map' String univ.Code) : Structure univ where
  fields := m.keySet
  fieldsDef := m
  equiv := Map.equiv_self

structure Term₀ (s : Structure univ) where
  subterms : Map' String (Σcode : univ.Code, code.decode)
  equiv : subterms.keySet.Equiv s.fields
  --wf2 : ∀k, (h : k ∈ subterms) -> (s.get k _).decode = subterms.get k h

theorem Term₀.subterms_contains_iff_struct_contains
  {s : Structure univ}
  {t : Term₀ s}
  : ∀k, t.subterms.contains k <-> s.contains k := by
    intro k
    have := t.equiv
    rw [Map.Set.equiv_iff_contains] at this
    have := this k
    rw [contains, <- this, Map.keySet_contains_iff]

structure Term (s : Structure univ) extends Term₀ s where
  tagging : ∀k, (h : subterms.contains k) -> (subterms.get k h).fst = s.get k (by rwa [<- Term₀.subterms_contains_iff_struct_contains (t := toTerm₀)])

namespace Term

def get {s : Structure univ} (t : Term s) (k : String) (h : s.contains k) :=
  (t.subterms.get k (by rwa [Term₀.subterms_contains_iff_struct_contains]))

end Term

/- theorem decode_eq_type_of_codable -/
/-   [Codable typ univ code] -/
/-   : code.decode = typ := by -/
/-     apply Codable.wf -/

theorem term_get_decode_eq_of_codable
  {s : Structure univ}
  {t : Term s}
  {k : String}
  {h : s.contains k}
  : (code : univ.Code) -> [Codable α univ code] -> (t.get k h).fst = code -> (t.get k h).fst.decode = α := by
    intro _ _ h'
    subst h'
    apply decode_eq_type_of_codable
