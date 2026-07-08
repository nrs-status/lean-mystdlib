import Mystdlib.List.NEList.Defs

namespace NEList

@[grind =]
theorem mem_iff_mem_toList
  {l : NEList α}
  {a : α}
  : a ∈ l <-> a ∈ l.toList := by
    simp [Membership.mem]

/-
List.getLast_mem 📋 Init.Data.List.Lemmas
{α : Type u_1} {l : List α} (h : l ≠ []) : l.getLast h ∈ l
-/

theorem getLast_mem
  {l : NEList α}
  : l.getLast ∈ l := by
    rcases l with ⟨toList, h⟩
    simp [NEList.getLast, mem_iff_mem_toList]

instance [DecidableEq α] : DecidableEq (NEList α) := by
  rintro ⟨toList, h⟩ ⟨toList', h'⟩
  simp only [NEList.mk.injEq]
  infer_instance
