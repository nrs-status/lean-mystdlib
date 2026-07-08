import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Multiset.Defs


namespace Multiset

def unattach {p : α -> Prop} (m : Multiset { x // p x }) : Multiset α :=
  m.map Subtype.val

theorem mem_unattach_satisfies_prop
  {p : α -> Prop}
  {m : Multiset { a // p a }}
  : ∀a, a ∈ m.unattach -> p a := by
    intro a h
    rw [unattach, Multiset.mem_map] at h
    grind

theorem 
  mem_subtype_iff_mem_unattach
  {p : α -> Prop}
  {m : Multiset { a // p a }}
  : ∀x, x ∈ m <-> x.val ∈ m.unattach ∧ p x := by
    simp [unattach]
    grind

variable {α : Type u} {p : α -> Prop} {m : Multiset { a // p a }}
theorem 
  unattach_card
  : m.card = m.unattach.card := by
    simp [unattach]

theorem
  unattach_nodup
  : m.Nodup -> m.unattach.Nodup := by
    simp [unattach]
    apply Multiset.Nodup.map 
    apply Subtype.val_injective












    


    


