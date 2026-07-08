import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image


namespace Finset

def unattach
  {p : α -> Prop}
  {s : Finset { x // p x }}
  : Finset α :=
  s.map ⟨Subtype.val, Subtype.val_injective⟩


theorem mem_unattach_satisfies_prop
  {p : α -> Prop}
  {m : Finset { a // p a }}
  : ∀a, a ∈ m.unattach -> p a := by
    intro a h
    rw [unattach, Finset.mem_map] at h
    simp_all
    grind


theorem 
  mem_subtype_iff_mem_unattach
  {p : α -> Prop}
  {m : Finset { a // p a }}
  : ∀x, x ∈ m <-> x.val ∈ m.unattach ∧ p x := by
    simp [unattach]
    grind



