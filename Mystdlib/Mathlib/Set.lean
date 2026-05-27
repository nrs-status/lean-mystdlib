import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finite.Prod

attribute [grind .] Set.Finite.to_subtype
attribute [grind .] List.finite_toSet
attribute [grind .] Set.Finite.insert
attribute [grind .] Set.Finite.prod
attribute [grind .] Membership.mem.out

@[grind =]
theorem prop_mem_eq_setOf_mem
  {p : α -> Prop}
  {a : α}
  : Set.instMembership.mem p a = (a ∈ { x | p x }) := rfl
