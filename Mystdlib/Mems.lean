
@[simp, grind]
abbrev Mems [Membership α γ] (y : γ) := { x : α // x ∈ y }

notation:max (name := Mems_pdescr) term "∋" => Mems term

syntax:max (name := Mems_mem_pdescr) term "∈" : term
macro_rules
| `($x∈) => do
  let stx <- `(⟨$x, by simp_all; grind⟩)
  return stx


instance [Membership α γ] [BEq α] [Hashable α] [LawfulHashable α] {y : γ} : LawfulHashable y∋ where
  hash_eq := by
    intro a b beq
    simp_all
    simp [hash]
    apply LawfulHashable.hash_eq
    grind
