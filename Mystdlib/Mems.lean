
@[simp, grind]
abbrev Mems [Membership α γ] (y : γ) := { x : α // x ∈ y }

notation:max (name := Mems_pdescr) term "∋" => Mems term

syntax:max (name := Mems_mem_pdescr) term "∈" : term
macro_rules
| `($x∈) => do
  let stx <- `(⟨$x, by simp_all; grind⟩)
  return stx

