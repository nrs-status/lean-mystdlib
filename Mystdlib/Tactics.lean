

syntax:max (name := close_pdescr) "close" : tactic
macro_rules
| `(tactic|close) => `(tactic|repeat first | split | rfl | infer_instance | native_decide | simp | simp_all | grind)

macro_rules
| `(tactic|decreasing_trivial) => `(tactic|grind)


-- Option grindset
attribute [grind .] Option.isSome_iff_ne_none

-- Array grindset
attribute [grind .] Array.isEmpty_iff_size_eq_zero

-- List grinset
attribute [grind .] List.isEmpty_iff_length_eq_zero
