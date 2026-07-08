import Std

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

-- HashSet grindset

attribute [grind .] Std.HashSet.mem_of_mem_union_of_not_mem_left
attribute [grind .] Std.HashSet.mem_of_mem_union_of_not_mem_right
attribute [grind .] Std.HashSet.mem_union_of_left
attribute [grind .] Std.HashSet.mem_union_of_right

-- HashMap grindset

attribute [grind .] Std.HashMap.nodup_keys 
attribute [grind .] Std.DHashMap.nodup_keys 
attribute [grind .] Std.TreeMap.nodup_keys 

-- Pairwise grindset

attribute [grind .] List.Pairwise.cons
