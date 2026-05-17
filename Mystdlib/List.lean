import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Lattice
import Mathlib.Data.List.Fold

namespace List

theorem flatMap_unpack_as_append_1
  (f : α -> β)
  (g : α -> β)
  (l : List α)
  : (l.map f ++ l.flatMap (singleton ∘ g)).Perm (l.flatMap (fun x => f x :: (singleton ∘ g) x)) :=
  List.map_append_flatMap_perm l f (singleton ∘ g)

theorem flatMap_unpack_as_append_2
  (f : α -> β)
  (l : List α)
  : l.flatMap (singleton ∘ f) = l.map f := by
    rw [<- List.flatMap_pure_eq_map]
    simp [pure, singleton]

theorem flatMap_unpack_as_append
  (f : α -> β)
  (g : α -> β)
  (l : List α)
  : (l.map f ++ l.map g).Perm (l.flatMap (fun x => [f x, g x])) := by
    rw (occs := [2]) [<- flatMap_unpack_as_append_2]
    apply flatMap_unpack_as_append_1

theorem diff_len_leq
  {x y : List α}
  [BEq α]
  [LawfulBEq α]
  : (List.diff x y).length ≤ x.length := by
    rw [List.diff_eq_foldl]
    unfold List.foldl
    split; grind; expose_names
    rw [<- List.diff_eq_foldl, <- List.diff_erase]
    induction l; simp [List.length_erase_le]; expose_names
    simp
    rw [<- List.diff_erase]
    grind

theorem diff_strict_sublist_len_lt
  {x y : List α}
  [BEq α] [LawfulBEq α]
  (h : List.Sublist x y)
  (h' : y.length < x.length)
  : (List.diff x y).length < x.length := by
    have := List.diff_sublist x y
    have : (List.diff x y).length ≠ x.length := by grind
    have := diff_len_leq (x := x) (y := y)
    grind

theorem min_append
  {x y : List α}
  {h : ¬ x.isEmpty}
  {h' : ¬ y.isEmpty}
  [Min α]
  [Std.Associative (min : α → α → α)]
  : (x ++ y).min (by simp_all) = min (x.min (by grind)) (y.min (by grind)) := by
    let x :: xs := x
    let y :: ys := y
    simp [List.min, List.foldl_assoc]

theorem min_append_mem
  {x y : List α}
  {h : ¬ x.isEmpty}
  {h' : ¬ y.isEmpty}
  [Min α]
  [Std.Associative (min : α -> α -> α)]
  [Std.MinEqOr α]
  : min (x.min (by grind)) (y.min (by grind)) ∈ (x ++ y) := by
    rw [<- min_append]
    apply List.min_mem
    grind; grind

theorem max_append
  {x y : List α}
  {h : ¬ List.isEmpty x}
  {h' : ¬ List.isEmpty y}
  [Max α]
  [Std.Associative (max : α -> α -> α)]
  : (x ++ y).max (by simp_all) = max (x.max (by grind)) (y.max (by grind)) := by
    let x :: xs := x
    let y :: ys := y
    simp [List.max, List.foldl_assoc]

instance [inst : Decidable (x ∈ l)] : Decidable (List.Mem x l) := by
  simp [Membership.mem] at inst
  assumption

@[grind ->]
theorem Mem_implies_mem
  {l : List α}
  : List.Mem a l -> a ∈ l := by
    simp [Membership.mem]


section
variable [BEq α] [LawfulBEq α]

instance : RightCommutative (List.erase (α := α)) where
  right_comm := by grind

theorem empty_inter_not_mem
  {x y : List α}
  : x.inter y = [] -> ∀a ∈ x, a ∉ y := by
    intro h
    rw [List.inter, List.filter_eq_nil_iff] at h
    grind


theorem empty_inter_implies_full_diff
  {x y : List α}
  : x.inter y = [] -> x.diff y = x := by
    intro h
    have := empty_inter_not_mem h
    rw [List.diff_eq_foldl]
    induction y; grind; expose_names; simp_all
    have thisa := @List.erase_of_not_mem α _ _ head x (by grind)
    rw [thisa]
    apply tail_ih
    rw [List.inter] at *; simp_all

-- technique: use that sublists of equal length are identical and squeeze the middle of 
-- x.length ≤ (x.diff tail).length ≤ ((x.diff tail).erase head).length
theorem full_diff_implies_empty_inter 
  {x y : List α}
  : x.diff y = x -> x.inter y = [] := by
    intro h
    simp [List.inter]
    intro a ismem
    induction y; simp; expose_names
    rw [List.diff_cons_right] at h 
    grind [List.diff_cons_right, List.diff_sublist] 


theorem full_diff_iff_empty_inter
  {x y : List α}
  : x.diff y = x <-> x.inter y = [] := by
    grind [full_diff_implies_empty_inter, empty_inter_implies_full_diff]

theorem full_diff_iff_disjoint
  {x y : List α}
  : x.diff y = x <-> x.Disjoint y := by
    rw [full_diff_iff_empty_inter]
    simp [List.inter, List.Disjoint]

end

attribute [grind .] List.disjoint_symm
attribute [grind] List.Disjoint
attribute [grind] List.Subset


@[simp, grind ->]
theorem disjoint_of_subset
  {x y z : List α}
  {h : y ⊆ z}
  {h' : x.Disjoint z}
  : x.Disjoint y := by
    grind

@[simp, grind ->]
theorem disjoint_of_sublist
  {x y z : List α}
  {h : y.Sublist z}
  {h' : x.Disjoint z}
  : x.Disjoint y := by
    simp_all [Disjoint]
    grind

@[simp, grind .]
theorem apply_sublist_flatMap_of_mem
  {f : α -> List β}
  {l : List α}
  {ismem : a ∈ l}
  : (f a).Sublist (List.flatMap f l) := by
    simp [List.flatMap_def]
    apply List.sublist_flatten_of_mem 
    grind

theorem flatMap_subset_iff_forall_mem_apply_subset
  {f : α -> List β}
  {l : List α}
  : l.flatMap f ⊆ l' <-> ∀a ∈ l, f a ⊆ l' := by
    grind

  

instance : Trans (α := List α) (β := List α) (γ := List α) List.Subset List.Subset List.Subset  where
  trans := by grind

@[grind .]
theorem Pairwise.rel_getLast_norefl
  {l : List α}
  {p : α -> α -> Prop}
  {a : α}
  {h : a ∈ l}
  {h' : a ≠ l.getLast (by grind)}
  : l.Pairwise p -> p a (l.getLast (by grind)) := by
    intro h
    apply List.Pairwise.rel_dropLast_getLast (h := h)
    grind [List.mem_dropLast_of_mem_of_ne_getLast]

      

    
    




