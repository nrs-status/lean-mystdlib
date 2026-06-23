import Mystdlib.DMap.Defs
import Mystdlib.List.Foldl

open Std Internal

namespace DMap

variable {α : Type u} [BEq α] {β : α -> Type v}

theorem distinct (m : DMap α β)
  : m.keys.Pairwise (fun (a b : α) => (a == b) = false) := by
    simp only [keys]
    apply m.distinctKeys.distinct

theorem emptyCollection_def
  : (∅ : DMap α β) = ⟨[], by simp⟩ := by
    simp [EmptyCollection.emptyCollection]

theorem union_def
  [PartialEquivBEq α]
  {m m' : DMap α β}
  : (m ∪ m') = m.insertList m'.toList := by
    simp [Union.union, union]

theorem mem_iff
  {m : DMap α β}
  {k : α}
  : k ∈ m <-> m.containsKey k := by
    simp [Membership.mem]

theorem keys_pairwise_not_beq
  {m : DMap α β}
  : m.keys.Pairwise (fun a b => (a == b) = false) := by
    apply List.DistinctKeys.distinct m.distinctKeys

theorem mem_union_disj_of_mem
  [PartialEquivBEq α]
  {m m' : DMap α β}
  {k : α}
  : k ∈ m ∪ m' <-> k ∈ m ∨ k ∈ m' := by
    simp only [union_def, mem_iff]
    rw [<- Bool.or_eq_true_iff, Bool.coe_iff_coe]
    apply List.containsKey_insertList_disj_of_containsKey

theorem mem_union_of_left
  [PartialEquivBEq α]
  {m m' : DMap α β}
  {k : α}
  (contains : k ∈ m)
  : k ∈ m ∪ m' := by
    rw [mem_union_disj_of_mem]
    simp_all

theorem mem_union_of_right
  [PartialEquivBEq α]
  {m m' : DMap α β}
  {k : α}
  (contains : k ∈ m')
  : k ∈ m ∪ m' := by
    rw [mem_union_disj_of_mem]
    simp_all

theorem mem_of_equiv
  [PartialEquivBEq α]
  {m m' : DMap α β}
  {k : α}
  (h : m.Equiv m')
  : k ∈ m <-> k ∈ m' := by
    rw [Equiv] at h
    simp only [mem_iff, Bool.coe_iff_coe]
    apply List.containsKey_of_perm h

theorem mem_iff_keys_contains
  [PartialEquivBEq α]
  {m : DMap α β}
  {k : α}
  : k ∈ m <-> m.keys.contains k := by
    simp [mem_iff, containsKey, keys, List.containsKey_eq_keys_contains]

theorem mem_keys_iff_mem
  [LawfulBEq α]
  {m : DMap α β}
  {k : α}
  : k ∈ m.keys <-> k ∈ m := by
    rw [keys, mem_iff]
    apply List.mem_keys_iff_contains

theorem insertList_congr
  [EquivBEq α]
  {m m' : DMap α β}
  {l l' : List ((a : α) × β a)}
  (h₁ : m.Equiv m')
  (h₂ : l.Perm l')
  (hd : l.DistinctKeys)
  : (m.insertList l).Equiv (m'.insertList l') := by
    simp only [Equiv, insertList]
    apply Std.Internal.List.insertList_congr
    <;> simp_all [Equiv, m.distinctKeys, m'.distinctKeys]

theorem union_congr
  [EquivBEq α]
  {m1 m2 m3 m4 : DMap α β}
  {h₁ : m1.Equiv m3}
  {h₂ : m2.Equiv m4}
  : (m1 ∪ m2).Equiv (m3 ∪ m4) := by
    simp [union_def]
    apply insertList_congr
    <;> simp_all [Equiv, m2.distinctKeys]

theorem keys_eq_map
  {m : DMap α β}
  : m.keys = m.toList.map Sigma.fst := by
    simp [keys, <- List.keys_eq_map]

theorem mem_iff_isSome_getValueCast?
  [LawfulBEq α]
  {m : DMap α β}
  {k : α}
  : k ∈ m <-> (m.getValueCast? k).isSome := by
    simp only [mem_iff, getValueCast?, containsKey, <-Std.Internal.List.containsKey_eq_isSome_getValueCast?]

theorem getValueCast?_eq_some_getValueCast
  [LawfulBEq α]
  {m : DMap α β}
  {k : α}
  (h : k ∈ m)
  : m.getValueCast? k = Option.some (m.getValueCast k h) := by
    simp [getValueCast?, getValueCast, <- List.getValueCast?_eq_some_getValueCast]

theorem toList_Nodup
  [LawfulBEq α]
  {m : DMap α β}
  : m.toList.Nodup := by
    unfold List.Nodup
    have := m.distinct
    rw [keys_eq_map] at this
    apply List.Pairwise.of_map (p := this)
    grind 

theorem keys_Nodup
  [LawfulBEq α]
  {m : DMap α β}
  : m.keys.Nodup := by
    unfold List.Nodup
    conv =>
      arg 1
      intro x y
      rw [<- beq_eq_false_iff_ne]
    apply m.distinct

theorem empty_isEmpty
  : (∅ : DMap α β).isEmpty := by
    simp [emptyCollection_def, isEmpty]

theorem isEmpty_iff_forall_mem
  [ReflBEq α]
  {m : DMap α β}
  : m.isEmpty <-> ∀a, ¬ a ∈ m := by
    simp only [isEmpty, mem_iff]
    rw [List.isEmpty_iff_forall_containsKey]
    simp [containsKey]

theorem mem_insertEntry_self
  [EquivBEq α]
  {m : DMap α β}
  {k : α}
  {v : β k}
  : k ∈ m.insertEntry k v := by
    simp only [mem_iff, containsKey]
    apply List.containsKey_insertEntry_self

theorem mem_insertEntry
  [PartialEquivBEq α]
  {m : DMap α β}
  {k a : α}
  {v : β k}
  : a ∈ m.insertEntry k v <-> k == a ∨ a ∈ m := by
    simp only [mem_iff, ← Bool.or_eq_true, Bool.coe_iff_coe]
    apply List.containsKey_insertEntry

theorem mem_insertEntry_of_mem
  [PartialEquivBEq α]
  {m : DMap α β}
  {k : α}
  (h : k ∈ m)
  : ∀k' v, k ∈ m.insertEntry k' v := by
    grind [mem_insertEntry]

theorem forall_mem_iff_forall_mem_getValueCast
  [LawfulBEq α]
  {ρ : (a : α) -> β a -> Prop}
  {m : DMap α β}
  : (∀x ∈ m.toList, ρ x.fst x.snd) <-> ∀a, (h : a ∈ m) -> ρ a (m.getValueCast a h) := by
    simp only [mem_iff, getValueCast]
    apply List.forall_mem_iff_forall_contains_getValueCast
    apply m.distinctKeys

theorem equiv_self
  {m : DMap α β}
  : m.Equiv m := by
    simp [Equiv]

theorem equiv_iff_getValueCast?_eq
  [LawfulBEq α]
  {m m' : DMap α β}
  : m.Equiv m' <-> ∀a, m.getValueCast? a = m'.getValueCast? a := by
    simp only [Equiv, getValueCast?]
    constructor
    · intro hperm a
      apply List.getValueCast?_of_perm m.distinctKeys hperm
    · intro h
      apply List.getValueCast?_ext
      <;> grind [m.distinctKeys, m'.distinctKeys]

theorem getValueCast_eq_of_equiv
  [LawfulBEq α]
  {m m' : DMap α β}
  : m.Equiv m' -> ∀a h h', m.getValueCast a h = m'.getValueCast a h' := by
    intro hequiv a h h'
    suffices Option.some (m.getValueCast a h) = Option.some (m'.getValueCast a h') by grind
    simp only [<- getValueCast?_eq_some_getValueCast]
    grind [equiv_iff_getValueCast?_eq]

theorem ofList_toList_eq_id
  [PartialEquivBEq α]
  {l : List ((a : α) × β a)}
  (h : l.DistinctKeys)
  : (ofList l).toList = l := by
    simp only [ofList, insertList, List.insertList_eq_foldl, reverse, emptyCollection_def]
    suffices l.foldl (fun acc next => List.insertEntry next.fst next.snd acc) [] = l.foldl (fun xs y => y :: xs) [] by
      grind [List.foldl_flip_cons_eq_append'] 
    apply List.insertList_foldl_cons_hom
    assumption
      

theorem ofList_mem_iff_containsKey
  [LawfulBEq α]
  {l : List ((a : α) × β a)}
  : ∀a, a ∈ (ofList l) <-> l.containsKey a := by
    intro a
    simp only [ofList, insertList, mem_iff, containsKey]
    constructor
    · intro h
      simp [reverse, <- List.containsKey_reverse_eq, List.containsKey_insertList_disj_of_containsKey] at h
      rcases h with h | h
      · simp [emptyCollection_def] at h
      · assumption
    · intro h
      simp_all [reverse, <- List.containsKey_reverse_eq, List.containsKey_insertList_disj_of_containsKey]

theorem ofList_getValueCast_eq_getValueCast
  [LawfulBEq α]
  {l : List ((a : α) × β a)}
  (hd : l.DistinctKeys)
  : ∀a h, (ofList l).getValueCast a h = l.getValueCast a (by simp_all [mem_iff, <- ofList_mem_iff_containsKey]) := by
    intro a h
    simp only [ofList, getValueCast, insertList, reverse]
    apply Std.Internal.List.getValueCast_of_perm 
    · apply List.DistinctKeys.reverse
      apply List.DistinctKeys.insertList 
      simp [emptyCollection_def]
    · apply List.Perm.trans (l₂ := (List.insertList (toList ∅) l)) (List.reverse_perm _) _
      apply Std.Internal.List.perm_insertList 
      · simp [emptyCollection_def]
      · simp [List.DistinctKeys.def] at hd
        grind
      · simp [emptyCollection_def]

theorem union_left_empty_equiv_self
  [EquivBEq α]
  {m' : DMap α β}
  : (∅ ∪ m').Equiv m' := by
    simp [union_def,  Equiv]
    apply List.perm_insertList
    · simp [emptyCollection_def]
    · grind [m'.distinct, keys_eq_map]
    · simp [emptyCollection_def]

theorem union_right_empty_equiv_self
  [EquivBEq α]
  {m : DMap α β}
  : (m ∪ ∅).Equiv m := by
    simp [union_def,  Equiv, insertList, emptyCollection_def, List.insertList]

theorem getValueCast_union_of_mem_right
  [LawfulBEq α]
  {m m' : DMap α β}
  (mem : k ∈ m')
  {h}
  : (m ∪ m').getValueCast k h = m'.getValueCast k mem := by
    simp [getValueCast, union_def, insertList]
    apply List.getValueCast_insertList_of_contains_right
    <;> grind [DMap]

theorem getValueCast_union_of_mem_eq_false_left
  [LawfulBEq α]
  {m m' : DMap α β}
  (mem : k ∈ m ∪ m')
  (notmem : ¬ k ∈ m)
  : DMap.getValueCast k (m ∪ m') mem = m'.getValueCast k (by grind [mem_union_disj_of_mem]) := by
    simp [getValueCast, union_def, insertList]
    apply List.getValueCast_insertList_of_contains_eq_false_left
    · grind [DMap]
    · grind [DMap]
    · simp [mem_iff, containsKey] at notmem
      assumption

omit [BEq α] in
instance {m m' : DMap α β} [DecidableEq α] [∀a, DecidableEq (β a)] : Decidable (Equiv m m') := by
  apply List.decidablePerm

instance {m : DMap α β} : Decidable m.isEmpty := by
  simp [isEmpty]
  infer_instance

instance {k : α} {m : DMap α β} : Decidable (k ∈ m) := by
  simp [mem_iff]
  infer_instance

omit [BEq α] in
instance [DecidableEq α] [∀a, DecidableEq (β a)] : DecidableEq (DMap α β) := by
  unfold DecidableEq
  rintro ⟨l, h⟩ ⟨l', h'⟩
  simp only [mk.injEq]
  infer_instance

end DMap

namespace DMap.Const

variable {α : Type u} [BEq α] {β : Type v}

theorem toList_Nodup
  [LawfulBEq α]
  {m : DMap α (fun (_ : α) => β)}
  : (DMap.Const.toList m).Nodup := by
    simp [toList, List.nodup_iff_pairwise_ne, List.pairwise_map]
    apply List.Pairwise.imp _ DMap.toList_Nodup
    grind

theorem forall_mem_iff_forall_mem_getValueCast
  [LawfulBEq α]
  {ρ : α -> β -> Prop}
  {m : DMap α (fun (_ : α) => β)}
  : (∀x ∈ DMap.Const.toList m, ρ x.fst x.snd) <-> ∀a, (h : a ∈ m) -> ρ a (m.getValueCast a h) := by
    simp [<- DMap.forall_mem_iff_forall_mem_getValueCast, toList]

theorem ofList_eq_DMap_ofList_map
  [PartialEquivBEq α]
  {l : List (α × β)}
  : ofList l = DMap.ofList (List.map List.Prod.toSigma l) := by
    simp [ofList, insertList, DMap.ofList, DMap.insertList, List.insertListConst]

theorem ofList_toList_eq_id
  [PartialEquivBEq α]
  {l : List (α × β)}
  (hd : l.Pairwise fun a b => (a.fst == b.fst) = false)
  : toList (ofList l) = l := by
    simp [ofList_eq_DMap_ofList_map, toList]
    rw [DMap.ofList_toList_eq_id]
    · simp only [List.map_map]
      delta List.Prod.toSigma Function.comp
      simp
    · simpa [List.DistinctKeys.def, List.pairwise_map, List.Prod.toSigma]

theorem ofList_mem_iff_containsKey
  [LawfulBEq α]
  {l : List (α × β)}
  : ∀a, a ∈ (ofList l) <-> (l.map List.Prod.toSigma).containsKey a := by
    intro a
    rw [<- DMap.ofList_mem_iff_containsKey]
    simp [ofList, insertList, DMap.ofList, reverse, emptyCollection_def, List.insertListConst, mem_iff, containsKey, <- List.containsKey_reverse_eq, DMap.insertList]

theorem ofList_getValueCast_eq_getValueCast
  [LawfulBEq α]
  {l : List (α × β)}
  (hd : l.Pairwise fun a b => (a.fst == b.fst) = false)
  : ∀a h, (ofList l).getValueCast a h = (l.map List.Prod.toSigma).getValueCast a (by grind [ofList_mem_iff_containsKey]) := by
    intro a h
    rw [<- DMap.ofList_getValueCast_eq_getValueCast]
    · simp [ofList_eq_DMap_ofList_map]
    · simp [List.DistinctKeys.def, List.pairwise_map, List.Prod.toSigma]
      grind
    · grind [DMap.ofList_mem_iff_containsKey, ofList_mem_iff_containsKey]

end DMap.Const

namespace DMap.Unit

variable [BEq α]

theorem toList_eq_keys
  {m : DMap α (fun (_ : α) => Unit)}
  : m.keys = toList m := by
    simp [toList, Const.toList, keys, List.keys_eq_map]


theorem toList_Nodup
  [LawfulBEq α]
  {m : DMap α (fun (_ : α) => Unit)}
  : (toList m).Nodup := by
    simp [<- toList_eq_keys, keys_Nodup]

theorem ofList_eq_DMap_ofList_map
  [PartialEquivBEq α]
  {l : List α}
  : ofList l = DMap.ofList (List.map (fun a => ⟨a, .unit⟩) l) := by
    simp [ofList, Const.ofList, Const.insertList, DMap.ofList, reverse, emptyCollection_def, List.insertListConst, insertList]
    unfold List.Prod.toSigma Function.comp
    simp

theorem ofList_toList_eq_id
  [PartialEquivBEq α]
  {l : List α}
  (hd : l.Pairwise fun a b => (a == b) = false)
  : toList (ofList l) = l := by
    simp [toList, ofList]
    rw [DMap.Const.ofList_toList_eq_id]
    · simp only [List.map_map]
      unfold Function.comp
      simp
    · simpa [List.pairwise_map]

theorem ofList_mem_iff_containsKey
  [LawfulBEq α]
  {l : List α}
  : ∀a, a ∈ (ofList l) <-> (l.map fun a => ⟨a, Unit.unit⟩).containsKey a := by
    intro a
    rw [<- DMap.ofList_mem_iff_containsKey]
    simp [ofList_eq_DMap_ofList_map]
