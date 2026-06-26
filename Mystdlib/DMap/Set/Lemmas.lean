import Mystdlib.DMap.Map.Lemmas
import Mystdlib.DMap.Set.Defs

open Std Internal

namespace Map.Set

variable [BEq α]

theorem distinct
  {s : Set α}
  : s.toList.Pairwise (fun (a b : α) => (a == b) = false) := by
    simp only [toList, <- Map.Unit.toList_eq_keys]
    apply Map.distinct

theorem emptyCollection_def
  : (∅ : Set α) = ⟨[], by simp⟩ := by
    simp [EmptyCollection.emptyCollection]

theorem union_def
  [LawfulBEq α]
  {m m' : Set α}
  : (m ∪ m') = m.insertListIfNew m'.toList := by
    simp only [Union.union, insertListIfNew, union, Unit.insertListIfNew, Map.union, DMap.Unit.insertListIfNew, DMap.union, DMap.insertList, List.insertListIfNewUnit_eq_insertListIfNew, List.insertListIfNew_eq_insertList, toList, Unit.toList, DMap.Unit.toList, DMap.Const.toList, List.map_map, mk.injEq, Map.mk.injEq, DMap.mk.injEq]
    suffices (((fun a => (⟨a, ()⟩ : (_ : α) × Unit))) ∘ (fun x => x.fst) ∘ fun x => (x.fst, x.snd)) = id by
      rw [this]
      simp
    funext
    simp

theorem mem_iff
  {m : Set α}
  {k : α}
  : k ∈ m <-> k ∈ m.inner := by
    simp [Membership.mem, containsKey]

theorem mem_iff_mem_toList
  [LawfulBEq α]
  {m : Set α}
  {k : α}
  : k ∈ m <-> k ∈ m.toList := by
    simp [toList, Unit.toList, <- DMap.Unit.toList_eq_keys, DMap.mem_keys_iff_mem, mem_iff, Map.mem_iff_mem_inner]

theorem toList_pairwise_not_beq
  {s : Set α}
  : s.toList.Pairwise (fun a b => (a == b) = false) := by
    simp only [toList, ← Unit.toList_eq_keys]
    apply Map.keys_pairwise_not_beq

theorem mem_union_disj_of_mem
  [PartialEquivBEq α]
  {s s' : Set α}
  {k : α}
  : k ∈ s ∪ s' <-> k ∈ s ∨ k ∈ s' := by
    apply Map.mem_union_disj_of_mem


theorem mem_union_of_left
  [PartialEquivBEq α]
  {s s' : Set α}
  {k : α}
  (contains : k ∈ s)
  : k ∈ s ∪ s' := by
    apply Map.mem_union_of_left
    simp_all [mem_iff]

theorem mem_union_of_right
  [PartialEquivBEq α]
  {s s' : Set α}
  {k : α}
  (contains : k ∈ s')
  : k ∈ s ∪ s' := by
    apply Map.mem_union_of_right
    simp_all [mem_iff]

theorem mem_of_equiv
  [PartialEquivBEq α]
  {s s' : Set α}
  {k : α}
  (h : s.Equiv s')
  : k ∈ s <-> k ∈ s' := by
    apply Map.mem_of_equiv
    simp_all [Equiv]

theorem insertListIfNew_congr_aux
  [EquivBEq α]
  {s s' : Set α}
  {l l' : List ((_ : α) × Unit)}
  (h₁ : s.Equiv s')
  (h₂ : l.Perm l')
  (hd : l.DistinctKeys)
  : (s.inner.inner.insertList l).Equiv (s'.inner.inner.insertList l') := by
    apply DMap.insertList_congr
    <;> simp_all [Equiv, Map.Equiv]

theorem insertListIfNew_congr
  [EquivBEq α]
  {s s' : Set α}
  {l l' : List α}
  (h₁ : s.Equiv s')
  (h₂ : l.Perm l')
  (hd : l.Pairwise (fun (a b : α) => (a == b) = false))
  : (s.insertListIfNew l).Equiv (s'.insertListIfNew l') := by
    simp only [insertListIfNew, Equiv, Unit.insertListIfNew, Map.Equiv, DMap.Unit.insertListIfNew, DMap.Equiv, List.insertListIfNewUnit_eq_insertListIfNew]
    suffices (List.insertList (l.map fun a => ⟨a, ()⟩) s.inner.inner.toList).Perm (List.insertList (l'.map fun a => ⟨a, ()⟩) s'.inner.inner.toList) by
      have perm1 := List.insertListIfNew_perm_insertList 
        (l₁ := s.inner.inner.toList)
        (l₂ := l.map fun a => ⟨a, ()⟩)
        s.inner.inner.distinctKeys
        (by grind [List.DistinctKeys, List.keys_eq_map])
      have perm2 := List.insertListIfNew_perm_insertList
        (l₁ := s'.inner.inner.toList)
        (l₂ := l'.map fun a => ⟨a, ()⟩)
        s'.inner.inner.distinctKeys
        <| by
          constructor
          simp [List.keys_eq_map, List.pairwise_map]
          apply List.Pairwise.perm (l := l)
          <;> grind [BEq.symm_false]
      grind [List.Perm.congr_left perm1, List.Perm.congr_right perm2]
    apply List.insertList_congr
    · apply List.Perm.map
      assumption
    · simp_all [Equiv, Map.Equiv, DMap.Equiv]
    · constructor
      simp only [List.keys_eq_map, List.pairwise_map]
      assumption
    · exact s.inner.inner.distinctKeys
    · constructor
      simp only [List.keys_eq_map, List.pairwise_map]
      apply List.Pairwise.perm (l := l)
      <;> grind [BEq.symm_false]
      
theorem union_congr
  [EquivBEq α]
  {s1 s2 s3 s4 : Set α}
  {h₁ : s1.Equiv s3}
  {h₂ : s2.Equiv s4}
  : (s1 ∪ s2).Equiv (s3 ∪ s4) := by
    simp only [Union.union, union, Equiv]
    have : ∀β (m m' : Map α β), m.union m' = m ∪ m' := by simp [Union.union]
    rw [this, this]
    apply Map.union_congr
    <;> simp_all [Equiv]

theorem toList_Nodup
  [LawfulBEq α]
  {s : Set α}
  : s.toList.Nodup := by
    apply DMap.Unit.toList_Nodup

theorem empty_isEmpty
  : (∅ : Set α).isEmpty := by
    apply Map.empty_isEmpty

theorem isEmpty_iff_forall_mem
  [ReflBEq α]
  {m : Set α}
  : m.isEmpty <-> ∀a, ¬ a ∈ m := by
    apply Map.isEmpty_iff_forall_mem

theorem mem_insertEntry_self
  [EquivBEq α]
  {m : Set α}
  {k : α}
  : k ∈ m.insertEntry k := by
    apply Map.mem_insertEntry_self

theorem mem_insertEntry
  [PartialEquivBEq α]
  {s : Set α}
  {k a : α}
  : a ∈ s.insertEntry k <-> k == a ∨ a ∈ s := by
    apply Map.mem_insertEntry

theorem mem_insertEntry_of_mem
  [PartialEquivBEq α]
  {s : Set α}
  {k : α}
  (h : k ∈ s)
  : k ∈ s.insertEntry k' := by
    apply Map.mem_insertEntry_of_mem
    assumption

theorem equiv_self
  {s : Set α}
  : s.Equiv s := by
    apply Map.equiv_self

theorem ofList_toList_eq_id
  [PartialEquivBEq α]
  {l : List α}
  {hd : List.Pairwise (fun a b => (a == b) = false) l}
  : toList (ofList l) = l := by
    apply DMap.Unit.ofList_toList_eq_id
    assumption

theorem ofList_mem_iff_containsKey
  [LawfulBEq α]
  {l : List α}
  : ∀a, a ∈ (ofList l) <-> (l.map fun a => ⟨a, Unit.unit⟩).containsKey a := by
    apply DMap.Unit.ofList_mem_iff_toList_containsKey

theorem union_left_empty_equiv_self
  [EquivBEq α]
  {m' : Set α}
  : (∅ ∪ m').Equiv m' := by
    apply Map.union_left_empty_equiv_self

theorem union_right_empty_equiv_self
  [EquivBEq α]
  {m : Set α}
  : (m ∪ ∅).Equiv m := by
    apply Map.union_right_empty_equiv_self



instance {m : Set α} : Decidable m.isEmpty := by
  simp [isEmpty]
  infer_instance

instance {k : α} {s : Set α} : Decidable (k ∈ s) := by
  simp [mem_iff]
  infer_instance

instance {s s' : Set α} [DecidableEq α]  : Decidable (Equiv s s') := by
  apply List.decidablePerm

omit [BEq α] in
instance [DecidableEq α] : DecidableEq (Set α) := by
  unfold DecidableEq
  rintro ⟨l, h⟩ ⟨l', h'⟩
  simp only [mk.injEq]
  infer_instance

instance decidableBAll [LawfulBEq α] {p : α -> Prop} [DecidablePred p] : ∀s : Set α, Decidable (∀a ∈ s, p a) := by
  intro m
  simp [mem_iff_mem_toList, toList, Unit.toList, DMap.Unit.toList, DMap.Const.toList]
  infer_instance
