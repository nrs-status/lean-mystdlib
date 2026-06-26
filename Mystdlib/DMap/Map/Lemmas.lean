import Mystdlib.DMap.Lemmas
import Mystdlib.DMap.Map.Defs

open Std Internal

namespace Map

variable [BEq α]

theorem distinct
  (m : Map α β)
  : m.keys.Pairwise (fun (a b : α) => (a == b) = false)
  := by
    simp only [keys]
    apply m.inner.distinctKeys.distinct

theorem emptyCollection_def
  : (∅ : Map α β) = ⟨[], by simp⟩ := by
    simp [EmptyCollection.emptyCollection]

theorem union_def
  [PartialEquivBEq α]
  {m m' : Map α β}
  : (m ∪ m') = m.insertList m'.toList := by
    simp [Union.union, union, insertList, DMap.union, DMap.Const.insertList, DMap.insertList, toList, DMap.Const.toList, List.insertListConst]
    unfold List.Prod.toSigma
    have : (fun (p : α × β) => (⟨p.fst, p.snd⟩ : (_ : α) × β)) ∘ (fun (x : (_ : α) × β) => (x.fst, x.snd)) = id := by grind
    simp [this]
    
theorem mem_iff_mem_inner
  {m : Map α β}
  {k : α}
  : k ∈ m <-> k ∈ m.inner := by
    simp [Membership.mem, containsKey]

theorem keys_pairwise_not_beq
  {m : Map α β}
  : m.keys.Pairwise (fun a b => (a == b) = false) := by
    apply DMap.keys_pairwise_not_beq

theorem mem_union_disj_of_mem
  [PartialEquivBEq α]
  {m m' : Map α β}
  {k : α}
  : k ∈ m ∪ m' <-> k ∈ m ∨ k ∈ m' := by
    apply DMap.mem_union_disj_of_mem

theorem mem_union_of_left
  [PartialEquivBEq α]
  {m m' : Map α β}
  {k : α}
  (contains : k ∈ m)
  : k ∈ m ∪ m' := by
    apply DMap.mem_union_of_left
    assumption

theorem mem_union_of_right
  [PartialEquivBEq α]
  {m m' : Map α β}
  {k : α}
  (contains : k ∈ m')
  : k ∈ m ∪ m' := by
    apply DMap.mem_union_of_right
    assumption


theorem mem_of_equiv
  [PartialEquivBEq α]
  {m m' : Map α β}
  {k : α}
  (h : m.Equiv m')
  : k ∈ m <-> k ∈ m' := by
    rw [Equiv] at h
    apply DMap.mem_of_equiv
    assumption

theorem mem_iff_keys_contains
  [PartialEquivBEq α]
  {m : Map α β}
  {k : α}
  : k ∈ m <-> m.keys.contains k := by
    simp [mem_iff_mem_inner, DMap.mem_iff_keys_contains, Map.keys]

theorem mem_keys_iff_mem
  [LawfulBEq α]
  {m : Map α β}
  {k : α}
  : k ∈ m.keys <-> k ∈ m := by
    rw [keys, mem_iff_mem_inner]
    apply DMap.mem_keys_iff_mem

theorem insertList_congr_aux
  [EquivBEq α]
  {m m' : Map α β}
  {l l' : List ((_ : α) × β)}
  (h₁ : m.Equiv m')
  (h₂ : l.Perm l')
  (hd : l.DistinctKeys)
  : (m.inner.insertList l).Equiv (m'.inner.insertList l') := by
    apply DMap.insertList_congr
    <;> simp_all [Equiv]

theorem insertList_congr
  [EquivBEq α]
  {m m' : Map α β}
  {l l' : List (α × β)}
  (h₁ : m.Equiv m')
  (h₂ : l.Perm l')
  (hd : (l.map List.Prod.toSigma).DistinctKeys)
  : (m.insertList l).Equiv (m'.insertList l') := by
    rw [Equiv]
    apply insertList_congr_aux
    <;> grind [List.Perm.map]

theorem union_congr
  [EquivBEq α]
  {m1 m2 m3 m4 : Map α β}
  {h₁ : m1.Equiv m3}
  {h₂ : m2.Equiv m4}
  : (m1 ∪ m2).Equiv (m3 ∪ m4) := by
    apply DMap.union_congr
    <;> simp_all [Equiv]

theorem keys_eq_map
  {m : Map α β}
  : m.keys = m.toList.map Prod.fst := by
    simp [keys, toList, DMap.Const.toList]
    apply DMap.keys_eq_map


theorem mem_iff_isSome_getValueCast?
  [LawfulBEq α]
  {m : Map α β}
  {k : α}
  : k ∈ m <-> (m.getValueCast? k).isSome := by
    apply DMap.mem_iff_isSome_getValueCast?

theorem getValueCast?_eq_some_getValueCast
  [LawfulBEq α]
  {m : Map α β}
  {k : α}
  (h : k ∈ m)
  : m.getValueCast? k = Option.some (m.getValueCast k h) := by
    apply DMap.getValueCast?_eq_some_getValueCast

theorem toList_Nodup
  [LawfulBEq α]
  {m : Map α β}
  : m.toList.Nodup := by
    apply DMap.Const.toList_Nodup

theorem keys_Nodup
  [LawfulBEq α]
  {m : Map α β}
  : m.keys.Nodup := by
    apply DMap.keys_Nodup

theorem empty_isEmpty
  : (∅ : Map α β).isEmpty := by
    apply DMap.empty_isEmpty

theorem isEmpty_iff_forall_mem
  [ReflBEq α]
  {m : Map α β}
  : m.isEmpty <-> ∀a, ¬ a ∈ m := by
    apply DMap.isEmpty_iff_forall_mem

theorem mem_insertEntry_self
  [EquivBEq α]
  {m : Map α β}
  {k : α}
  {v : β}
  : k ∈ m.insertEntry k v := by
    apply DMap.mem_insertEntry_self

theorem mem_insertEntry
  [PartialEquivBEq α]
  {m : Map α β}
  {k a : α}
  {v : β}
  : a ∈ m.insertEntry k v <-> k == a ∨ a ∈ m := by
    apply DMap.mem_insertEntry

theorem mem_insertEntry_of_mem
  [PartialEquivBEq α]
  {m : Map α β}
  {k : α}
  (h : k ∈ m)
  : ∀k' v, k ∈ m.insertEntry k' v := by
    apply DMap.mem_insertEntry_of_mem
    simp_all [mem_iff_mem_inner]

theorem forall_mem_iff_forall_mem_getValueCast
  [LawfulBEq α]
  {ρ : α -> β -> Prop}
  {m : Map α β}
  : (∀x ∈ m.toList, ρ x.fst x.snd) <-> ∀a, (h : a ∈ m) -> ρ a (m.getValueCast a h) := by
    apply DMap.Const.forall_mem_iff_forall_mem_getValueCast

theorem equiv_self
  {m : Map α β}
  : m.Equiv m := by
    apply DMap.equiv_self

theorem equiv_iff_getValueCast?_eq
  [LawfulBEq α]
  {m m' : Map α β}
  : m.Equiv m' <-> ∀a, m.getValueCast? a = m'.getValueCast? a := by
    apply DMap.equiv_iff_getValueCast?_eq

theorem getValueCast_eq_of_equiv
  [LawfulBEq α]
  {m m' : DMap α β}
  : m.Equiv m' -> ∀a h h', m.getValueCast a h = m'.getValueCast a h' := by
    apply DMap.getValueCast_eq_of_equiv

theorem ofList_toList_eq_id
  [PartialEquivBEq α]
  {l : List (α × β)}
  (h : l.Pairwise fun a b => (a.fst == b.fst) = false)
  : (ofList l).toList = l := by
    apply DMap.Const.ofList_toList_eq_id
    assumption

theorem ofList_mem_iff_mem_inner
  [LawfulBEq α]
  {l : List (α × β)}
  : ∀a, a ∈ (ofList l) <-> (l.map List.Prod.toSigma).containsKey a := by
    apply DMap.Const.ofList_mem_iff_toList_containsKey

theorem ofList_getValueCast_eq_getValueCast
  [LawfulBEq α]
  {l : List (α × β)}
  (hd : l.Pairwise fun a b => (a.fst == b.fst) = false)
  : ∀a h, (ofList l).getValueCast a h = (l.map List.Prod.toSigma).getValueCast a (by grind [ofList_mem_iff_mem_inner]) := by
    apply DMap.Const.ofList_getValueCast_eq_getValueCast
    assumption

theorem union_left_empty_equiv_self
  [EquivBEq α]
  {m' : Map α β}
  : (∅ ∪ m').Equiv m' := by
    apply DMap.union_left_empty_equiv_self

theorem union_right_empty_equiv_self
  [EquivBEq α]
  {m : Map α β}
  : (m ∪ ∅).Equiv m := by
    apply DMap.union_right_empty_equiv_self

theorem getValueCast_union_of_mem_right
  [LawfulBEq α]
  {m m' : Map α β}
  (mem : k ∈ m')
  {h}
  : (m ∪ m').getValueCast k h = m'.getValueCast k mem := by
    apply DMap.getValueCast_union_of_mem_right

theorem getValueCast_union_of_mem_eq_false_left
  [LawfulBEq α]
  {m m' : Map α β}
  (mem : k ∈ m ∪ m')
  (notmem : ¬ k ∈ m)
  : Map.getValueCast k (m ∪ m') mem = m'.getValueCast k (by grind [mem_union_disj_of_mem]) := by
    apply DMap.getValueCast_union_of_mem_eq_false_left
    simpa


theorem mem_map
  {γ : Type w}
  {f : α -> β -> γ}
  {m : Map α β}
  {k : α}
  : k ∈ m <-> k ∈ m.map f := by
    simp [mem_iff_mem_inner, map]
    apply DMap.mem_map


theorem containsKey_modifyKey
  [LawfulBEq α]
  {k k' : α}
  {f : β -> β}
  {m : Map α β}
  : k' ∈ m.modifyKey k f <-> k' ∈ m := by
    apply DMap.containsKey_modifyKey
    
theorem beq_of_getEntry_eq
  [PartialEquivBEq α]
  {m : Map α β}
  {k h}
  : (m.getEntry k h).fst == k := by
    simp [getEntry, DMap.Const.getEntry, DMap.beq_of_getEntry_eq]

theorem getEntry?_eq_getValueCast?
  [LawfulBEq α]
  {m : Map α β}
  {k : α}
  : m.getEntry? k = Option.map (fun v => ⟨k, v⟩) (m.getValueCast? k) := by
    simp only [getEntry?, DMap.Const.getEntry?, getValueCast?, DMap.getEntry?_eq_getValueCast?, Option.map]
    grind

theorem getEntry?_eq_some_getEntry
  {m : Map α β}
  {k : α}
  {h}
  : m.getEntry? k = Option.some (m.getEntry k h) := by
    simp [getEntry, DMap.Const.getEntry, getEntry?, DMap.Const.getEntry?]
    have := DMap.getEntry?_eq_some_getEntry (m := m.inner) (k := k) (h := h)
    grind

theorem containsKey_eq_isSome_getEntry?
  {m : Map α β}
  {k : α}
  : k ∈ m <-> (m.getEntry? k).isSome := by
    simp [getEntry?, DMap.Const.getEntry?]
    apply DMap.containsKey_eq_isSome_getEntry?

theorem snd_eq_getValueCast_of_getEntry?_eq_some
  [LawfulBEq α]
  {m : Map α β}
  {k : α}
  (h : m.getEntry? k = some y)
  : y.snd = cast (have := beq_of_getEntry_eq (m := m) (k := k) (h := (by grind [containsKey_eq_isSome_getEntry?])); by grind [getEntry?_eq_some_getEntry]) (m.getValueCast k (by grind [containsKey_eq_isSome_getEntry?])) := by
    simp [getValueCast]
    have : k ∈ m.inner := by
      rw [<- mem_iff_mem_inner]
      grind [containsKey_eq_isSome_getEntry?]
    rw [getEntry?_eq_some_getEntry (h := by grind [mem_iff_mem_inner])] at h
    simp only [getEntry, DMap.Const.getEntry, Option.some.injEq] at h
    have := DMap.snd_eq_getValueCast_of_getEntry?_eq_some (k := k) (m := m.inner) (y := ⟨(m.inner.getEntry k this).fst, (m.inner.getEntry k this).snd⟩) (by grind [DMap.getEntry?_eq_some_getEntry])
    grind
    

theorem getValueCast_eq_getEntry_snd
  [LawfulBEq α]
  {m : Map α β}
  {k : α}
  {h}
  : (m.getEntry k h).snd = cast (by grind [beq_of_getEntry_eq]) (m.getValueCast k h) := by
    have := getEntry?_eq_some_getEntry (h := h)
    have := snd_eq_getValueCast_of_getEntry?_eq_some (m := m) (k := k) (y := m.getEntry k h) (by grind)
    grind

theorem getEntry_eq_key_getValueCast
  [LawfulBEq α]
  {m : Map α β}
  {k : α}
  {h}
  : m.getEntry k h = ⟨k, cast (by grind [beq_of_getEntry_eq]) (m.getValueCast k h)⟩ := by
    simp [getEntry, DMap.Const.getEntry, getValueCast]
    grind [DMap.getEntry_eq_key_getValueCast]


theorem getEntry_mem
  [LawfulBEq α]
  {m : DMap α β}
  {k : α}
  {h}
  : m.getEntry k h ∈ m.toList := by
    apply DMap.getEntry_mem

theorem mem_of_mem_toList
  [ReflBEq α]
  {m : DMap α β}
  {x : (a : α) × β a}
  : x ∈ m.toList -> x.fst ∈ m := by
    apply DMap.mem_of_mem_toList

theorem getEntry_of_mem
  [EquivBEq α]
  {m : DMap α β}
  {x : (a : α) × β a}
  {h : x ∈ m.toList}
  : m.getEntry x.fst (by grind [mem_of_mem_toList]) = x := by
    apply DMap.getEntry_of_mem
    assumption
      
instance {m : Map α β} : Decidable m.isEmpty := by
  simp [isEmpty]
  infer_instance

instance {k : α} {m : Map α β} : Decidable (k ∈ m) := by
  simp [mem_iff_mem_inner]
  infer_instance

instance {m m' : Map α β} [DecidableEq α] [DecidableEq β] : Decidable (Equiv m m') := by
  apply List.decidablePerm

omit [BEq α] in
instance [DecidableEq α] [DecidableEq β] : DecidableEq (Map α β) := by
  unfold DecidableEq
  rintro ⟨l, h⟩ ⟨l', h'⟩
  simp only [mk.injEq]
  infer_instance

instance entryDecidableBAll_key_getValueCast [LawfulBEq α] {p : α -> β -> Prop} [∀a, DecidablePred (p a)] : ∀m : Map α β, Decidable (∀a h, p a (m.getValueCast a h)) := by
  intro m
  have := DMap.entryDecidableBAll_key_getValueCast (p := p) (m := m.inner)
  simp_all only [mem_iff_mem_inner, getValueCast]
  infer_instance


instance entryDecidableBAll_getEntry [LawfulBEq α] {p : α -> β -> Prop} [∀a, DecidablePred (p a)] : ∀m : Map α β, Decidable (∀a h, p (m.getEntry a h).fst (m.getEntry a h).snd) := by
  intro m
  have := DMap.entryDecidableBAll_getEntry (p := p) (m := m.inner)
  simp_all only [mem_iff_mem_inner, getEntry, DMap.Const.getEntry]
  infer_instance

instance entryDecidableBAll_Prod_p [LawfulBEq α] {p : α × β -> Prop} [DecidablePred p] : ∀m : Map α β, Decidable (∀a h, p (m.getEntry a h)) := by
  intro m
  have := DMap.entryDecidableBAll_Sigma_p (m := m.inner) (p := fun x => p (x.fst, x.snd))
  simp_all only [mem_iff_mem_inner, getEntry, DMap.Const.getEntry]
  infer_instance

instance keyDecidableBAll [LawfulBEq α] {p : α -> Prop} [DecidablePred p] : ∀m : Map α β, Decidable (∀a ∈ m, p a) := by
  intro m
  simp [mem_iff_mem_inner]
  infer_instance



instance entryDecidableBEx_key_getValueCast [LawfulBEq α] {p : α -> β -> Prop} [∀a, DecidablePred (p a)] : ∀m : Map α β, Decidable (∃a h, p a (m.getValueCast a h)) := by
  intro m
  have := DMap.entryDecidableBEx_key_getValueCast (p := p) (m := m.inner)
  simp_all only [mem_iff_mem_inner, getValueCast]
  infer_instance

instance entryDecidableBEx_getEntry [LawfulBEq α] {p : α -> β -> Prop} [∀a, DecidablePred (p a)] : ∀m : Map α β, Decidable (∃a h, p (m.getEntry a h).fst (m.getEntry a h).snd) := by
  intro m
  if h : ∃a h, p a (m.getValueCast a h)
  then apply Decidable.isTrue; grind [getEntry_eq_key_getValueCast]
  else apply Decidable.isFalse; grind [getEntry_eq_key_getValueCast]

instance entryDecidableBEx_Prod_p [LawfulBEq α] {p : α × β -> Prop} [DecidablePred p] : ∀m : Map α β, Decidable (∃a h, p (m.getEntry a h)) := by
  intro m
  let ρ (a : α) (b : β) := p ⟨a, b⟩
  if h : ∃ a h, ρ (m.getEntry a h).fst (m.getEntry a h).snd
  then
    subst ρ
    apply Decidable.isTrue
    grind
  else
    subst ρ
    apply Decidable.isFalse
    grind

instance keyDecidableBEx [LawfulBEq α] {p : α -> Prop} [DecidablePred p] : ∀m : Map α β, Decidable (∃a ∈ m, p a) := by
  intro m
  simp [mem_iff_keys_contains]
  infer_instance






namespace Unit

theorem toList_eq_keys
  {m : Map α Unit}
  : m.keys = Map.Unit.toList m := by
    simp [toList, keys, DMap.Unit.toList_eq_keys]

