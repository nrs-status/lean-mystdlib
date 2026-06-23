import Std.Data.Internal.List.Defs
import Std.Data.Internal.List.Associative
import Mystdlib.List.Foldl

namespace Std
namespace Internal
namespace List

variable {α : Type u} {β : α → Type v} [BEq α] 

theorem containsKey_reverse_eq
  [PartialEquivBEq α]
  {l : List ((a : α) × β a)}
  : ∀a, List.containsKey a l = List.containsKey a l.reverse := by
    intro a
    simp only [List.containsKey_eq_keys_contains, Std.Internal.List.keys_eq_map ]
    grind


@[grind .]
theorem DistinctKeys.reverse
  [PartialEquivBEq α]
  {l : List ((a : α) × β a)}
  (h : List.DistinctKeys l)
  : List.DistinctKeys l.reverse := by
    rcases h with ⟨h⟩
    constructor
    rw [<- Std.Internal.List.reverse_keys, List.pairwise_reverse ]
    apply List.Pairwise.imp _ h
    apply BEq.symm_false

theorem DistinctKeys.reverse_iff
  [PartialEquivBEq α]
  {l : List ((a : α) × β a)}
  : List.DistinctKeys l <-> List.DistinctKeys l.reverse := by
    grind [List.reverse_reverse]


@[simp, grind =]
theorem containsKey_getElem_fst
  [LawfulBEq α]
  {l : List ((a : α) × β a)}
  : ∀i (h : i < l.length), containsKey l[i].fst l := by
    intro i lt
    rw [<- mem_keys_iff_contains, keys_eq_map]
    grind


instance {l : List ((a : α) × β a)} : Decidable (List.DistinctKeys l) := by
  suffices Decidable (List.Pairwise (fun a b => (a == b) = false) (List.map (fun x => x.fst) l)) by
    match this with
    | .isTrue p => 
      apply Decidable.isTrue
      constructor
      grind [Std.Internal.List.keys_eq_map ]
    | .isFalse p =>
      apply Decidable.isFalse
      intro k
      cases k
      grind [Std.Internal.List.keys_eq_map]
  infer_instance


attribute [grind .] Std.Internal.List.DistinctKeys.tail
attribute [grind .] Std.Internal.List.DistinctKeys.cons 
attribute [grind .] Std.Internal.List.containsKey_cons
attribute [grind .] Std.Internal.List.containsKey_nil
attribute [grind .] Std.Internal.List.DistinctKeys.distinct

attribute [grind .] PartialEquivBEq.symm
attribute [simp] PartialEquivBEq.symm
    


@[grind .]
theorem DistinctKeys.append
  [PartialEquivBEq α]
  {l l' : List ((a : α) × β a)}
  : List.DistinctKeys (l ++ l') -> List.DistinctKeys l ∧ List.DistinctKeys l' := by
    intro h
    induction l
    · simp_all
    · expose_names
      specialize tail_ih (by grind)
      simp_all only [List.cons_append, and_true]
      apply List.DistinctKeys.mk
      have := List.DistinctKeys.distinct h
      grind [keys, keys_eq_map]


open Std Internal

theorem insertList_eq_foldl
  [PartialEquivBEq α]
  {l toInsert : List ((a : α) × β a)}
  : l.insertList toInsert = toInsert.foldl (fun acc next => List.insertEntry next.fst next.snd acc) l := by
    fun_induction List.insertList
    <;> simp_all!

theorem insertList_scanl_getElem_containsKey
  [PartialEquivBEq α]
  {l toInsert : List ((a : α) × β a)}
  : ∀(i : Nat) (h : i + 1 < (List.scanl (fun acc next => insertEntry next.fst next.snd acc) l toInsert).length) k, List.containsKey k (getElem (toInsert.scanl (fun acc next => List.insertEntry next.fst next.snd acc) l) (i + 1) h) <-> k == (getElem toInsert i (by grind)).fst ∨ List.containsKey k (getElem (toInsert.scanl (fun acc next => List.insertEntry next.fst next.snd acc) l) i (by grind)) := by
    intro i h k
    rcases List.scanl_preservation
      (mot1 := fun b => List.containsKey k b)
      (mot2 := fun b (a : (a : α) × β a) => k == a.fst ∨ List.containsKey k b)
      (f := fun acc next => List.insertEntry next.fst next.snd acc)
      (init := l)
      (l := toInsert)
      (by grind [containsKey_insertEntry])
      with _
    grind

theorem insertList_scanl_containsKey_false
  [PartialEquivBEq α]
  {l : List ((a : α) × β a)}
  {hd : List.DistinctKeys l}
  {i : Nat}
  {h : i + 1 < (List.scanl (fun acc next => insertEntry next.fst next.snd acc) [] l).length}
  : List.containsKey (getElem l i (by grind)).fst (getElem (List.scanl (fun acc next => List.insertEntry next.fst next.snd acc) [] l) i (by grind)) = false := by
    apply List.scanl_idx_induction
      (motive := fun n (b : List ((a : α) × β a)) => (h : n < i + 1) -> b.containsKey (getElem l i (by grind)).fst = false)
    · grind
    · intro i lt h lt'
      apply Bool.of_not_eq_true
      rw [insertList_scanl_getElem_containsKey]
      simp only [not_or, Bool.not_eq_true]
      constructor
      · rw [DistinctKeys.def, List.pairwise_iff_getElem] at hd
        grind
      · grind
    · grind

theorem insertList_foldl_cons_hom
  [PartialEquivBEq α]
  {l : List ((a : α) × β a)}
  {hd : List.DistinctKeys l}
  : l.foldl (fun acc next => List.insertEntry next.fst next.snd acc) [] = l.foldl (fun xs y => y :: xs) [] := by
    apply List.foldl_fn_hom
    intro i
    induction i <;> expose_names
    · grind
    · if h' : n < l.length 
      then
        rw [<- List.getElem_scanl, <- List.getElem_scanl]
        · rw [List.getElem_succ_scanl, List.getElem_succ_scanl]
          grind [List.insertList_scanl_containsKey_false, List.insertEntry_of_containsKey_eq_false]
        · grind
        · grind
      else
        grind [List.take_of_length_le]

theorem insertListIfNewUnit_eq_foldl
  [PartialEquivBEq α]
  {l : List ((_ : α) × Unit)}
  {toInsert : List α}
  : l.insertListIfNewUnit toInsert = toInsert.foldl (fun acc next => acc.insertEntryIfNew next ()) l := by
    fun_induction List.insertListIfNewUnit
    <;> simp_all!

theorem insertListIfNewUnit_eq_insertListIfNew
  {l : List ((_ : α) × Unit)}
  {l' : List α}
  : l.insertListIfNewUnit l' = l.insertListIfNew (l'.map fun a => ⟨a, Unit.unit⟩) := by
    fun_induction List.insertListIfNewUnit
    <;> simp_all!

theorem replaceEntry_eq_self
  [LawfulBEq α]
  {l : List ((_ : α) × Unit)}
  : ∀k, l.replaceEntry k Unit.unit = l := by
    intro k
    fun_induction List.replaceEntry
    <;> simp_all

theorem insertListIfNew_eq_insertList
  [LawfulBEq α]
  {l l' : List ((_ : α) × Unit)}
  : l.insertListIfNew l' = l.insertList l' := by
    fun_induction List.insertListIfNew
    · simp!
    · simp_all only [List.insertList]
      congr
      simp only [List.insertEntryIfNew, List.insertEntry, cond]
      grind [replaceEntry_eq_self]
