import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Dedup
import Mystdlib.List
import Mystdlib.MachineModel.ProgramLayout

open MachineSpec AddressableMem ProgramLayout

variable {spec : MachineSpec} {mem : AddressableMem spec} {allocs : List (Slice mem)}


def lim_addresses {mem : AddressableMem spec} (allocations : List (Slice mem)) : List (spec.AddrPos) :=
  allocations.flatMap (fun x => [x.upperInclusiveLimit, x.lowerInclusiveLimit])

theorem
  lim_addresses_cons
  {allocs : List (Slice mem)}
  : lim_addresses (x :: allocs) = [x.upperInclusiveLimit, x.lowerInclusiveLimit] ++ lim_addresses allocs := by
    rw [lim_addresses, lim_addresses, List.flatMap_cons]

theorem lim_addresses_empty_iff_allocs_empty
  : (lim_addresses allocs).isEmpty <-> allocs.isEmpty := by
    simp [lim_addresses]
    constructor
    · intro h
      have := not_exists_of_forall_not h
      rw [<- List.isEmpty_eq_false_iff_exists_mem] at this
      grind
    · intro h x; grind

def maxAddressPos {mem : AddressableMem spec} (allocations : List (Slice mem)) (h : ¬ allocations.isEmpty) : spec.AddrPos :=
  (lim_addresses allocations).max <| by simp [lim_addresses]; rw [<- List.isEmpty_eq_false_iff_exists_mem]; grind

@[simp]
def maxAddressPos_is_max
  : x ∈ lim_addresses allocs -> x ≤ maxAddressPos allocs h := by
    intro ismem
    apply List.le_max_of_mem
    grind

@[simp]
theorem maxAddressPos_cons_mono
  {allocs : List (Slice mem)}
  {h : ¬ allocs.isEmpty}
  {xslice}
  : maxAddressPos allocs h ≤ maxAddressPos (allocs.cons xslice) (by grind) := by 
    simp only [maxAddressPos, lim_addresses_cons]
    grind

def minAddressPos {mem : AddressableMem spec} (allocations : List (Slice mem)) (h : ¬ allocations.isEmpty) : spec.AddrPos :=
  (lim_addresses allocations).min <| by simp [lim_addresses]; rw [<- List.isEmpty_eq_false_iff_exists_mem]; grind

@[simp]
theorem minAddressPos_is_min
  : x ∈ lim_addresses allocs -> minAddressPos allocs h ≤ x := by
    intro ismem
    apply List.min_le_of_mem
    grind


@[simp]
theorem minAddressPos_cons_mono
  {h : ¬ allocs.isEmpty}
  {xslice}
  : minAddressPos (allocs.cons xslice) (by grind) ≤ minAddressPos allocs h := by
    simp only [minAddressPos, lim_addresses_cons]
    grind


def sliceOfExtremes (allocations : List (Slice mem)) (h : ¬ allocations.isEmpty) : Slice mem where
  upperInclusiveLimit := maxAddressPos allocations h
  lowerInclusiveLimit := minAddressPos allocations h
  wf := by
    have : minAddressPos allocations h ∈ lim_addresses allocations := by
      simp [minAddressPos, List.min_mem]
    have := List.le_max_of_mem (l := lim_addresses allocations) this
    rwa [maxAddressPos]

theorem 
  minAddressPos_is_sliceOfExtremes_llim
  : minAddressPos allocs h = (sliceOfExtremes allocs h).lowerInclusiveLimit := by
    simp [minAddressPos, sliceOfExtremes]

theorem
  maxAddressPos_is_sliceOfExtremes_ulim
  : maxAddressPos allocs h = (sliceOfExtremes allocs h).upperInclusiveLimit := by
    simp [maxAddressPos, sliceOfExtremes]

theorem
  sliceOfExtremes_range_mem_within_extremes_1
  : x ∈ (sliceOfExtremes allocs h).range -> minAddressPos allocs h ≤ x ∧ x ≤ maxAddressPos allocs h := by
    intro h'
    simp [sliceOfExtremes, Slice.range] at h'
    rcases h' with ⟨a, aa, aaa⟩
    constructor
    · simp; grind
    · simp; grind

theorem
  sliceOfExtremes_range_mem_within_extremes_2
  : minAddressPos allocs h ≤ x ∧ x ≤ maxAddressPos allocs h -> x ∈ (sliceOfExtremes allocs h).range := by
    rintro ⟨a, b⟩
    simp [Slice.range]
    rw [<- maxAddressPos_is_sliceOfExtremes_ulim]
    rw [<- minAddressPos_is_sliceOfExtremes_llim]
    constructor
    · simp [List.finRange]; grind
    · simp_all

theorem
  sliceOfExtremes_range_mem_within_extremes
  : x ∈ (sliceOfExtremes allocs h).range <-> minAddressPos allocs h ≤ x ∧ x ≤ maxAddressPos allocs h := by
    constructor
    · apply sliceOfExtremes_range_mem_within_extremes_1
    · apply sliceOfExtremes_range_mem_within_extremes_2

theorem
  alloc_mem_subslice_sliceOfExtremes
  : (h : x ∈ allocs) -> x.Subslice (sliceOfExtremes allocs (by grind)) := by
    intro h
    constructor
    · simp [sliceOfExtremes, maxAddressPos]
      have : x.upperInclusiveLimit ∈ lim_addresses allocs := by
        simp [lim_addresses]; grind
      apply List.le_max_of_mem at this
      simp_all; grind
    · simp [sliceOfExtremes, minAddressPos]
      have : x.lowerInclusiveLimit ∈ lim_addresses allocs := by
        simp [lim_addresses]; grind
      apply List.min_le_of_mem at this
      simp_all; grind


theorem sliceOfExtremes_size_mono
  {allocs : List (Slice mem)}
  {h : ¬ allocs.isEmpty}
  {xslice}
  : (sliceOfExtremes allocs h).length ≤ (sliceOfExtremes (allocs.cons xslice) (by grind)).length := by
    simp [sliceOfExtremes, Slice.length]
    have thisa := @minAddressPos_cons_mono spec mem allocs h xslice
    have thisb := @maxAddressPos_cons_mono spec mem allocs h xslice
    simp_all; grind

theorem sliceOfExtremes_range_sublist_mono
  : (sliceOfExtremes allocs h).range.Sublist (sliceOfExtremes (x :: allocs) (by grind)).range := by
    have : (sliceOfExtremes allocs h).Subslice (sliceOfExtremes (x :: allocs) (by grind)) := by
      simp [sliceOfExtremes]
      constructor
      · have := maxAddressPos_cons_mono (h := h) (xslice := x)
        simp_all; grind
      · have := minAddressPos_cons_mono (h := h) (xslice := x)
        simp_all; grind
    grind [subslice_implies_range_sublist]

theorem sliceOfExtremes_subslice_mono
  : (sliceOfExtremes allocs h).Subslice (sliceOfExtremes (x :: allocs) (by grind)) := by
    constructor
    · simp_all [sliceOfExtremes]
      have := maxAddressPos_cons_mono (xslice := x) (allocs := allocs) (h := by grind)
      simp_all; grind
    · simp_all [sliceOfExtremes]
      have := minAddressPos_cons_mono (xslice := x) (allocs := allocs) (h := by grind)
      simp_all; grind
      

theorem sliceOfExtremes_range_min_mono
  {h : ¬ allocs.isEmpty }
  : (sliceOfExtremes (x :: allocs) (by grind)).range.min (by grind) ≤ (sliceOfExtremes allocs (by grind)).range.min (by grind) := by
    apply List.min_le_of_mem
    suffices (sliceOfExtremes allocs h).range.Sublist (sliceOfExtremes (x :: allocs) (by grind)).range by
      grind
    apply sliceOfExtremes_range_sublist_mono 



theorem sliceOfExtremes_range_min_cons
  {h : ¬ allocs.isEmpty}
  : (sliceOfExtremes (x :: allocs) (by grind)).range.min (by grind) = min (x.range.min (by grind)) ((sliceOfExtremes allocs (by grind)).range.min (by grind)) := by
    simp [sliceOfExtremes]
    rw [slice_range_min_is_llim, slice_range_min_is_llim, slice_range_min_is_llim]
    simp
    rw [minAddressPos]
    rw! [lim_addresses_cons]
    rw [List.min_append, minAddressPos]
    congr
    have := x.wf
    dsimp [List.min, min]
    split
    · exfalso; simp_all; grind
    · grind
    simp; grind [lim_addresses_empty_iff_allocs_empty]

theorem sliceOfExtremes_range_max_cons
  {h : ¬ allocs.isEmpty}
  : (sliceOfExtremes (x :: allocs) (by grind)).range.max (by grind) = max (x.range.max (by grind)) ((sliceOfExtremes allocs (by grind)).range.max (by grind)) := by
    simp [sliceOfExtremes]
    rw [slice_range_max_is_ulim, slice_range_max_is_ulim, slice_range_max_is_ulim]
    simp
    rw [maxAddressPos]
    rw! [lim_addresses_cons]
    rw [List.max_append, maxAddressPos]
    congr
    have := x.wf
    dsimp [List.max, max]
    split
    · exfalso; simp_all; grind
    · grind
    grind; grind [lim_addresses_empty_iff_allocs_empty]

def allocatedPositions 
  {mem : AddressableMem spec} 
  (allocations : List (Slice mem)) 
  : List (spec.AddrPos) 
  := allocations.flatMap Slice.range


@[grind! .]
theorem allocatedPositions_empty_iff_allocs_empty
  : (allocatedPositions allocs).isEmpty <-> allocs.isEmpty := by
    simp [allocatedPositions]
    constructor
    · intro h
      suffices allocs.isEmpty by grind
      suffices ¬ (allocs.isEmpty = false) by grind
      rw [List.isEmpty_eq_false_iff_exists_mem]
      simp
      intro x
      have := slice_range_not_empty (xslice := x)
      grind
    · intro h x e; grind

theorem allocatedPositions_of_allocs_in_sliceOfExtremes
  {h x}
  : x ∈ allocatedPositions allocs -> x ∈ (sliceOfExtremes allocs h).range := by
    intro ismem
    simp [allocatedPositions] at ismem
    rcases ismem with ⟨a, p, q⟩
    have := alloc_mem_subslice_sliceOfExtremes p
    rcases this with ⟨p', q'⟩
    rw [sliceOfExtremes_range_mem_within_extremes]
    constructor
    · rw [<- minAddressPos_is_sliceOfExtremes_llim] at q'
      suffices a.lowerInclusiveLimit ≤ x by simp_all; grind
      simp [Slice.range] at q; simp_all
    · rw [<- maxAddressPos_is_sliceOfExtremes_ulim] at p'
      suffices x ≤ a.upperInclusiveLimit by simp_all; grind
      simp [Slice.range] at q; simp_all


theorem allocatedPositions_sublist_mono
  : (allocatedPositions allocs).Sublist (allocatedPositions (x :: allocs)) := by
    simp [allocatedPositions]

theorem allocatedPositions_min_mono
  {h : ¬ allocs.isEmpty}
  : (allocatedPositions (x :: allocs)).min (by grind) ≤ (allocatedPositions allocs).min (by grind) := by
    apply List.min_le_of_mem
    grind [allocatedPositions_sublist_mono]

theorem allocatedPositions_min_is_sliceOfExtremes_range_llim
  {h : ¬ allocs.isEmpty}
  : (allocatedPositions allocs).min (by grind) = (sliceOfExtremes allocs (by grind)).lowerInclusiveLimit := by
    simp [allocatedPositions]
    induction allocs; grind; expose_names; simp_all
    induction tail
    · simp_all [sliceOfExtremes, minAddressPos, lim_addresses, Min.min]
      split; have := head.wf; simp_all; grind
      simp [slice_range_min_is_llim]
    · simp_all; expose_names
      rw [<- slice_range_min_is_llim, sliceOfExtremes_range_min_cons, List.min_append]
      suffices ((head_1.range ++ List.flatMap Slice.range tail).min (by grind)) = ((sliceOfExtremes (head_1 :: tail) (by grind)).range.min (by grind)) by
        grind
      specialize tail_ih
      rw [slice_range_min_is_llim]; grind; grind; simp_all
      grind; grind

theorem allocatedPositions_max_is_sliceOfExtremes_range_ulim
  {h : ¬ allocs.isEmpty}
  : (allocatedPositions allocs).max (by grind) = (sliceOfExtremes allocs (by grind)).upperInclusiveLimit := by
    simp [allocatedPositions]
    induction allocs; grind; expose_names; simp_all
    induction tail
    · simp_all [sliceOfExtremes, maxAddressPos, lim_addresses, Max.max]
      split; have := head.wf; simp_all; grind
      simp [slice_range_max_is_ulim]
    · simp_all; expose_names
      rw [<- slice_range_max_is_ulim, sliceOfExtremes_range_max_cons, List.max_append]
      suffices ((head_1.range ++ List.flatMap Slice.range tail).max (by grind)) = (sliceOfExtremes (head_1 :: tail) (by grind)).range.max (by grind) by
        grind
      specialize tail_ih
      rw [slice_range_max_is_ulim]; grind; grind; simp_all
      grind; grind


def isAllocatedPosition 
  {mem : AddressableMem spec}
  (xpos : spec.AddrPos)
  (allocations : List (Slice mem))
  : Prop := xpos ∈ (allocatedPositions allocations)

instance : Decidable (isAllocatedPosition xpos allocs) := by
  simp [isAllocatedPosition]; infer_instance

def gapPositions
  {mem : AddressableMem spec}
  (allocs : List (Slice mem))
  : List (spec.AddrPos)
  := if h : allocs.isEmpty then .nil else
    (sliceOfExtremes allocs h).range.filter (· ∉ allocatedPositions allocs)


theorem
  gapPositions_mem_notmem_allocatedPositions
  : x ∈ gapPositions allocs -> x ∉ allocatedPositions allocs := by
    intro h
    simp [gapPositions] at h; grind

theorem sliceOfExtremes_diff_allocatedPositions_is_gapPositions
  : (sliceOfExtremes allocs h).range.diff (allocatedPositions allocs) = gapPositions allocs := by
    have := List.Nodup.diff_eq_filter (l₁ := (sliceOfExtremes allocs h).range) (l₂ := allocatedPositions allocs) (by simp)
    rw [gapPositions]
    split; grind
    grind



theorem
  gapPositions_sub_sliceOfExtremes_range
  {h}
  : (gapPositions allocs).Sublist (sliceOfExtremes allocs h).range := by
    simp [gapPositions]
    split; grind
    apply List.filter_sublist

theorem
  gapPositions_len_lt_sliceOf_extremes_range_len
  {h}
  : (gapPositions allocs).length < (sliceOfExtremes allocs h).range.length := by
    rw [gapPositions]; split; grind
    simp
    exists (allocatedPositions allocs).min (by grind)
    constructor
    · apply allocatedPositions_of_allocs_in_sliceOfExtremes
      grind
    · grind


