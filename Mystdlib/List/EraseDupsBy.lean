import Mathlib.Data.List.Chain
import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas

namespace List

structure eraseDupsByLoopTracer.Result (α) where
  x : List α
  y : List α

def eraseDupsByLoopTracer {α} (r : α → α → Bool) (x y : List α) : List (eraseDupsByLoopTracer.Result α) :=
  .cons (.mk x y) <| match x, y with
  | [], _ => .nil
  | a::as, bs => match bs.any (r a) with
    | .true => eraseDupsByLoopTracer r as bs
    | .false => eraseDupsByLoopTracer r as (a::bs)

namespace eraseDupsByLoopTracer

@[grind! .]
theorem not_isEmpty
  {r} {x y : List α}
  : ¬ (eraseDupsByLoopTracer r x y).isEmpty := by
    fun_induction eraseDupsByLoopTracer
    grind

theorem getLast
  {r} {x y : List α}
  : eraseDupsBy.loop r ((eraseDupsByLoopTracer r x y).getLast (by grind)).x ((eraseDupsByLoopTracer r x y).getLast (by grind)).y = eraseDupsBy.loop r x y := by
    fun_induction eraseDupsBy.loop <;> grind [eraseDupsByLoopTracer, eraseDupsBy.loop]

theorem getLast_x_isEmpty
  {r} {x y : List α}
  : ((eraseDupsByLoopTracer r x y).getLast (by grind)).x = [] := by
    fun_induction eraseDupsByLoopTracer
    grind [eraseDupsByLoopTracer]

theorem getLast_y_eq
  {r} {x y : List α}
  : ((eraseDupsByLoopTracer r x y).getLast (by grind)).y.reverse = eraseDupsBy.loop r x y := by
    fun_induction eraseDupsByLoopTracer
    grind [eraseDupsByLoopTracer, eraseDupsBy.loop]

theorem head
  {r} {x y : List α}
  : (eraseDupsByLoopTracer r x y).head (by grind) = ⟨x, y⟩ := by
    fun_induction eraseDupsByLoopTracer
    grind [eraseDupsByLoopTracer]

def IsChain_rel
  (r : α -> α -> Bool)
  : eraseDupsByLoopTracer.Result α -> eraseDupsByLoopTracer.Result α -> Prop :=
  fun ⟨x, y⟩ ⟨x', y'⟩ => match x, y with
  | [], _ => False
  | a::as, bs => match bs.any (r a) with
    | .true => x' = as ∧ y' = bs
    | .false => x' = as ∧ y' = a::bs

theorem IsChain
  {r} {x y : List α}
  : (eraseDupsByLoopTracer r x y).IsChain (IsChain_rel r) := by
    fun_induction eraseDupsByLoopTracer
    split <;> simp_all
    expose_names
    split <;> induction as <;> grind [eraseDupsByLoopTracer, IsChain_rel]
        
theorem results_IsChain
  {r : α -> α -> Bool}
  : ∀x y result, y.IsChain (!r · ·) -> result ∈ eraseDupsByLoopTracer r x y -> result.y.IsChain (!r · ·) := by
    intro x y result ischain iselm
    cases result; expose_names
    induction x
    · simp_all [eraseDupsByLoopTracer]
    · expose_names; simp_all
      simp_all [eraseDupsByLoopTracer]
      rcases iselm with h | h
      · simp_all
      · split at h <;> simp_all; expose_names
        have := List.IsChain.induction (r := IsChain_rel r) (h := IsChain) (l := eraseDupsByLoopTracer r tail (head :: y)) (fun result => result.y.IsChain (! r · ·)) <| by
          intro x y rel ischain'
          unfold IsChain_rel at rel
          split at rel
          split at rel
          split at rel
          · simp_all
          · split at rel
            · simp_all
            · expose_names
              simp_all
              apply List.IsChain.cons
              · assumption
              · grind
        have := this <| by
          intro notempty
          rw [eraseDupsByLoopTracer.head]
          simp
          induction y
          · simp
          · simp_all
        have := this ⟨x_1, y_1⟩ h 
        grind

theorem eraseDupsBy_IsChain
  : (eraseDupsBy r l).IsChain (fun x y => !r y x) := by
    rw [eraseDupsBy, <- getLast_y_eq, List.isChain_reverse]
    apply results_IsChain l [] <;> grind

theorem results_Pairwise
  {r : α -> α -> Bool}
  : ∀x y, y.Pairwise (!r · ·) -> ∀result ∈ eraseDupsByLoopTracer r x y, result.y.Pairwise (!r · ·) := by
    intro x y pairwise result iselm
    cases result
    induction x <;> simp_all [eraseDupsByLoopTracer]; expose_names
    rcases iselm with h | h
    · simp_all
    · split at h <;> simp_all; expose_names
      have := List.IsChain.induction (fun result => result.y.Pairwise (!r · ·)) (eraseDupsByLoopTracer r tail (head :: y)) IsChain 
      have := this <| by
        intro x y rel pairwise
        unfold IsChain_rel at rel
        split at rel
        split at rel
        split at rel
        · simp_all
        · split at rel
          · simp_all
          · simp_all
      have := this <| by
        intro notempty
        rw [eraseDupsByLoopTracer.head]
        simp_all
      grind


theorem eraseDupsBy_Pairwise
  {l : List α}
  : (eraseDupsBy r l).Pairwise (fun x y => !r y x) := by
    rw [eraseDupsBy, <- getLast_y_eq, List.pairwise_reverse]
    apply results_Pairwise l [] <;> grind

theorem eraseDups_Pairwise
  [BEq α]
  [PartialEquivBEq α]
  {l : List α}
  : (eraseDups l).Pairwise (! · == ·) := by
    rw [eraseDups]
    apply Pairwise.imp _ eraseDupsBy_Pairwise
    grind [BEq.symm_false]
    
theorem eraseDups_Nodup
  [BEq α]
  [LawfulBEq α]
  {l : List α}
  : (eraseDups l).Nodup := by
    rw [eraseDups, List.Nodup]
    apply Pairwise.imp _ eraseDups_Pairwise
    grind





