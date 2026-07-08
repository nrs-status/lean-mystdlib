
namespace List

theorem foldl_eq_scanl_getElem
  {f : β -> α -> β}
  {l : List α}
  {init : β}
  : l.foldl f init = (l.scanl f init)[l.length] := by
    rw [<- getLast_scanl]
    · rw [getLast_eq_getElem]
      simp
    · grind

theorem scanl_induction
  {motive : β -> Prop}
  {f : β -> α -> β}
  {l : List α}
  {init : β}
  {i : Nat}
  {h}
  (base : motive (getElem (l.scanl f init) i h))
  (ih : ∀i (h : i + 1 < (l.scanl f init).length), motive (l.scanl f init)[i] -> motive (l.scanl f init)[i + 1])
  : ∀j (h' : j < (l.scanl f init).length), i ≤ j -> motive (l.scanl f init)[j] := by
    intro i h
    induction i
    <;> grind

theorem scanl_induction_of_preservation
  {motive : β -> Prop}
  {f : β -> α -> β}
  {l : List α}
  {init : β}
  {i : Nat}
  {h}
  (base : motive (getElem (l.scanl f init) i h))
  (preservation : ∀b, motive b -> ∀a, motive (f b a))
  : ∀j (h' : j < (l.scanl f init).length), i ≤ j -> motive (l.scanl f init)[j] := by
    intro j lt leq
    apply scanl_induction
    · assumption
    · intro i' lt h''
      have := preservation _ h''
      rw [getElem_succ_scanl]
      apply this
    · assumption
  

theorem foldl_prefix_induction
  {motive : β -> Prop}
  {f : β -> α -> β}
  {l : List α}
  {init : β}
  {i : Nat}
  (base : motive ((l.take i).foldl f init))
  (ih : ∀j h, motive ((l.take j).foldl f init) -> motive (f ((l.take j).foldl f init) l[j]))
  : ∀j, i ≤ j -> motive ((l.take j).foldl f init) := by
    intro j leq
    if ltlen : j < l.length
    then
      have := scanl_induction (l := l) (f := f) (init := init) (i := i) (h := by grind) (motive := motive)
      simp only [getElem_scanl] at this
      apply this base
      · intro i' lt hmote
        rw [<- getElem_scanl]
        · grind [getElem_succ_scanl]
        · assumption
      · grind
      · assumption
    else
      if eq_i : i = j
      then grind
      else
        have lt_i : i < j := by grind
        if ileq_len : l.length ≤ i
        then grind [List.take_of_length_le]
        else
          rw [List.take_of_length_le (by grind), foldl_eq_scanl_getElem]
          apply scanl_induction (i := i)
          <;> grind [getElem_succ_scanl]

theorem foldl_prefix_induction_of_preservation
  {motive : β -> Prop}
  {f : β -> α -> β}
  {l : List α}
  {init : β}
  {i : Nat}
  (preservation : ∀b, motive b -> ∀a, motive (f b a))
  (base : motive ((l.take i).foldl f init))
  : ∀j, i ≤ j -> motive ((l.take j).foldl f init) := by
    apply foldl_prefix_induction
    · assumption
    · grind

theorem foldl_full_prefix_induction
  {motive : β -> Prop}
  {f : β -> α -> β}
  {l : List α}
  {init : β}
  {i : Nat}
  (base : motive ((l.take i).foldl f init))
  (ih : ∀j h, motive ((l.take j).foldl f init) -> motive (f ((l.take j).foldl f init) l[j]))
  : motive (l.foldl f init) := by
    rw [show l = l.take l.length by grind]
    if ltlen : i < l.length
    then
      apply foldl_prefix_induction (i := i) base
      · grind
      · grind
    else grind [List.take_of_length_le]

theorem foldl_full_prefix_induction_of_preservation
  {motive : β -> Prop}
  {f : β -> α -> β}
  {l : List α}
  {init : β}
  {i : Nat}
  (preservation : ∀b, motive b -> ∀a, motive (f b a))
  (base : motive ((l.take i).foldl f init))
  : motive (l.foldl f init) := by
    apply foldl_full_prefix_induction (i := i) base
    grind

theorem scanl_idx_induction
  {motive : Nat -> β -> Prop}
  {f : β -> α -> β}
  {l : List α}
  {init : β}
  (base : motive 0 init)
  (ih : ∀i (h : i + 1 < (l.scanl f init).length), motive i (l.scanl f init)[i] -> motive (i + 1) (l.scanl f init)[i + 1])
  : ∀i (h : i < (l.scanl f init).length), motive i (l.scanl f init)[i] := by
    intro i h
    induction i
    <;> grind

theorem foldl_prefix_idx_induction
  {motive : Nat -> β -> Prop}
  {f : β -> α -> β}
  {l : List α}
  {init : β}
  (base : motive 0 init)
  (ih : ∀i h, motive i ((l.take i).foldl f init) -> motive (i + 1) (f ((l.take i).foldl f init) l[i]))
  : ∀i, motive (l.take i).length ((l.take i).foldl f init) := by
    intro i
    rw [foldl_eq_scanl_getElem]
    apply scanl_idx_induction
    <;> grind [getElem_succ_scanl]


theorem scanl_fn_hom
  {f : β -> α -> β}
  {g : β -> α -> β}
  {l : List α}
  {init : β}
  (ih : ∀i (h : i + 1 < (l.scanl f init).length), (l.scanl f init)[i] = (getElem (l.scanl g init) i (by grind)) -> (l.scanl f init)[i + 1] = (getElem (l.scanl g init) (i + 1) (by grind)))
  : ∀i (h : i < (l.scanl f init).length), (l.scanl f init)[i] = (getElem (l.scanl g init) i (by grind)) := by
    intro i h
    grind [scanl_idx_induction
      (motive := fun (n : Nat) (b : β) => (h : n < (l.scanl f init).length) -> n ≤ i -> b = (getElem (l.scanl g init) n (by grind)))]

theorem foldl_fn_hom
  {f : β -> α -> β}
  {g : β -> α -> β}
  {l : List α}
  {init : β}
  (ih : ∀i, (l.take i).foldl f init = (l.take i).foldl g init)
  : l.foldl f init = l.foldl g init := by
    grind [foldl_eq_scanl_getElem, scanl_fn_hom]

theorem scanl_induction_of_ite_left
  {P : β -> α -> Prop}
  [∀b a, Decidable (P b a)]
  {f : β -> α -> β}
  {g : β -> α -> β}
  {l : List α}
  {init : β}
  (nontrivial_diff : ∀b a, ¬ P b a <-> f b a ≠ g b a)
  : (∀i (h : i < (l.scanl f init).length), 
    (getElem (l.scanl (fun acc next => if P acc next then f acc next else g acc next) init) i (by grind)) = (l.scanl f init)[i])
  -> ∀i (h : i + 1 < (l.scanl f init).length), P (l.scanl f init)[i] (getElem l i (by grind)) := by
    intro ih i lt
    have := ih (i + 1) (by grind)
    rw [getElem_succ_scanl, getElem_succ_scanl] at this
    grind

theorem scanl_induction_of_ite_right
  {P : β -> α -> Prop}
  [∀b a, Decidable (P b a)]
  {f : β -> α -> β}
  {g : β -> α -> β}
  {l : List α}
  {init : β}
  (nontrivial_diff : ∀b a, P b a -> f b a ≠ g b a)
  : (∀i (h : i < (l.scanl g init).length), 
    (getElem (l.scanl (fun acc next => if P acc next then f acc next else g acc next) init) i (by grind)) = (l.scanl g init)[i])
  -> ∀i (h : i + 1 < (l.scanl g init).length), ¬ P (l.scanl g init)[i] (getElem l i (by grind)) := by
    intro ih i lt
    have := ih (i + 1) (by grind)
    rw [getElem_succ_scanl, getElem_succ_scanl] at this
    grind

theorem scanl_on_ite_left
  {P : β -> α -> Prop}
  [∀b a, Decidable (P b a)]
  {f : β -> α -> β}
  {g : β -> α -> β}
  {l : List α}
  {init : β}
  (ih : ∀i (h : i + 1 < l.length), P (getElem (l.scanl f init) i (by grind)) l[i] -> P (getElem (l.scanl f init) (i + 1) (by grind)) l[i + 1])
  : ∀i (h : i < (l.scanl f init).length), 
    (hh : ¬ l.isEmpty) ->
    P init (getElem l 0 (by grind)) ->
    (getElem (l.scanl (fun acc next => if P acc next then f acc next else g acc next) init) i (by grind)) = (l.scanl f init)[i] := by
      intro i lt notempty base
      have all_P : ∀i (h : i < l.length), P (getElem (l.scanl f init) i (by grind)) l[i] := by
        grind [scanl_idx_induction (motive := fun i (b : β) => (h : i < l.length) -> P b l[i])]
      induction i
      · grind
      · rw [getElem_succ_scanl, getElem_succ_scanl]
        grind

theorem scanl_on_ite_right
  {P : β -> α -> Prop}
  [∀b a, Decidable (P b a)]
  {f : β -> α -> β}
  {g : β -> α -> β}
  {l : List α}
  {init : β}
  (ih : ∀i (h : i + 1 < l.length), ¬ P (getElem (l.scanl g init) i (by grind)) l[i] -> ¬ P (getElem (l.scanl g init) (i + 1) (by grind)) l[i + 1])
  : ∀i (h : i < (l.scanl g init).length), 
    (_ : ¬ l.isEmpty) ->
    ¬ P init (getElem l 0 (by grind)) ->
    (getElem (l.scanl (fun acc next => if P acc next then f acc next else g acc next) init) i (by grind)) = (l.scanl g init)[i] := by
      intro i lt notempty base
      have all_not_P : ∀i (h : i < l.length), ¬ P (getElem (scanl g init l) i (by grind)) l[i] := by
        grind [scanl_idx_induction (motive := fun i (b : β) => (h : i < l.length) -> ¬ P b l[i])]
      induction i
      · grind
      · rw [getElem_succ_scanl, getElem_succ_scanl]
        grind

theorem foldl_on_ite_left
  {P : β -> α -> Prop}
  [∀b a, Decidable (P b a)]
  {f : β -> α -> β}
  {g : β -> α -> β}
  {l : List α}
  {init : β}
  (ih : ∀i (h : i + 1 < l.length), P ((l.take i).foldl f init) l[i] -> P ((l.take (i + 1)).foldl f init) l[i + 1])
  : (_ : ¬ l.isEmpty) -> P init (getElem l 0 (by grind)) -> l.foldl (fun acc next => if P acc next then f acc next else g acc next) init = l.foldl f init := by
    intro notempty base
    simp only [foldl_eq_scanl_getElem]
    apply scanl_on_ite_left   
    <;> grind

theorem foldl_on_ite_right
  {P : β -> α -> Prop}
  [∀b a, Decidable (P b a)]
  {f : β -> α -> β}
  {g : β -> α -> β}
  {l : List α}
  {init : β}
  (ih : ∀i (h : i + 1 < l.length), ¬ P ((l.take i).foldl g init) l[i] -> ¬ P ((l.take (i + 1)).foldl g init) l[i + 1])
  : (_ : ¬ l.isEmpty) -> ¬ P init (getElem l 0 (by grind)) -> l.foldl (fun acc next => if P acc next then f acc next else g acc next) init = l.foldl g init := by
    intro notempty base
    simp only [foldl_eq_scanl_getElem]
    apply scanl_on_ite_right
    <;> grind

theorem scanl_preservation_of_apply
  {α : Type u}
  {β : Type v}
  {mot1 : β -> Prop}
  {mot2 : β -> α -> Prop}
  {f : β -> α -> β}
  (preservation : ∀b a, mot1 (f b a) -> mot2 b a)
  {l : List α}
  {init : β}
  : ∀i (h : i + 1 < (l.scanl f init).length), mot1 (l.scanl f init)[i + 1] -> mot2 (l.scanl f init)[i] (getElem l i (by grind)) := by
    grind [List.getElem_succ_scanl]

theorem scanl_apply_preservation
  {α : Type u}
  {β : Type v}
  {mot1 : β -> Prop}
  {mot2 : β -> α -> Prop}
  {f : β -> α -> β}
  (preservation : ∀b a, mot2 b a -> mot1 (f b a))
  {l : List α}
  {init : β}
  : ∀i (h : i + 1 < (l.scanl f init).length), mot2 (l.scanl f init)[i] (getElem l i (by grind)) -> mot1 (l.scanl f init)[i + 1] := by
    grind [List.getElem_succ_scanl]

theorem scanl_preservation
  {α : Type u}
  {β : Type v}
  {mot1 : β -> Prop}
  {mot2 : β -> α -> Prop}
  {f : β -> α -> β}
  (preservation : ∀b a, mot1 (f b a) <-> mot2 b a)
  {l : List α}
  {init : β}
  : ∀i (h : i + 1 < (l.scanl f init).length), mot1 (l.scanl f init)[i + 1] <-> mot2 (l.scanl f init)[i] (getElem l i (by grind)) := by
    grind [List.getElem_succ_scanl]

theorem foldl_preservation_of_apply
  {α : Type u}
  {β : Type v}
  {mot1 : β -> Prop}
  {mot2 : β -> α -> Prop}
  {f : β -> α -> β}
  (preservation : ∀b a, mot1 (f b a) -> mot2 b a)
  {l : List α}
  {init : β}
  : ∀i (h : i < l.length), mot1 (f ((l.take i).foldl f init) l[i]) -> mot2 ((l.take i).foldl f init) l[i] := by
    grind 

theorem foldl_apply_preservation
  {α : Type u}
  {β : Type v}
  {mot1 : β -> Prop}
  {mot2 : β -> α -> Prop}
  {f : β -> α -> β}
  (preservation : ∀b a, mot2 b a -> mot1 (f b a))
  {l : List α}
  {init : β}
  : ∀i (h : i < l.length), mot2 ((l.take i).foldl f init) l[i] -> mot1 (f ((l.take i).foldl f init) l[i]) := by
    grind 

theorem foldl_preservation
  {α : Type u}
  {β : Type v}
  {mot1 : β -> Prop}
  {mot2 : β -> α -> Prop}
  {f : β -> α -> β}
  (preservation : ∀b a, mot1 (f b a) <-> mot2 b a)
  {l : List α}
  {init : β}
  : ∀i (h : i < l.length), mot1 (f ((l.take i).foldl f init) l[i]) <-> mot2 ((l.take i).foldl f init) l[i] := by
    grind 
