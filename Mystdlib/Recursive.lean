
class Recursive (α : Type) where
  ctor_aux : Type -- required for reconstruction after recursing
  recur_info : α -> Option (ctor_aux × Array α)
  of_recur : ctor_aux × Array α -> α

partial def Recursive.collect [Recursive α] (a : α) (collection_fn : α -> Option β) : Array β :=
  runST fun σ => do
    let ref <- ST.mkRef (σ := σ) #[]
    let rec aux (a' : α) : ST σ Unit :=
      match collection_fn a' with
      | .some x => ref.modify (·.push x)
      | .none => match recur_info a' with
        | .none => return
        | .some x => discard <| x.2 |>.mapM aux
    aux a
    ref.get

partial def Recursive.replace [Recursive α] (replace_fn : α -> Option α) (a : α) : α :=
  match replace_fn a with
  | .some x => x
  | .none =>
    match recur_info a with
    | .some (xβ, recur_result) => of_recur (xβ, recur_result.map (Recursive.replace replace_fn))
    | .none => a



