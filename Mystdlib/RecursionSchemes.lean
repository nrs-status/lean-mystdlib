import Mystdlib

partial def collect {α β : Type}  (recur_info : α -> Array α) (collection_fn : α -> Option β) (a : α) : Array β :=
    runST fun σ => do
    let ref <- ST.mkRef (σ := σ) #[]
    let rec aux (a' : α) : ST σ Unit :=
      match collection_fn a' with
      | .some x => ref.modify (·.push x)
      | .none => discard <| recur_info a' |>.mapM aux
    aux a
    ref.get

partial def replace (recur_info : α -> Option (β × Array α)) (of_recur : β × Array α -> α) (replace_fn : α -> Option α) (a : α) : α :=
  match replace_fn a with
  | .some x => x
  | .none =>
    match recur_info a with
    | .some (xβ, recur_result) => of_recur (xβ, recur_result.map (replace recur_info of_recur replace_fn))
    | .none => a



