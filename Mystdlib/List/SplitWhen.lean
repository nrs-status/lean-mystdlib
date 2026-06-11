
namespace List

def splitWhen_aux (p : α -> Bool) (l : List α) (result's_next_head : List α) : List (List α) :=
  match l with
  | .nil => match result's_next_head with
    | .nil => []
    | .cons .. => [result's_next_head.reverse]
  | .cons x xs =>
    if p x
    then match result's_next_head with
      | .nil => splitWhen_aux p xs [x]
      | .cons .. => result's_next_head.reverse :: splitWhen_aux p xs [x]
    else splitWhen_aux p xs (result's_next_head.cons x)

def splitWhen (p : α -> Bool) (l : List α) :=
  splitWhen_aux p l []


def splitWhen_foldl_aux (p : α -> Bool) (l : List α) : List α × List (List α) :=
  l.foldl (fun (result's_next_head, result) next =>
    if p next
    then Prod.mk [next] <| match result's_next_head with
      | .nil => result
      | .cons .. => result's_next_head.reverse :: result
    else Prod.mk (next :: result's_next_head) result)
    ([], [])

def splitWhen_foldl (p : α -> Bool) (l : List α) : List (List α) :=
  (match splitWhen_foldl_aux p l with
  | (.nil, r) => r
  | (.cons x xs, r) => (List.cons x xs).reverse :: r).reverse

--#eval splitWhen_foldl (· % 2 = 0) [0, 1, 107, 101, 2, 3, 999, 3, 4, 7]
