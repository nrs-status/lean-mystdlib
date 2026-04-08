
def elim_list_as_sum_aux
  {α : Type}
  (mot : α -> Type)
  (target : Type)
  (auxl : List α)
  : Type := match auxl with
  | .nil => target
  | .cons x xs =>
    mot x -> (elim_list_as_sum_aux (mot := mot) target xs)

def elim_list_as_sum
  {α : Type}
  [DecidableEq α]
  {mot : α -> Type}
  (l : List α)
  (a : α)
  (fin : Fin l.length)
  (h : a = l.get fin)
  : elim_list_as_sum_aux mot (mot a) l
  := match l with
  | .cons x xs => 
    let rec aux (p : mot a) (l' : List α) : elim_list_as_sum_aux (mot := mot) (mot a) l' :=
      match l' with
      | .nil => by simpa [elim_list_as_sum_aux]
      | .cons x xs => by simp [elim_list_as_sum_aux]; intro; exact aux p xs
    if h' : x = a 
    then by intro xmotx; rw [h'] at xmotx; exact aux xmotx _
    else by unhygienic
      intro xmotx; cases fin; simp_all; cases val <;> simp_all
      cases xs; exfalso; grind
      exact elim_list_as_sum _ _ (.mk n (by grind)) (by grind)

def elim_list_as_sum.nd
  {α : Type}
  [DecidableEq α]
  {mot : Type}
  (l : List α)
  (a : α)
  (fin : Fin l.length)
  (h : a = l.get fin)
  : elim_list_as_sum_aux (fun _ => mot) mot l
  := elim_list_as_sum _ a fin h

inductive ListSum {α : Type} : List α -> Type
| mk : (val : α) -> (i : Fin l.length) -> val = l.get i -> ListSum l

def ListSum.val {l : List α} : ListSum l -> α
| .mk val _ _ => val

def ListSum.elim
  {α : Type}
  [DecidableEq α]
  {mot : α -> Type}
  {l : List α}
  (ls : ListSum l)
  : elim_list_as_sum_aux (mot := mot) (mot ls.val) l
  := match ls with
  | .mk _ i p => elim_list_as_sum _ _ i p
  

def ListSum.elim_nd
  {α : Type}
  [DecidableEq α]
  {mot : Type}
  {l : List α}
  (ls : ListSum l)
  := match ls with
  | .mk val i p => elim_list_as_sum.nd (mot := mot) l val i p

