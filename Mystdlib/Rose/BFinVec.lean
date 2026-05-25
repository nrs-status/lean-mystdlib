
inductive Rose (β : α -> Nat)
| mk : (a : α) -> (Fin (β a) -> Rose β) -> Rose β
