import Mystdlib.FinVec

def DFinVec (n : Nat) (β : Fin n -> Sort u) :=
  (i : Fin n) -> β i

namespace DFinVec

def foldl (v : DFinVec n β) (f : α -> (i : Fin n) -> β i -> α) (init : α) : α := match n with
| .zero => init
| .succ _ =>
  DFinVec.foldl (Fin.tail v) (fun a i βi => f a i.succ βi) (f init 0 (v 0))

abbrev myvecβ : Fin 3 -> Type
| 0 => Nat
| 1 => Bool
| 2 => Fin 10


def myvec : DFinVec 3 myvecβ
| 0 => nat_lit 7
| 1 => Bool.false
| 2 => Fin.mk 4 (by grind)


def myfold_fn  : Nat -> (i : Fin 3) -> myvecβ i -> Nat :=
  fun n i βi => match i with
  | 0 =>
    n + βi
  | 1 =>
    if βi then n.succ else n
  | 2 =>
    n + βi.val



