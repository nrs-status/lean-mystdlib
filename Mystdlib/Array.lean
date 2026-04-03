import Mystdlib.General


def Array.take' (n : Nat) (ar : Array α) (_ : n ≤ ar.size) : Array α :=
  ar.take n

def Array.drop' (n : Nat) (ar : Array α) (_ : n ≤ ar.size) : Array α :=
  ar.drop n

def Array.split (n : Nat) (ar : Array α) (h : n ≤ ar.size) : Array α × Array α := 
  (ar.take' n h, ar.drop' n h)

def Array.backN_aux (n : Nat) (ar : Array α) (h : n ≤ ar.size) (accum : Array α) : Array α :=
  match n with
  | .zero => accum
  | .succ nn =>
    let new_accum := accum.push (ar.back (by grind))
    ar.pop.backN_aux nn (by grind) new_accum

def Array.backNRev (ar : Array α) (n : Nat)  (h : n ≤ ar.size) : Array α :=
  ar.backN_aux n h #[]

def Array.backN (ar : Array α) (n : Nat)  (h : n ≤ ar.size) : Array α :=
  Array.reverse <| ar.backN_aux n h #[]

def Array.backN! (ar : Array α) (n : Nat) : Array α :=
  if h : n ≤ ar.size then ar.backN n h else ar

def Array.backWhile_impl (ar : Array α) (pred : α -> Bool) (accum : Array α) (h : 0 < ar.size) : Array α :=
  let xback := ar.back h
  if pred xback 
  then 
    if h' : 0 < ar.pop.size 
    then recur ar.pop pred (accum.push xback) h'
    else accum.push xback
  else accum

def Array.backWhile (ar : Array α) (pred : α -> Bool) (h : 0 < ar.size) : Array α :=
  ar.backWhile_impl pred #[] h

def Array.backWhileRev (ar : Array α) (pred : α -> Bool) (h : 0 < ar.size) : Array α :=
  Array.reverse <| ar.backWhile_impl pred #[] h

def Array.tuplize_impl (ar_rev : Array α) (n : Nat)  (h : n ≤ ar_rev.size := by grind) (p : n ≠ .zero := by grind) : (Array (Array α)) :=
  if h : n ≤ ar_rev.pop.size 
  then
    let taking := ar_rev.backNRev n (by grind)
    let recurring := Array.tuplize_impl ar_rev.pop n h p
    recurring.push taking
  else #[ar_rev.reverse]
termination_by ar_rev.size
decreasing_by grind

def Array.tuplize (ar : Array α) (n : Nat) (h : n ≤ ar.size := by grind) (p : n ≠ .zero := by grind) : Array (Array α) := Array.tuplize_impl ar.reverse n (by grind) (by grind) |>.reverse


def Array.and (ar : Array Bool) : Bool := ar.all id
def Array.or (ar : Array Bool) : Bool := ar.any id

