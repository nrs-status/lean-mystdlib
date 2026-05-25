import Mystdlib.General
import Std

open Std

@[grind ->]
theorem ne_implies_gt_zero {ar : Array γ} : ¬ ar.isEmpty -> 0 < ar.size := by grind

macro_rules
| `(tactic|decreasing_trivial) => `(tactic|grind)

namespace UniTrie
structure Raw (α : Type u) [BEq α] [Hashable α] where
  sup : HashMap.Raw α (Raw α)
  deriving Inhabited

variable [BEq α] [Hashable α]


def Raw.empty : Raw α := .mk {}

def Raw.linearOfList (l : List α) : Raw α :=
  match l with
  | .nil => .empty
  | .cons a as => .mk <| {(a, recur as)}

def Raw.linearOfArray (ar : Array α) : Raw α :=
  if h : ar.isEmpty 
  then .empty
  else .mk <| {(ar.back (by grind), recur ar.pop)}
termination_by ar.size

instance : EmptyCollection (Raw α) := ⟨.empty⟩

def Raw.insert [EquivBEq α] (t : Raw α) (keys_nxt : α) (keys_rest : Array α) : Raw α :=
  if h : ¬ t.sup.contains keys_nxt
  then
    if keys_rest.isEmpty
    then .mk (t.sup.insert keys_nxt {})
    else .mk (t.sup.insert keys_nxt (.linearOfArray keys_rest))
  else
    if h : keys_rest.isEmpty
    then t
    else .mk <| t.sup.modify keys_nxt (fun t' => insert t' (keys_rest.back !p) keys_rest.pop)
termination_by keys_rest.size

namespace BiTrie

structure Raw (α : Type u) (β : Type v)   where
  sup : HashMap.Raw α (Option β × Raw α β)
  deriving Inhabited

def Raw.empty : Raw α β := .mk {}

variable [BEq α] [Hashable α]


def Raw.arrayLinear (keys_nxt : α) (keys_rest : Array α) (v : β) : Raw α β :=
  if h : keys_rest.isEmpty
  then .mk {(keys_nxt, (.some v, .empty))}
  else .mk {(keys_nxt, (.none, recur (keys_rest.back !p) keys_rest.pop v))}
termination_by keys_rest.size

def Raw.upsert [EquivBEq α] (t : Raw α β) (keys_nxt : α) (keys_rest : Array α) (f : Option β -> β) : Raw α β :=
  if h : ¬ t.sup.contains keys_nxt
  then .arrayLinear keys_nxt keys_rest (f .none)
  else if h' : keys_rest.isEmpty
  then .mk <| t.sup.modify keys_nxt (fun (v', t') => (f v', t'))
  else .mk <| t.sup.modify keys_nxt (fun (v', t') => (v', t'.upsert (keys_rest.back !p) keys_rest.pop f))
termination_by keys_rest.size

def Raw.insert [EquivBEq α] (t : Raw α β) (keys_nxt : α) (keys_rest : Array α) (v : β) : Raw α β :=
  t.upsert keys_nxt keys_rest (fun _ => v)

structure WF 
  (init_ρ : HashMap.Raw α (Option β × Raw α β) -> Prop)
  (sup_ρ : α -> HashMap.Raw α (Option β × Raw α β) -> Prop) 
  (t : Raw α β) : Prop where
    init_wf : init_ρ t.sup
    sup_wf : ∀k t', t.sup.get? k = .some t' -> sup_ρ k t'.snd.sup


end BiTrie


namespace DBiTrie

-- the first recursive occurence is the fixpoint proper, the second recursive occurence is the tail of the spine; the spine is the first three terms combined with the last one
inductive Raw (α : Type u) (β : α -> Type v)
| nil
| cons : (a : α) -> Option (β a) -> Raw α β -> Raw α β -> Raw α β

@[reducible]
def Raw.size : Raw α β -> Nat
| .nil => 0
| .cons _ _ subsup spine_tail => 1 + recur subsup + recur spine_tail

variable {α} in
theorem array_last_is_same {ar : Array α} : (h : 0 < ar.pop.size) -> (h' : 1 < ar.size) -> ar[0] = ar.pop[0] := by grind

def Raw.upsert [DecidableEq α] (t : Raw α β) (keys : Array α) (h : 0 < keys.size) (f : Option (β keys[0]) -> β keys[0]) : Raw α β := 
  match h' : t with
  | .nil => 
    if h'' : keys.pop.isEmpty
    then .cons keys[0] (f .none) .nil .nil
    else 
      have := array_last_is_same (ar := keys) (by grind) (by grind)
      .cons keys[0] .none (recur .nil keys.pop (by grind) (this ▸ f)) .nil
  | .cons a ba subsup spine_tail =>
    if h'' : a = keys.back h
    then if h''' : keys.pop.isEmpty
      then 
        have h'''' : a = keys[0] := by grind
        .cons a (.some (h'''' ▸ f (h'''' ▸ ba))) subsup spine_tail
      else 
        have := array_last_is_same (ar := keys) (by grind) (by grind)
        .cons a ba (recur subsup keys.pop (by grind) (this ▸ f)) spine_tail
    else 
      .cons a ba subsup (recur spine_tail keys !p f)
termination_by keys.size + t.size
  
def Raw.insert [DecidableEq α] (t : Raw α β) (keys : Array α) (h : 0 < keys.size) (v : β keys[0]) := t.upsert keys h (fun _ => v)
    
def Raw.find? [DecidableEq α] (t : Raw α β) (keys : Array α) (h : 0 < keys.size) : Option (β keys[0]) := match t with
| .nil => .none
| .cons a ba sup tail =>
  if h' : a = keys.back h
  then
    if h'' : keys.pop.isEmpty
    then
      have : a = keys[0] := by grind
      this ▸ ba
    else 
      have := array_last_is_same (ar := keys) (by grind) (by grind)
      this ▸ recur sup keys.pop _
  else recur tail keys _


def Raw.spine_size : Raw α β -> Nat
| .nil => 0
| .cons _ _ _ spine_tail => 1 + recur spine_tail

namespace WTrie

structure Cont (op : Type u) where
  arity : op -> Nat

-- educational
def Raw.spineToDHashMap : Raw α β -> DHashMap α (fun a => Option (β a) × Raw α β)
| .nil => {}
| .cons k v subsup spine_tail =>
  (recur spine_tail).insert k (v, subsup)

@[reducible]
def Cont.ρ_1 (xcont : Cont α) : Raw α β -> Prop
| .nil => True
| .cons k _ subsup spine_tail =>
  (subsup.spine_size = xcont.arity k) ∧ recur xcont subsup ∧ recur xcont spine_tail

structure Cont.ρ (xcont : Cont α) (xraw : Raw α β) : Prop where
  ρ_1 : xcont.ρ_1 xraw
  ρ_2 : xraw.spine_size = 1


end WTrie

structure WTrie (xcont : WTrie.Cont α) β where
  raw : Raw α β
  wf : xcont.ρ raw

namespace WTrie


def Cont.Nat : Cont (Fin 2) where
  arity := fun
  | 0 => 0
  | 1 => 1

@[reducible]
def Nat := WTrie Cont.Nat (fun _ => Unit)

def Nat.zero : WTrie.Nat where
  raw := .cons 0 (.some .unit) .nil .nil
  wf := .mk 
    (by simp [Cont.ρ_1]; rfl)
    rfl

def Nat.succ : WTrie.Nat -> Nat
| ⟨prev_raw, wf⟩ => {
    raw := (.cons 1 (.some .unit) prev_raw .nil)
    wf := .mk
      ⟨wf.2, wf.1, by dsimp [Cont.ρ_1]⟩
      (by simp [Raw.spine_size])
  }

def Nat.toNat : Nat -> _root_.Nat
| ⟨.cons k _ subsup _, ⟨ρ_1, _⟩⟩ => match k with
  | 0 => .zero
  | 1 => 1 + Nat.toNat ⟨subsup, ρ_1.2.1, ρ_1.1⟩

@[reducible]
def List (α : Type) := WTrie Cont.Nat (fun | 0 => Unit | 1 => α)

def List.nil (α : Type) : List α where
  raw := .cons 0 (.some .unit) .nil .nil
  wf := .mk
    (by simp [Cont.ρ_1]; rfl)
    rfl

def List.cons (a : α) (as : List α) : List α where
  raw := .cons 1 (.some a) as.raw .nil
  wf := .mk
    ⟨as.wf.2, as.wf.1, by dsimp [Cont.ρ_1]⟩
    (by simp [Raw.spine_size])


end WTrie


end DBiTrie

namespace TreeMapTrie

abbrev Raw α [Ord α] β := TreeMap (Array α) (Option β)

structure WF [Ord α] (xraw : Raw α β) : Prop where
  no_trivial_key : key ∈ xraw -> ¬ key.isEmpty
  well_pathed : key ∈ xraw -> 1 < key.size -> ∃key' ∈ xraw, ∃a : α, key = key'.push a

end TreeMapTrie

structure TreeMapTrie α [Ord α] [BEq α] β where
  raw : TreeMapTrie.Raw α β
  wf : TreeMapTrie.WF raw

instance [Ord α] [BEq α] : Membership (Array α) (TreeMapTrie α β) where
  mem := fun ⟨raw, _⟩ a => a ∈ raw

namespace ContinuTreeMapTrie 

structure Raw α [Ord α] [BEq α] β where
  inner : TreeMapTrie.Raw α β
  conts : Array (Array α)

/-
inductive WF {α : Type u} [Ord α] [BEq α] {β : Type v} : Raw α β -> Prop
| intro
  (inner : TreeMapTrie α β)
  (conts : Array (Array α))
  : (∀cont, cont ∈ conts -> cont ∉ inner) ->
    (∀cont, cont ∈ conts -> ∃k ∈ inner, ∃a : α, cont = k.push a) ->
    WF ⟨inner, conts⟩
-/

structure WF [Ord α] (xraw : Raw α β) : Prop where
  is_treemaptrie : TreeMapTrie.WF xraw.inner
  conts_wf_1 : ∀cont ∈ xraw.conts, cont ∉ xraw.inner
  conts_wf_2 : ∀cont ∈ xraw.conts, ∃key ∈ xraw.inner, ∃a : α, cont = key.push a


end ContinuTreeMapTrie

structure ContinuTreeMapTrie α [Ord α] [BEq α] β where
  raw : ContinuTreeMapTrie.Raw α β
  wf : ContinuTreeMapTrie.WF raw


/-
structure Raw α [Ord α] β  where
  val : TreeMap (Array α) (Option β)
  conts : Array (Array α)

variable [Ord α]

inductive WF : Raw α β -> Prop where
| nocont (val : TreeMap (Array α) (Option β)) : WF ⟨val, #[]⟩
| cont_is_extension
  (val : TreeMap (Array α) (Option β))
  (conts : Array (Array α))
  : (∀cont, cont ∈ conts -> cont ∉ val) ->
    (∀cont, cont ∈ conts -> (∃k ∈ val, ∃a : α, cont = k.push a)) -> 
    WF ⟨val, conts⟩

end TreeMapTrie

structure TreeMapTrie α [Ord α] β where
  raw : TreeMapTrie.Raw α β
  wf : TreeMapTrie.WF raw
-/
