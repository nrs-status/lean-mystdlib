import Mathlib.Data.Subtype
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mystdlib.Wellfounded
import Mystdlib.FinVec


inductive Rose (α : Type u)
| nil
| node (a : α) {n} (fv : Fin n -> Rose α)

namespace Rose

open FinVec

@[grind]
def ImmediateChild (x y : Rose α) : Prop :=
  match y with
  | .nil => False
  | .node _ fv => x ∈ fv

theorem ImmediateChild_wf : WellFounded (ImmediateChild (α := α)) := by
  constructor; intro a
  induction a
  · constructor; simp [ImmediateChild]
  · expose_names; constructor; intro x h
    simp [ImmediateChild, <- mem_iff_exists_idx] at h
    obtain ⟨fin, eq⟩ := h
    exact eq ▸ fv_ih fin

def Subrose (x y : Rose α) : Prop := Relation.ReflTransGen ImmediateChild x y

def node? : Rose α -> Option α
| .nil => .none
| .node a _ => a

instance : Membership (Rose α) (Rose α) where
  mem := Subrose

theorem mem_args_subrose
  : x ∈ args -> Subrose x (.node a args) := by
    simp [<- mem_iff_exists_idx]
    intro i eq
    exact .tail .refl ⟨_, eq⟩

def NodeHead (a : α) (r : Rose α) : Prop :=
  ∃r', r' ∈ r ∧ r'.node? = some a

theorem nodehead_of_node
  : NodeHead a (Rose.node a fv) := by
    simp [NodeHead]
    exists Rose.node a fv
    constructor
    simp [Membership.mem, Subrose]; grind
    simp [node?]

def size : Rose α -> Nat :=
  fun x => match h : x with
| .nil => 0
| .node a fv => 1 + FinVec.sum (FinVec.pmap (P := (ImmediateChild · (.node a fv))) (fun x y => size x) fv (by grind [ImmediateChild]))
termination_by x => ImmediateChild_wf.wrap x
decreasing_by simpa

@[simp, grind! .]
theorem zero_lt_size_node
  : 0 < size (.node a args) := by
    simp [size]

@[simp, grind .]
theorem zero_eq_size_nil
  : 0 = size (Rose.nil (α := α)) := by
    simp [size]

theorem size_decreasing
  {x y : Rose α}
  : x.ImmediateChild y -> x.size < y.size := by
    intro h
    rw (occs := [2]) [size.eq_def]
    split; grind; simp_all; expose_names
    simp [Finset.sum_eq_multiset_sum, pmap_eq_ofFn_pmap]
    suffices x.size ≤ (List.ofFn (size ∘ fv)).sum by grind
    apply List.le_sum_of_mem
    grind

unsafe def mapImpl (f : α -> β) (r : Rose α) : Rose β :=
  match r with
  | .nil => .nil
  | .node a fv => .node (f a) (FinVec.map (mapImpl f) fv)

@[implemented_by mapImpl]
def map (f : α -> β) : Rose α -> Rose β 
| .nil => .nil
| .node a fv => .node (f a) (FinVec.pmap (P := fun x => x.ImmediateChild (.node a fv)) (fun x _ => map f x) fv (by grind))
termination_by x => x.size
decreasing_by simp_all [size_decreasing]

end Rose

class RoseLike (α : Type u) where
  subterms : α -> Σn, Fin n -> α
  acc_wrt_immediate_children : ∀a, Acc (fun x y => x ∈ (subterms y).2) a

namespace RoseLike

variable [RoseLike α]

def ImmediateChild (x y : α) : Prop := x ∈ (RoseLike.subterms y).2

theorem ImmediateChild_wf : WellFounded (ImmediateChild (α := α)) :=
  ⟨RoseLike.acc_wrt_immediate_children⟩

def size : α -> Nat :=
  fun a => match h : RoseLike.subterms a with
  | ⟨0, _⟩ => 0
  | ⟨.succ nn, fv⟩ => 1 + FinVec.sum (FinVec.pmap (P := (ImmediateChild · a)) (fun x _ => size x) fv (by grind [ImmediateChild]))
termination_by x => ImmediateChild_wf.wrap x



