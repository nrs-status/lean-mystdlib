import Mystdlib.Univ.MetaUniv
import Mystdlib.Std.TreeMap
import Lean
import Std


open Lean

open Std

inductive SchemaIndexing
| finite (n : Nat) | infinite | unique
deriving BEq, Hashable, Ord

structure Schema (univ : Univ) where
  indexing : SchemaIndexing
  fields : TreeMap String univ.Code

structure Key (s : HashMap String (Schema univ)) where
  schema_ref : s∋
  i : match (s.get schema_ref.val schema_ref.property).indexing with
  | .finite n => Fin n
  | .infinite => Nat
  | .unique => Unit

variable {s : HashMap String (Schema univ)}

instance  {k : Key s} : BEq
    (match (s.get k.schema_ref.val k.schema_ref.property).indexing with
    | SchemaIndexing.finite n => Fin n
    | SchemaIndexing.infinite => ℕ
    | SchemaIndexing.unique => Unit) where
      beq := by
        split <;> exact (· == ·)

def Key_beq (k k' : Key s) : Bool :=
  if h : k.schema_ref == k'.schema_ref
  then 
    k.i == (cast !p k'.i)
  else .false

instance : BEq (Key s) where
  beq := Key_beq

instance {k : Key s} : Hashable
    (s∋ ×
      match (s.get k.schema_ref.val k.schema_ref.property).indexing with
      | SchemaIndexing.finite n => Fin n
      | SchemaIndexing.infinite => ℕ
      | SchemaIndexing.unique => Unit) := by
        split <;> infer_instance


instance : Hashable (Key s) where
  hash := fun k => 
  match (s.get k.schema_ref.val k.schema_ref.property).indexing with
  | .finite _ => 
    hash (Prod.mk k.schema_ref k.i)
  | .infinite =>
    hash (Prod.mk k.schema_ref k.i)
  | .unique => hash (Prod.mk k.schema_ref k.i)
  
def simple  (code : univ.Code) : Schema univ where
  indexing := .unique
  fields := {("field", code)}

def Branching (k : Key s) : Type :=
  (fieldnm : (s.get k.schema_ref.val k.schema_ref.property).fields∋) -> ((s.get k.schema_ref.val k.schema_ref.property).fields.get fieldnm !p).decode


