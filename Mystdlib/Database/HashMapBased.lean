import Std
import Mystdlib.General
import Mystdlib.Univ.BasicUniv
import Mystdlib.Mems
import Mystdlib.Tactics

open Std

structure Schema (univ : Univ) where
  entities : HashSet String
  foreignKeys : HashMap (String × entities∋) entities∋
  attributes : HashMap (String × entities∋) univ.Code


structure Instance (schema : Schema univ) where
  generators : schema.entities∋ -> Nat
  foreignKeyMaps : DHashMap { x : String × (σ : schema.entities∋) × Fin (generators σ) // (x.fst, x.snd.fst) ∈ schema.foreignKeys } fun σ' => Fin (generators (schema.foreignKeys.get (σ'.val.fst, σ'.val.snd.fst) σ'.property))
  attributeMaps : DHashMap { x : String × (σ : schema.entities∋) × Fin (generators σ) // (x.fst, x.snd.fst) ∈ schema.attributes } fun σ' => (schema.attributes.get (σ'.val.fst, σ'.val.snd.fst) σ'.property).decode

def Instance.empty : Instance schema where
  generators := fun _ => 0
  foreignKeyMaps := {}
  attributeMaps := {}

def Instance.newGen (x : Instance schema) (σ : schema.entities∋) : Instance schema where
  generators := fun σ' => (x.generators σ') + (if σ = σ' then 1 else 0)
  foreignKeyMaps := x.foreignKeyMaps.fold 
    (fun acc k v => 
      acc.insert 
        ⟨(k.val.fst, ⟨k.val.snd.fst, ⟨k.val.snd.snd, by grind⟩⟩), by grind⟩ 
        ⟨v.val, by grind⟩)
    {}
  attributeMaps := x.attributeMaps.fold 
    (fun acc k v =>
      acc.insert
        ⟨(k.val.fst, ⟨k.val.snd.fst, ⟨k.val.snd.snd, by grind⟩⟩), by grind⟩
        (by simp; exact v)) 
    {}

def Instance.newGens (x : Instance schema) (σ : schema.entities∋) (n : Nat) : Instance schema := match n with
| .zero => x
| .succ nn => recur (x.newGen σ) σ nn

def Instance.insertForeignKeyMap 
  (x : Instance schema)
  (k : { x : String × (σ : schema.entities∋) × Fin (x.generators σ) // (x.fst, x.snd.fst) ∈ schema.foreignKeys })
  (v : Fin (x.generators (schema.foreignKeys.get (k.val.fst, k.val.snd.fst) k.property))
 )
 : Instance schema :=
  { x with foreignKeyMaps := x.foreignKeyMaps.insert k v }

def Instance.insertForeignKeyMapsAtGen_aux
  (x : Instance schema)
  (σ : schema.entities∋)
  (gen : Fin (x.generators σ))
  (hm : DHashMap { x : String // (x, σ) ∈ schema.foreignKeys } (fun k => Fin (x.generators (schema.foreignKeys.get (k.val, σ) k.property))))
  : { y : Instance schema // y.generators = x.generators } :=
  hm.fold (fun acc k v => ⟨acc.val.insertForeignKeyMap ⟨⟨k.val, σ, cast !p gen⟩, !p⟩ (cast !p v), (by simp [insertForeignKeyMap]; grind)⟩) ⟨x, rfl⟩

def Instance.insertForeignKeyMapsAtGen
  (x : Instance schema)
  (σ : schema.entities∋)
  (gen : Fin (x.generators σ))
  (hm : DHashMap { x : String // (x, σ) ∈ schema.foreignKeys } (fun k => Fin (x.generators (schema.foreignKeys.get (k.val, σ) k.property))))
  : Instance schema :=
  x.insertForeignKeyMapsAtGen_aux σ gen hm


def Instance.insertAttributeMap
  (x : Instance schema)
  (k : { x : String × (σ : schema.entities∋) × Fin (x.generators σ) // (x.fst, x.snd.fst) ∈ schema.attributes })
  (v : (schema.attributes.get (k.val.fst, k.val.snd.fst) k.property).decode)
  : Instance schema :=
  { x with attributeMaps := x.attributeMaps.insert k v }


def Instance.insertAttributeMapsAtGen_aux
  (x : Instance schema)
  (σ : schema.entities∋)
  (gen : Fin (x.generators σ))
  (hm : DHashMap { x : String // (x, σ) ∈ schema.attributes } (fun k => (schema.attributes.get (k.val, σ) k.property).decode))
  : { y : Instance schema // y.generators = x.generators } :=
  hm.fold (fun acc k v => ⟨acc.val.insertAttributeMap ⟨⟨k.val, σ, cast !p gen⟩, !p⟩ (cast !p v), (by simp [insertAttributeMap]; grind)⟩) ⟨x, rfl⟩

def Instance.insertAttributeMapsAtGen
  (x : Instance schema)
  (σ : schema.entities∋)
  (gen : Fin (x.generators σ))
  (hm : DHashMap { x : String // (x, σ) ∈ schema.attributes } (fun k => (schema.attributes.get (k.val, σ) k.property).decode))
  : Instance schema :=
  x.insertAttributeMapsAtGen_aux σ gen hm

def Instance.insertAtGen_aux
  {schema : Schema univ}
  (x : Instance schema)
  (σ : schema.entities∋)
  (gen : (Fin (x.generators σ)))
  (hm : DHashMap { x : String // (x, σ) ∈ schema.foreignKeys ∨ (x, σ) ∈ schema.attributes } fun k => (if h : (k.val, σ) ∈ schema.foreignKeys then Fin (x.generators (schema.foreignKeys.get (k.val, σ) !p)) else (schema.attributes.get (k.val, σ) !p).decode))
  : { y : Instance schema // y.generators = x.generators } :=
  hm.fold (fun acc k v => 
    if h : (k.val, σ) ∈ schema.foreignKeys 
    then ⟨acc.val.insertForeignKeyMap ⟨⟨k.val, σ, cast !p gen⟩, !p⟩ (cast !p v), (by simp [insertForeignKeyMap]; grind)⟩ 
    else ⟨acc.val.insertAttributeMap ⟨⟨k.val, σ, cast !p gen⟩, !p⟩ (cast !p v), (by simp [insertAttributeMap]; grind)⟩) 
    ⟨x, rfl⟩


def Instance.insertAtGen
  {schema : Schema univ}
  (x : Instance schema)
  (σ : schema.entities∋)
  (gen : (Fin (x.generators σ)))
  (hm : DHashMap { x : String // (x, σ) ∈ schema.foreignKeys ∨ (x, σ) ∈ schema.attributes } fun k => (if h : (k.val, σ) ∈ schema.foreignKeys then Fin (x.generators (schema.foreignKeys.get (k.val, σ) !p)) else (schema.attributes.get (k.val, σ) !p).decode))
  : Instance schema :=
  x.insertAtGen_aux σ gen hm






