import Std
import Mystdlib.General
import Mystdlib.Univ.BasicUniv
import Mystdlib.Mems
import Mystdlib.Tactics

open Std

structure Schema (univ : Univ) where
  entities : HashSet String
  foreignKeys : HashSet String
  attributes : HashSet String
  foreignKeysDef : foreignKeys∋ -> entities∋ -> Option entities∋
  attributesDef : attributes∋ -> entities∋ -> Option univ.Code


structure Instance (schema : Schema univ) where
  generators : schema.entities∋ -> Nat
  foreignKeyMaps : (key : schema.foreignKeys∋) -> (σ : schema.entities∋) -> (h : (schema.foreignKeysDef key σ).isSome) -> Fin (generators σ) -> Option (Fin (generators ((schema.foreignKeysDef key σ).get h)))
  attributeMaps : (attr : schema.attributes∋) -> (σ : schema.entities∋) -> (h : (schema.attributesDef attr σ).isSome) -> Fin (generators σ) -> Option ((schema.attributesDef attr σ).get h).decode

def Instance.empty : Instance schema where
  generators := fun _ => 0
  foreignKeyMaps := nofun
  attributeMaps := nofun

def Instance.newGen (x : Instance schema) (σ : schema.entities∋) : Instance schema where
  generators := fun σ' => (x.generators σ') + (if σ = σ' then 1 else 0)
  foreignKeyMaps := fun k σ' h gen =>
    if h : gen.val < x.generators σ'
    then (x.foreignKeyMaps k σ' !p ⟨gen.val, by grind⟩).map (·.val<:)
    else Option.none
  attributeMaps := fun k σ' h gen =>
    if h : gen.val < x.generators σ'
    then x.attributeMaps k σ' !p gen.val<:
    else Option.none

def Instance.newGens (x : Instance schema) (σ : schema.entities∋) (n : Nat) : Instance schema :=
  match n with
  | .zero => x
  | .succ nn => recur (x.newGen σ) σ nn

def Instance.insertForeignKeyMap
  (x : Instance schema)
  (key : schema.foreignKeys∋)
  (σ : schema.entities∋)
  (h : (schema.foreignKeysDef key σ).isSome)
  (gen : Fin (x.generators σ))
  (v : Fin (x.generators ((schema.foreignKeysDef key σ).get h)))
  : Instance schema :=
  { x with foreignKeyMaps := fun key' σ' h gen' =>
    if h : key = key' ∧ σ = σ' ∧ gen.val = gen'.val
    then .some v.val<:
    else x.foreignKeyMaps key' σ' !p gen'}

def Instance.insertForeignKeyMapsAtGen
  (x : Instance schema)
  (σ : schema.entities∋)
  (gen : Fin (x.generators σ))
  (f : (key : schema.foreignKeys∋) -> (h : (schema.foreignKeysDef key σ).isSome) -> Option (Fin (x.generators ((schema.foreignKeysDef key σ).get h))))
  : Instance schema := 
  { x with foreignKeyMaps := fun k σ' h gen' =>
    if h' : σ = σ' ∧ gen.val = gen'.val ∧ (schema.foreignKeysDef k σ).isSome
    then match f k !p with
    | .some x => .some x.val<:
    | .none => x.foreignKeyMaps k σ' h gen'
    else x.foreignKeyMaps k σ' h gen'
    }

def Instance.insertAttributeMapAtGen
  (x : Instance schema)
  (attr : schema.attributes∋)
  (σ : schema.entities∋)
  (h : (schema.attributesDef attr σ).isSome)
  (gen : Fin (x.generators σ))
  (v : ((schema.attributesDef attr σ).get h).decode)
  : Instance schema := 
  { x with attributeMaps := fun attr' σ' h gen' =>
    if h : attr = attr' ∧ σ = σ' ∧ gen.val = gen'.val
    then .some (cast !p v)
    else x.attributeMaps attr' σ' !p gen' }


def Instance.insertAttributeMapsAtGen
  (x : Instance schema)
  (σ : schema.entities∋)
  (gen : Fin (x.generators σ))
  (f : (attr : schema.attributes∋) -> (h : (schema.attributesDef attr σ).isSome) -> Option ((schema.attributesDef attr σ).get h).decode)
  : Instance schema := 
  { x with attributeMaps := fun attr σ' h gen' =>
    if h' : σ = σ' ∧ gen.val = gen'.val ∧ (schema.attributesDef attr σ).isSome
    then match f attr !p with
    | .some x => .some (cast !p x)
    | .none => x.attributeMaps attr σ' h gen'
    else x.attributeMaps attr σ' h gen'
    }

@[grind, simp]
def myschema : Schema BasicUniv where
  entities := {"Department", "Employee"}
  foreignKeys := {"manager", "secretary", "worksIn"}
  attributes := {"age", "cummulative_age", "first", "last", "name"}
  foreignKeysDef := (fun ⟨k, is_key⟩ ⟨ent, is_ent⟩ =>
    if h : k = "manager" ∧ ent = "Employee" then .some "Employee"<:
    else if h : k = "secretary" ∧ ent = "Department" then .some "Employee"<:
    else if h : k = "worksIn" ∧ ent = "Employee" then .some "Department"<:
    else .none)
  attributesDef := fun ⟨attr, is_attr⟩ ⟨ent, is_ent⟩ =>
    if h : attr = "age" ∧ ent = "Employee" then .some nat#
    else if h : attr = "cummulative_age" ∧ ent = "Employee" then .some nat#
    else if h : attr = "first" ∧ ent = "Employee" then .some string#
    else if h : attr = "last" ∧ ent = "Employee" then .some string#
    else if h : attr = "name" ∧ ent = "Department" then .some string#
    else .none

def myinstance : Instance myschema :=
  Instance.empty
  |>.newGens "Department"<: 2
  |>.newGens "Employee"<: 3
  |>.insertAttributeMapsAtGen "Department"<: 0<: fun attr h =>
    if attr = "name" then .some (cast (by simp) "Math")
    else .none
