import Mystdlib.Univ.Basic

open Univ

class CodableGen (t : Type 1) (T : t) (types : List Type) (univ : Univ) (code : outParam Code)  where
  satisfies : univ.SatisfiedBy code
  eq : (h : t = Type) -> univ.decode code satisfies = h ▸ T

instance : CodableGen Type T [] ⟨.ofList [mkUnivEntry typ 0 T]⟩ (.mk typ 0 []) := sorry

instance 
  [CodableGen t T v ⟨.ofList as⟩ code]
  : CodableGen t T v ⟨.ofList (a :: as)⟩ code := sorry

instance 
  [CodableGen t T v ⟨.ofList (a :: as)⟩ code]
  : CodableGen t T v ⟨.ofList (a :: b :: as)⟩ code := sorry

class CodableGenAggregator (types : List Type) (univ : Univ) (len : outParam Nat) (codes : outParam (List Code)) where
  wf1 : types.length = codes.length
  wf2 : codes.length = len

instance 
  [CodableGen Type T [] univ code]
  : CodableGenAggregator [T] univ 1 [code] := sorry

instance
  [CodableGenAggregator types univ n codes]
  [CodableGen Type T [] univ code]
  : CodableGenAggregator (T :: types) univ (Nat.succ n) (code :: codes) := sorry

class IsUnivMem (t : Type 1) (α : t) (univ : Univ) (typ : outParam String)

instance [TypeFnGen arity t] : IsUnivMem t α ⟨.ofList [mkUnivEntry typ arity α]⟩ typ where

instance 
  [IsUnivMem t α ⟨.ofList es⟩ a] 
  : IsUnivMem t α ⟨.ofList (e :: es)⟩ a := sorry

instance 
  [IsUnivMem t α ⟨.ofList (e :: es)⟩ a]
  : IsUnivMem t α ⟨.ofList (e :: e' :: es)⟩ a  := sorry

instance
  [TypeFnGen arity t]
  [inst : CodableGenAggregator types univ arity codes]
  [IsUnivMem t F univ f]
  : CodableGen t F types univ (.mk f arity codes inst.wf2) := sorry

instance 
  [CodableGen (Type -> t) F (type :: types) univ code]
  : CodableGen t (F type) types univ code := sorry

instance 
  [CodableGen Type T [] univ code]
  : Codable T univ code := sorry


--these two are needed because anonymous functions mess up synthesis
instance
  [CodableGen (Type -> Type -> Type) (· -> ·) [α, β] univ code]
  : CodableGen (Type -> Type) (α -> ·) [β] univ code := sorry

instance
  {α β : Type}
  [CodableGen (Type -> Type) (α -> ·) [β] univ code]
  : CodableGen Type (α -> β) [] univ code := sorry

/-
abbrev BasicUniv : Univ where
  inner := .ofList [
      (mkUnivEntry "nat" 0 Nat),
      (mkUnivEntry "bool" 0 Bool),
      (mkUnivEntry "list" 1 List),
      (mkUnivEntry "prod" 2 Prod),
      (mkUnivEntry "arrow" 2 (· -> ·)),
      (mkUnivEntry "string" 0 String),
      ]
-/
