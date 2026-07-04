import Mystdlib.Univ.Basic

open Univ

class GenCodable (t : Type 1) (T : t) (types : List Type) (univ : Univ) (code : outParam Code)  where
  satisfies : univ.SatisfiedBy code
  eq : (h : t = Type) -> univ.decode code satisfies = h ▸ T

instance : GenCodable Type T [] ⟨.ofList [mkUnivEntry typ 0 T]⟩ (.mk typ 0 []) := sorry

instance 
  [GenCodable t T v ⟨.ofList as⟩ code]
  : GenCodable t T v ⟨.ofList (a :: as)⟩ code := sorry

instance 
  [GenCodable t T v ⟨.ofList (a :: as)⟩ code]
  : GenCodable t T v ⟨.ofList (a :: b :: as)⟩ code := sorry

class GenCodableAggregator (types : List Type) (univ : Univ) (len : outParam Nat) (codes : outParam (List Code)) where
  wf1 : types.length = codes.length
  wf2 : codes.length = len

instance 
  [GenCodable Type T [] univ code]
  : GenCodableAggregator [T] univ 1 [code] := sorry

instance
  [GenCodableAggregator types univ n codes]
  [GenCodable Type T [] univ code]
  : GenCodableAggregator (T :: types) univ (Nat.succ n) (code :: codes) := sorry

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
  [inst : GenCodableAggregator types univ arity codes]
  [IsUnivMem t F univ f]
  : GenCodable t F types univ (.mk f arity codes inst.wf2) := sorry

instance 
  [GenCodable (Type -> t) F (type :: types) univ code]
  : GenCodable t (F type) types univ code := sorry


instance 
  [GenCodable Type T [] univ code]
  : Codable T univ code := sorry


--these two are needed because anonymous functions mess up synthesis
instance
  [GenCodable (Type -> Type -> Type) (· -> ·) [α, β] univ code]
  : GenCodable (Type -> Type) (α -> ·) [β] univ code := sorry

instance
  {α β : Type}
  [GenCodable (Type -> Type) (α -> ·) [β] univ code]
  : GenCodable Type (α -> β) [] univ code := sorry



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
