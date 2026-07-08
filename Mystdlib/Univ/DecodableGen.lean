import Mystdlib.Univ.Basic

open Univ

class Decodable (code : Code) (univ : Univ) (type : outParam Type) : Prop where
  satisfies : univ.SatisfiedBy code
  wf : univ.decode code satisfies = type

class DecodableGen
  (typ : String) (tail revAcc : List Code)  (univ : Univ) (t : outParam (Type 1)) (type : outParam t) where

instance 
  [DecodableGen typ tail [] ⟨.ofList es⟩ t α]
  : DecodableGen typ tail [] ⟨.ofList (e :: es)⟩ t α := sorry

instance 
  [DecodableGen typ tail [] ⟨.ofList (e :: es)⟩ t α]
  : DecodableGen typ tail [] ⟨.ofList (e :: e' :: es)⟩ t α := sorry

class IsUnivType (typ : String) (univ : Univ) (t : outParam (Type 1)) (type : outParam t) where

instance [TypeFnGen arity t] : IsUnivType type ⟨.ofList [mkUnivEntry type arity T]⟩ t T := sorry

instance 
  [IsUnivType typ ⟨.ofList es⟩ t T]
  : IsUnivType typ ⟨.ofList (e :: es)⟩ t T := sorry

instance
  [IsUnivType typ ⟨.ofList (e :: es)⟩ t T]
  : IsUnivType typ ⟨.ofList (e :: e' :: es)⟩ t T := sorry

instance 
  [IsUnivType f univ t F]
  : DecodableGen f [] [] univ t F := sorry

instance
  {t : Type 1}
  {F : Type -> t}
  [DecodableGen f codes [] univ (Type -> t) F]
  [DecodableGen typ [] [] univ Type α]
  : DecodableGen f (.mk typ 0 [] :: codes) [] univ t (F α) := sorry

instance
  [DecodableGen f (code :: codes) acc univ Type α]
  : DecodableGen f codes (code :: acc) univ Type α := sorry

instance 
  [DecodableGen f [] codes univ Type α] 
  : Decodable (.mk f n codes h) univ α := sorry

def Univ.CodedTerm.repr {univ : Univ} (t : univ.CodedTerm) : match t with | ⟨code, _, _⟩ => [Decodable code univ α] -> [Repr α] -> Std.Format := match t with
| ⟨code, satisfies, term⟩ => @_root_.repr α _ (Decodable.wf (code := t.code) (univ := univ) (type := α) ▸ t.term)


