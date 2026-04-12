import Mystdlib.General
import Mystdlib.Foldable

open Foldable

class Uniplate (α : Type u) where
  uniplate : α -> Array α × (Array α -> α)

export Uniplate (uniplate)

namespace Uniplate

variable
  {α : Type}
  [Uniplate α]

def children : α -> Array α :=
  Prod.fst ∘ uniplate

def context : α -> (Array α -> α) :=
  Prod.snd ∘ uniplate

partial def univ (a : α) : Array α :=
  #[a] ++ (flatMap univ (children a))

partial def transform (f : α -> α) (x : α) : α :=
  let (children, context) := uniplate x
  f <| context <| Array.map (transform f) children

def descend (f : α -> α) (x : α) : α :=
  let (children, context) := uniplate x
  context <| Array.map f children

end Uniplate

abbrev BiplateType (β α : Type u) := β -> Array α × (Array α -> β)

class Biplate (β α : Type u) [Uniplate α] where
  biplate : β -> Array α × (Array α -> β)
export Biplate (biplate)

namespace Biplate

def universeOn [Uniplate α] (f : BiplateType β α) (x : β) : Array α :=
  flatMap Uniplate.univ <| Prod.fst (f x)

def transformOn [Uniplate α] (f : BiplateType β α) (g : α -> α) (x : β) : β :=
  let (children, ctx) := f x
  ctx <| Array.map (Uniplate.transform g) children

def univ [Uniplate α] [Biplate β α] : β -> Array α :=
  universeOn biplate

def transform [Uniplate α] [Biplate β α] : (α -> α) -> β -> β :=
  transformOn biplate



