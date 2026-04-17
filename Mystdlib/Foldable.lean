
namespace Foldable

instance : Append (α -> α) where
  append := Function.comp

class Monoid α extends Append α where
  mconcat : List α -> α := List.foldr Append.append mempty
  mempty : α := mconcat []
export Monoid (mconcat)
export Monoid (mempty)

instance : Monoid (List α) where
  mconcat := List.flatten

instance : Monoid (Array α) where
  mconcat := (·.foldl (· ++ ·) #[])

instance : Monoid (α -> α) where
  mempty := id
  
class Foldable (t : Type -> Type) where
  foldMap [Monoid m] : (α -> m) -> t α -> m :=
    fun f xtα => foldr (Append.append ∘ f) mempty xtα
  foldr : (α -> β -> β) -> β -> t α -> β :=
    fun f init xs => foldl (β := β -> β) (fun k x z => k (f x z)) id xs init
  foldl : (β -> α -> β) -> β -> t α -> β :=
    fun f init xs => foldr (β := β -> β) (fun x k z => k (f z x)) id xs init
export Foldable (foldMap)

instance : Foldable List where
  foldr := List.foldr
  foldl := List.foldl

instance : Foldable Array where
  foldr := Array.foldr
  foldl := Array.foldl


def flatMap [Foldable t] (f : α -> Array β) (as : t α) : Array β :=
  Foldable.foldl (fun bs a => bs ++ f a) ∅ as

def toList [Foldable t] (as : t α) : List α := Foldable.foldr .cons ∅ as

def toArray [Foldable t] (as : t α) : Array α := Foldable.foldl (fun as a => as.push a) ∅ as


class Filterable F extends Functor F where
  filterMap : (α -> Option β) -> F α -> F β :=
    fun f => reduceOption ∘ (map f)
  reduceOption : F (Option α) -> F α :=
    filterMap id
export Filterable (filterMap)
export Filterable (reduceOption)

instance : Filterable List where
  filterMap := List.filterMap
  reduceOption := List.reduceOption

instance : Filterable Array where
  filterMap := Array.filterMap
  reduceOption := Array.reduceOption


