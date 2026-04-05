
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
    fun f xβ xfα => foldMap (m := β -> β) f xfα xβ
export Foldable (foldMap)


instance : Foldable List where
  foldr := List.foldr

instance : Foldable Array where
  foldr := Array.foldr

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
