import Mystdlib.Optics.Tambara.Optics
import Mystdlib.Optics.Tambara.Combinators
import Mystdlib.Optics.Tambara.Traversal

namespace Tamb

class Each (α β ς τ : Type u) where
  each : Traversal α β ς τ

class Each' (α : outParam (Type u)) (ς : Type u) where
  each : Traversal α α ς ς

instance : Each' α α where
  each := TraversalVL.toTraversal fun _ _ f x => f x

instance [inst : Each' α ξ] : Each' α (α × ξ) where
  each := TraversalVL.toTraversal fun _ _ f x =>
    (fun a xξ => (a, xξ)) <$> f x.fst <*> Each'.each.traverseOf f x.snd

instance : Each' α (List α) where
  each := traversed

instance : Each' α (Array α) where
  each := traversed


